-- | Bidirectional type checking for SmartTS (annotated locals, parameters, returns).
-- Designed to grow: judgments live here; surface 'Type' stays in "AST" until we add variables/schemes.
module SmartTS.TypeCheck
  ( typeCheckContract
  ) where

import Control.Monad(foldM, unless, when, zipWithM)
import Control.Monad.State
import Data.List (intercalate, nub)
import qualified Data.Map.Strict as M
import SmartTS.IR.AST

data Signature = Signature
  { formalArgs :: [Type]
  , returnType :: Type
  } deriving (Eq, Show)

data BindingKind = Param | LocalMutable | LocalImmutable
  deriving (Eq, Show)

data TcBinding = TcBinding
  { bindingKind :: BindingKind
  , bindingType :: Type
  }
  deriving (Eq, Show)

data TcEnv = TcEnv
  { envStorageType :: Type
  , envBindings :: M.Map Name TcBinding
  , envFunctionSignatures :: M.Map Name Signature
  , envReturnType :: Type
  }
  deriving (Eq, Show)

type TcM = StateT TcEnv (Either String)

tcError :: String -> TcM a
tcError = lift . Left

-- | Run an action in a child scope: state changes (new locals) do not escape.
withSavedEnv :: TcM a -> TcM a
withSavedEnv action = do
  saved <- get
  r <- action
  put saved
  return r

-- | Type-check a parsed contract and return a typed contract on success.
typeCheckContract :: ParsedContract -> Either String TypedContract
typeCheckContract c = do
  checkDuplicateStorage (contractStorage c)
  mapM_ (\(n, t) -> expectWellFormed ("Storage field `" ++ n ++ "`") t) (contractStorage c)
  mapM_ (checkDuplicateParams . methodArgs) (contractMethods c)
  mapM_ checkSignatureWellFormed (contractMethods c)
  typedMethods <- mapM (checkMethod c) (contractMethods c)
  return $ Contract
    { contractName    = contractName c
    , contractStorage = contractStorage c
    , contractMethods = typedMethods
    }

checkDuplicateStorage :: Storage -> Either String ()
checkDuplicateStorage fields =
  let names = map fst fields
   in if length names == length (nub names)
        then Right ()
        else Left "Duplicate field name in contract storage."

checkDuplicateParams :: [FormalParameter] -> Either String ()
checkDuplicateParams params =
  let names = map (\(FormalParameter n _) -> n) params
   in if length names == length (nub names)
        then Right ()
        else Left "Duplicate parameter name in method."

-- | Parameter and return types of a method must be well formed.
checkSignatureWellFormed :: MethodDecl a -> Either String ()
checkSignatureWellFormed m = do
  mapM_
    (\(FormalParameter n t) -> expectWellFormed ("Parameter `" ++ n ++ "`") t)
    (methodArgs m)
  expectWellFormed ("Return type of method `" ++ methodName m ++ "`") (methodReturnType m)

buildSigMap :: Contract a -> M.Map Name Signature
buildSigMap c =
  M.fromList
    [ (methodName m, Signature
        { formalArgs = [t | FormalParameter _ t <- methodArgs m]
        , returnType = methodReturnType m
        })
    | m <- contractMethods c
    , methodKind m == Private
    ]

checkMethod :: Contract a -> MethodDecl () -> Either String (MethodDecl Type)
checkMethod c m =
  let storageT = TRecord (contractStorage c)
      paramMap =
        M.fromList
          [ (n, TcBinding Param t)
          | FormalParameter n t <- methodArgs m
          ]
      env0 =
        TcEnv
          { envStorageType = storageT
          , envBindings = paramMap
          , envFunctionSignatures = buildSigMap c
          , envReturnType = methodReturnType m
          }
   in case runStateT (checkStmt (methodBody m)) env0 of
        Left err -> Left err
        Right (typedBody, _) -> Right $ MethodDecl
          { methodKind       = methodKind m
          , methodName       = methodName m
          , methodArgs       = methodArgs m
          , methodReturnType = methodReturnType m
          , methodBody       = typedBody
          }

-- | Check a statement and return the type-annotated version.
checkStmt :: Stmt () -> TcM (Stmt Type)
checkStmt (SequenceStmt ss) = SequenceStmt <$> mapM checkStmt ss
checkStmt (ReturnStmt e) = do
  expected <- gets envReturnType
  te <- checkExpr "return value" e expected
  return (ReturnStmt te)
checkStmt (VarDeclStmt n typ e) = do
  noDuplicateLocal n
  lift $ expectWellFormed ("Local `" ++ n ++ "`") typ
  te <- checkExpr ("initializer of var `" ++ n ++ "`") e typ
  modify $ insertLocal n LocalMutable typ
  return (VarDeclStmt n typ te)
checkStmt (ValDeclStmt n typ e) = do
  noDuplicateLocal n
  lift $ expectWellFormed ("Local `" ++ n ++ "`") typ
  te <- checkExpr ("initializer of val `" ++ n ++ "`") e typ
  modify $ insertLocal n LocalImmutable typ
  return (ValDeclStmt n typ te)
checkStmt (AssignmentStmt lv e) = do
  checkAssignable lv
  tl <- typeOfLValue lv
  te <- checkExpr "assignment" e tl
  return (AssignmentStmt lv te)
checkStmt (IfStmt cond thn mel) = do
  tc <- inferExpr cond
  lift $ expectType "if condition" (exprAnn tc) TBool
  tthn <- withSavedEnv (checkStmt thn)
  tmel <- case mel of
    Nothing  -> return Nothing
    Just els -> Just <$> withSavedEnv (checkStmt els)
  return (IfStmt tc tthn tmel)
checkStmt (WhileStmt cond body) = do
  tc <- inferExpr cond
  lift $ expectType "while condition" (exprAnn tc) TBool
  tbody <- withSavedEnv (checkStmt body)
  return (WhileStmt tc tbody)
checkStmt (MatchStmt scrutinee cases) = do
  tscrutinee <- inferExpr scrutinee
  alts <- case exprAnn tscrutinee of
    TVariant alts -> return alts
    t -> tcError $ "match scrutinee must be a variant, but it has type " ++ prettyType t ++ "."
  when (null cases) $ tcError "match has no cases."
  (tcases, covered, hasWildcard) <- checkMatchCases alts cases
  let missing = [tag | (tag, _) <- alts, tag `notElem` covered]
  when (not hasWildcard && not (null missing)) $
    tcError $
      "match is not exhaustive: missing "
        ++ intercalate ", " [ "`" ++ tag ++ "`" | tag <- missing ]
        ++ "; add those cases or a `_` case."
  return (MatchStmt tscrutinee tcases)

-- | Check the cases of a match from top to bottom. Besides the typed cases, it
-- returns the tags covered and whether a wildcard was seen, which the caller needs
-- to decide exhaustiveness. Each case runs in its own scope: the name it binds,
-- and any local declared in its body, disappear when the case ends.
checkMatchCases
  :: [(Name, Type)] -> [MatchCase ()] -> TcM ([MatchCase Type], [Name], Bool)
checkMatchCases alts cases = do
  (reversed, covered, wildcardSeen) <- foldM step ([], [], False) cases
  return (reverse reversed, covered, wildcardSeen)
  where
    step (done, covered, wildcardSeen) (MatchCase pat body) = do
      tbody <- case pat of
        PWildcard -> do
          when wildcardSeen $ afterWildcard "_"
          withSavedEnv (checkStmt body)
        PTag tag binder -> do
          payloadType <- case lookup tag alts of
            Nothing ->
              tcError $
                "Tag `" ++ tag ++ "` is not part of " ++ prettyType (TVariant alts) ++ "."
            Just p -> return p
          when wildcardSeen $ afterWildcard tag
          when (tag `elem` covered) $
            tcError $ "Tag `" ++ tag ++ "` is handled more than once in this match."
          withSavedEnv $ do
            case binder of
              Nothing -> return ()
              Just x -> do
                -- A payload of type unit carries nothing, so binding it is almost surely a mistake.
                when (typesEqual payloadType TUnit) $
                  tcError $ "Tag `" ++ tag ++ "` has no payload, so it cannot bind a name (`" ++ x ++ "`)."
                noDuplicateLocal x
                modify (insertLocal x LocalImmutable payloadType)
            checkStmt body
      let covered' = case pat of
            PTag tag _ -> tag : covered
            PWildcard -> covered
      return (MatchCase pat tbody : done, covered', wildcardSeen || pat == PWildcard)
    afterWildcard what =
      tcError $ "Case `" ++ what ++ "` comes after `_` and can never run."

noDuplicateLocal :: Name -> TcM ()
noDuplicateLocal n = do
  env <- get
  case M.lookup n (envBindings env) of
    Just (TcBinding LocalMutable _) ->
      tcError $ "Duplicate local `" ++ n ++ "` in the same block."
    Just (TcBinding LocalImmutable _) ->
      tcError $ "Duplicate local `" ++ n ++ "` in the same block."
    _ -> return ()

insertLocal :: Name -> BindingKind -> Type -> TcEnv -> TcEnv
insertLocal n k t env =
  env {envBindings = M.insert n (TcBinding k t) (envBindings env)}

checkAssignable :: LValue -> TcM ()
checkAssignable lv = do
  env <- get
  case rootOf lv of
    LStorage -> return ()
    LVar n ->
      case M.lookup n (envBindings env) of
        Nothing -> tcError $ "Unknown assignment target: `" ++ n ++ "`."
        Just (TcBinding Param _) ->
          tcError $ "Cannot assign to method parameter `" ++ n ++ "` (or through it for field updates)."
        Just (TcBinding LocalImmutable _) ->
          tcError $ "Cannot assign to immutable val `" ++ n ++ "` (or through it for field updates)."
        Just (TcBinding LocalMutable _) -> return ()
    LField {} -> return ()

rootOf :: LValue -> LValue
rootOf LStorage    = LStorage
rootOf (LVar n)    = LVar n
rootOf (LField p _) = rootOf p

typeOfLValue :: LValue -> TcM Type
typeOfLValue LStorage = gets envStorageType
typeOfLValue (LVar n) = do
  env <- get
  case M.lookup n (envBindings env) of
    Nothing -> tcError $ "Unknown variable `" ++ n ++ "`."
    Just b  -> return (bindingType b)
typeOfLValue (LField root fld) = do
  tRoot <- typeOfLValue root
  case tRoot of
    TRecord fields ->
      case lookup fld fields of
        Nothing -> tcError $ "Record has no field `" ++ fld ++ "`."
        Just t  -> return t
    _ -> tcError "Field access requires a record value (or typed storage)."

-- | Check mode: verify that an expression has the expected type, and return it
-- annotated. @ctx@ says where the expression appears (it starts the error message).
--
-- Forms that inference alone cannot type have their own cases, which read the
-- expected type: @#Tag(e)@ takes its type from the annotation, and @[]@ and list
-- literals take their element type from it. Record literals and comprehensions pass
-- the expected type down to their fields and body, so a @#Tag@ or @[]@ inside them
-- finds its type. Every other expression is handled the same way: infer its type,
-- then compare.
checkExpr :: String -> Expr () -> Type -> TcM (Expr Type)
checkExpr ctx (VariantCons () tag payload) expected =
  case expected of
    TVariant alts ->
      case lookup tag alts of
        Nothing ->
          tcError $
            ctx ++ " uses tag `" ++ tag ++ "`, which is not part of " ++ prettyType expected ++ "."
        Just payloadType -> do
          tpayload <- checkExpr ("payload of `#" ++ tag ++ "`") payload payloadType
          return (VariantCons expected tag tpayload)
    _ ->
      tcError $
        ctx ++ " has wrong type: expected " ++ prettyType expected
          ++ ", but `#" ++ tag ++ "` builds a variant."
checkExpr ctx (Record () fields) expected@(TRecord expectedFields)
  | names == map fst expectedFields = do
      tfields <-
        zipWithM
          (\(k, e) (_, ft) -> (,) k <$> checkExpr ("field `" ++ k ++ "` of " ++ ctx) e ft)
          fields
          expectedFields
      return (Record expected tfields)
  | otherwise =
      tcError $
        ctx ++ " has wrong type: expected " ++ prettyType expected
          ++ ", but the record literal has fields {" ++ intercalate ", " names ++ "}."
  where
    names = map fst fields
checkExpr ctx (ListLit () elements) expected@(TList elementType) = do
  telements <-
    zipWithM
      (\i e -> checkExpr ("element " ++ show i ++ " of " ++ ctx) e elementType)
      [1 :: Int ..]
      elements
  return (ListLit expected telements)
checkExpr ctx (ListComp () body clauses) expected@(TList elementType) =
  withSavedEnv $ do
    tclauses <- mapM checkClause clauses
    tbody <- checkExpr ("element of " ++ ctx) body elementType
    return (ListComp expected tbody tclauses)
checkExpr ctx (ListLit () []) expected =
  tcError $
    ctx ++ " has wrong type: expected " ++ prettyType expected ++ ", but `[]` builds a list."
checkExpr ctx e expected = do
  te <- inferExpr e
  lift $ expectType ctx (exprAnn te) expected
  return te

-- | Infer the type of a parsed expression and return the type-annotated version.
inferExpr :: Expr () -> TcM (Expr Type)
inferExpr (CInt () n)  = return (CInt TInt n)
inferExpr (CBool () b) = return (CBool TBool b)
inferExpr (Unit ())    = return (Unit TUnit)
inferExpr (StorageExpr ()) = do
  st <- gets envStorageType
  return (StorageExpr st)
inferExpr (Var () n) = do
  env <- get
  case M.lookup n (envBindings env) of
    Nothing -> tcError $ "Unknown variable `" ++ n ++ "`."
    Just b  -> return (Var (bindingType b) n)
inferExpr (FieldAccess () e fld) = do
  te <- inferExpr e
  case exprAnn te of
    TRecord fields ->
      case lookup fld fields of
        Nothing -> tcError $ "Record has no field `" ++ fld ++ "`."
        Just ft -> return (FieldAccess ft te fld)
    _ -> tcError "Field access requires a record-typed expression."
inferExpr (Not () e) = do
  te <- inferExpr e
  lift $ expectType "operand of !" (exprAnn te) TBool
  return (Not TBool te)
inferExpr (And () a b)  = inferBoolBin (And TBool) a b
inferExpr (Or () a b)   = inferBoolBin (Or TBool) a b
inferExpr (Add () a b)  = inferIntBin  (Add TInt) a b
inferExpr (Sub () a b)  = inferIntBin  (Sub TInt) a b
inferExpr (Mul () a b)  = inferIntBin  (Mul TInt) a b
inferExpr (Div () a b)  = inferIntBin  (Div TInt) a b
inferExpr (Mod () a b)  = inferIntBin  (Mod TInt) a b
inferExpr (Eq () a b)   = inferEq      (Eq TBool)  a b
inferExpr (Neq () a b)  = inferEq      (Neq TBool) a b
inferExpr (Lt () a b)   = inferIntCmp  (Lt TBool)  a b
inferExpr (Lte () a b)  = inferIntCmp  (Lte TBool) a b
inferExpr (Gt () a b)   = inferIntCmp  (Gt TBool)  a b
inferExpr (Gte () a b)  = inferIntCmp  (Gte TBool) a b
inferExpr (Record () pairs) = do
  tpairs <- mapM (\(k, e) -> (,) k <$> inferExpr e) pairs
  let fields = [(k, exprAnn te) | (k, te) <- tpairs]
  return (Record (TRecord fields) tpairs)
inferExpr (Call () name args) = do
  env <- get
  case M.lookup name (envFunctionSignatures env) of
    Nothing -> tcError $ "Unknown function `" ++ name ++ "`."
    Just sig -> do
      let expected = formalArgs sig
      when (length args /= length expected) $
        tcError $
          "Function `" ++ name ++ "` expects " ++ show (length expected)
            ++ " argument(s) but got " ++ show (length args) ++ "."
      targs <- zipWithM (\arg ex -> checkExpr ("argument to `" ++ name ++ "`") arg ex) args expected
      return (Call (returnType sig) name targs)
inferExpr (VariantCons () tag _) =
  tcError $
    "Cannot infer the type of `#" ++ tag ++ "`; annotate it (for example, with the type of a `val`)."
inferExpr (ListLit () []) =
  tcError "Cannot infer the element type of `[]`; annotate it (for example, with the type of a `val`)."
inferExpr (ListLit () (first : rest)) = do
  tfirst <- inferExpr first
  -- The first element fixes the element type, and the others must agree with it.
  trest <-
    zipWithM
      (\i e -> checkExpr ("element " ++ show i ++ " of the list literal") e (exprAnn tfirst))
      [2 :: Int ..]
      rest
  return (ListLit (TList (exprAnn tfirst)) (tfirst : trest))
inferExpr (ListComp () body clauses) =
  -- The names bound by the generators live only until the end of the comprehension.
  withSavedEnv $ do
    tclauses <- mapM checkClause clauses
    tbody <- inferExpr body
    return (ListComp (TList (exprAnn tbody)) tbody tclauses)

-- | Check one clause of a comprehension. Clauses are checked from left to right, and
-- a generator extends the environment for every clause after it and for the body.
-- A guard only reads names, so it never changes the environment.
checkClause :: CompClause () -> TcM (CompClause Type)
checkClause (CompGen name source) = do
  tsource <- inferExpr source
  elementType <- case exprAnn tsource of
    TList t -> return t
    t ->
      tcError $
        "generator `for " ++ name ++ " in ...` needs a list, but the expression has type "
          ++ prettyType t ++ "."
  noDuplicateLocal name
  modify (insertLocal name LocalImmutable elementType)
  return (CompGen name tsource)
checkClause (CompGuard guard) =
  CompGuard <$> checkExpr "guard of the list comprehension" guard TBool

inferBoolBin :: (Expr Type -> Expr Type -> Expr Type) -> Expr () -> Expr () -> TcM (Expr Type)
inferBoolBin con a b = do
  ta <- inferExpr a
  tb <- inferExpr b
  lift $ expectType "left operand of boolean operator"  (exprAnn ta) TBool
  lift $ expectType "right operand of boolean operator" (exprAnn tb) TBool
  return (con ta tb)

inferIntBin :: (Expr Type -> Expr Type -> Expr Type) -> Expr () -> Expr () -> TcM (Expr Type)
inferIntBin con a b = do
  ta <- inferExpr a
  tb <- inferExpr b
  lift $ expectType "left operand of arithmetic operator"  (exprAnn ta) TInt
  lift $ expectType "right operand of arithmetic operator" (exprAnn tb) TInt
  return (con ta tb)

inferIntCmp :: (Expr Type -> Expr Type -> Expr Type) -> Expr () -> Expr () -> TcM (Expr Type)
inferIntCmp con a b = do
  ta <- inferExpr a
  tb <- inferExpr b
  lift $ expectType "left operand of comparison"  (exprAnn ta) TInt
  lift $ expectType "right operand of comparison" (exprAnn tb) TInt
  return (con ta tb)

inferEq :: (Expr Type -> Expr Type -> Expr Type) -> Expr () -> Expr () -> TcM (Expr Type)
inferEq con a b = do
  (ta, tb) <- case (needsExpected a, needsExpected b) of
    (True, True) ->
      tcError
        "Cannot infer the type of either side of this comparison; compare against something with a known type (for example, a typed variable)."
    -- Only a side that cannot be inferred is checked. The other side tells its type.
    (True, False) -> do
      tb <- inferExpr b
      ta <- checkExpr "left operand of equality" a (exprAnn tb)
      return (ta, tb)
    (False, True) -> do
      ta <- inferExpr a
      tb <- checkExpr "right operand of equality" b (exprAnn ta)
      return (ta, tb)
    (False, False) -> (,) <$> inferExpr a <*> inferExpr b
  unless (typesEqual (exprAnn ta) (exprAnn tb)) $
    tcError $
      "Equality requires operands of the same type (got "
        ++ prettyType (exprAnn ta)
        ++ " and "
        ++ prettyType (exprAnn tb)
        ++ ")."
  unless (comparable (exprAnn ta)) $
    tcError $
      "Cannot compare values of type " ++ prettyType (exprAnn ta)
        ++ ": it is or contains a list, and lists are not comparable."
  return (con ta tb)

-- | Expressions that inference cannot type, because they only make sense against a
-- known type: a constructor @#Tag(e)@, an empty list, or a record, list or
-- comprehension built from them. A non-empty list is inferred from its first element,
-- and a comprehension from its body.
needsExpected :: Expr () -> Bool
needsExpected (VariantCons () _ _) = True
needsExpected (Record () fields) = any (needsExpected . snd) fields
needsExpected (ListLit () []) = True
needsExpected (ListLit () (first : _)) = needsExpected first
needsExpected (ListComp () body _) = needsExpected body
needsExpected _ = False

expectType :: String -> Type -> Type -> Either String ()
expectType ctx got expected =
  if typesEqual got expected
    then Right ()
    else
      Left $
        ctx ++ " has wrong type: expected " ++ prettyType expected ++ ", inferred " ++ prettyType got ++ "."

typesEqual :: Type -> Type -> Bool
typesEqual TInt  TInt  = True
typesEqual TBool TBool = True
typesEqual TUnit TUnit = True
typesEqual (TRecord as) (TRecord bs) = namedTypesEqual as bs
typesEqual (TVariant as) (TVariant bs) = namedTypesEqual as bs
typesEqual (TList a) (TList b) = typesEqual a b
typesEqual _ _ = False

-- | Types whose values can be compared with @==@ and @!=@, following Michelson's
-- COMPARE: base types, and records and variants whose components are comparable.
-- A list is never comparable, so neither is a type that contains one.
comparable :: Type -> Bool
comparable TInt = True
comparable TBool = True
comparable TUnit = True
comparable (TRecord fields) = all (comparable . snd) fields
comparable (TVariant alts) = all (comparable . snd) alts
comparable (TList _) = False

-- | Records and variants are compared position by position: names and types
-- must match, so the order of fields (or tags) is part of the type.
namedTypesEqual :: [(Name, Type)] -> [(Name, Type)] -> Bool
namedTypesEqual as bs = length as == length bs && and (zipWith entryEq as bs)
  where
    entryEq (n1, t1) (n2, t2) = n1 == n2 && typesEqual t1 t2

prettyType :: Type -> String
prettyType TInt  = "int"
prettyType TBool = "bool"
prettyType TUnit = "unit"
prettyType (TRecord fs) =
  "{"
    ++ concat
      [ n ++ ": " ++ prettyType t ++ if i < lastI then ", " else ""
      | (i, (n, t)) <- zip [0 :: Int ..] fs
      , let lastI = length fs - 1
      ]
    ++ "}"
prettyType (TList t) = "list<" ++ prettyType t ++ ">"
prettyType (TVariant alts) =
  "variant { " ++ intercalate " | " (map alt alts) ++ " }"
  where
    -- An alternative without payload has payload type unit and is written as a bare tag.
    alt (tag, TUnit) = tag
    alt (tag, t) = tag ++ "(" ++ prettyType t ++ ")"

-- | A type is well formed when, at any depth, no record repeats a field name
-- and no variant repeats a tag. The error mentions only the offending type.
checkTypeWF :: Type -> Either String ()
checkTypeWF TInt = Right ()
checkTypeWF TBool = Right ()
checkTypeWF TUnit = Right ()
checkTypeWF t@(TRecord fields) = checkNamedEntries "field" t fields
checkTypeWF t@(TVariant alts) = checkNamedEntries "tag" t alts
checkTypeWF (TList el) = checkTypeWF el

checkNamedEntries :: String -> Type -> [(Name, Type)] -> Either String ()
checkNamedEntries what t entries =
  case duplicates (map fst entries) of
    d : _ -> Left $ "duplicate " ++ what ++ " `" ++ d ++ "` in " ++ prettyType t
    [] -> mapM_ (checkTypeWF . snd) entries

-- | Names that appear more than once, in order of their second appearance.
duplicates :: [Name] -> [Name]
duplicates ns = nub [n | (i, n) <- zip [0 :: Int ..] ns, n `elem` take i ns]

-- | 'checkTypeWF' with a description of where the type was written.
expectWellFormed :: String -> Type -> Either String ()
expectWellFormed ctx t =
  either (\err -> Left (ctx ++ " has an ill-formed type: " ++ err ++ ".")) Right (checkTypeWF t)
