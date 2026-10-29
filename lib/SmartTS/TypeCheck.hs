-- | Bidirectional type checking for SmartTS (annotated locals, parameters, returns).
-- Designed to grow: judgments live here; surface 'Type' stays in "AST" until we add variables/schemes.
module SmartTS.TypeCheck
  ( typeCheckContract
  ) where

import Control.Monad(when, zipWithM_)
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
  te <- inferExpr e
  expected <- gets envReturnType
  lift $ expectType "return value" (exprAnn te) expected
  return (ReturnStmt te)
checkStmt (VarDeclStmt n typ e) = do
  noDuplicateLocal n
  lift $ expectWellFormed ("Local `" ++ n ++ "`") typ
  te <- inferExpr e
  lift $ expectType ("initializer of var `" ++ n ++ "`") (exprAnn te) typ
  modify $ insertLocal n LocalMutable typ
  return (VarDeclStmt n typ te)
checkStmt (ValDeclStmt n typ e) = do
  noDuplicateLocal n
  lift $ expectWellFormed ("Local `" ++ n ++ "`") typ
  te <- inferExpr e
  lift $ expectType ("initializer of val `" ++ n ++ "`") (exprAnn te) typ
  modify $ insertLocal n LocalImmutable typ
  return (ValDeclStmt n typ te)
checkStmt (AssignmentStmt lv e) = do
  checkAssignable lv
  tl <- typeOfLValue lv
  te <- inferExpr e
  lift $ expectType "assignment" (exprAnn te) tl
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
      targs <- mapM inferExpr args
      zipWithM_
        (\ta ex -> lift $ expectType ("argument to `" ++ name ++ "`") (exprAnn ta) ex)
        targs
        expected
      return (Call (returnType sig) name targs)
inferExpr (ListLit () _) = tcError "lists not supported by the type checker yet"
inferExpr (ListComp () _ _ ) = tcError "lists not supported by the type checker yet" 

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
  ta <- inferExpr a
  tb <- inferExpr b
  if typesEqual (exprAnn ta) (exprAnn tb)
    then return (con ta tb)
    else
      tcError $
        "Equality requires operands of the same type (got "
          ++ prettyType (exprAnn ta)
          ++ " and "
          ++ prettyType (exprAnn tb)
          ++ ")."

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
