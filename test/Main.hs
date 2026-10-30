{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import Test.Tasty
import Test.Tasty.HUnit
import SmartTS.IR.AST
import SmartTS.Parser
import Data.Aeson (object, (.=))
import Data.List (isInfixOf)
import SmartTS.Interpreter (ContractInstance (..), contractInstanceFromStorageValue)
import SmartTS.TypeCheck (typeCheckContract)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "SmartTS"
    [ testGroup
        "Parser Tests"
        [ contractTests
        , storageTests
        , methodTests
        , expressionTests
        , statementTests
        , errorTests
        , listTests
        ]
    , typeCheckTests
    , expectedTypeTests
    , variantTypeTests
    , variantConsTests
    , matchTests
    , equalityTests
    , listLiteralTests
    , comprehensionTests
    , typedAstTests
    ]

-- Helper function to parse and assert success
parseSuccess :: String -> (ParsedContract -> Assertion) -> Assertion
parseSuccess input assertion = case parseContractFromString input of
  Left err      -> assertFailure $ "Parse failed: " ++ show err
  Right contract -> assertion contract

-- Helper function to parse and assert failure
parseFailure :: String -> Assertion
parseFailure input = case parseContractFromString input of
  Left _  -> return ()  -- Expected failure
  Right _ -> assertFailure "Expected parse failure but got success"

typeCheckSuccess :: String -> Assertion
typeCheckSuccess input = case parseContractFromString input of
  Left err -> assertFailure $ "Parse failed: " ++ show err
  Right c ->
    case typeCheckContract c of
      Left err -> assertFailure $ "Type check failed: " ++ err
      Right _  -> return ()

typeCheckFailure :: String -> Assertion
typeCheckFailure input = case parseContractFromString input of
  Left err -> assertFailure $ "Parse failed (need valid parse for type test): " ++ show err
  Right c ->
    case typeCheckContract c of
      Left _  -> return ()
      Right _ -> assertFailure "Expected type error but checking succeeded"

-- Like 'typeCheckFailure', but the error message must also contain @expected@,
-- so a test cannot pass because of an unrelated error.
typeCheckFailureWith :: String -> String -> Assertion
typeCheckFailureWith expected input = case parseContractFromString input of
  Left err -> assertFailure $ "Parse failed (need valid parse for type test): " ++ show err
  Right c ->
    case typeCheckContract c of
      Left err
        | expected `isInfixOf` err -> return ()
        | otherwise ->
            assertFailure $
              "Type error message does not contain " ++ show expected ++ ".\nActual message: " ++ err
      Right _ -> assertFailure "Expected type error but checking succeeded"

contractTests :: TestTree
contractTests = testGroup "Contract Parsing"
  [ testCase "Simple contract with storage and method" $
      parseSuccess "contract MyContract { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract "MyContract" [( "x", TInt)] [MethodDecl Originate "init" [] TInt (SequenceStmt [ReturnStmt (CInt _ 0)])] ->
            return ()
          _ -> assertFailure $ "Unexpected contract structure: " ++ show contract

  , testCase "Contract with multiple storage fields" $
      parseSuccess "contract Test { storage: { x: int, y: int }; @entrypoint test(): int { return 1; } }" $ \contract ->
        case contract of
          Contract "Test" storage _ ->
            assertEqual "Storage should have 2 fields" 2 (length storage)
          _ -> assertFailure "Unexpected contract name"

  , testCase "Contract with multiple methods" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } @entrypoint inc(): int { return 1; } }" $ \contract ->
        case contract of
          Contract _ _ methods ->
            assertEqual "Should have 2 methods" 2 (length methods)
  ]

storageTests :: TestTree
storageTests = testGroup "Storage Parsing"
  [ testCase "Single storage field" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ [(name, typ)] _ -> do
            assertEqual "Storage field name" "x" name
            assertEqual "Storage field type" TInt typ
          _ -> assertFailure "Unexpected storage structure"

  , testCase "Multiple storage fields" $
      parseSuccess "contract Test { storage: { x: int, y: int, z: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ storage _ ->
            assertEqual "Should have 3 storage fields" 3 (length storage)

  , testCase "Storage with single field (no comma)" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ storage _ ->
            assertEqual "Should have 1 storage field" 1 (length storage)
  ]

methodTests :: TestTree
methodTests = testGroup "Method Parsing"
  [ testCase "Method with @originate decorator" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl Originate "init" [] TInt _] ->
            return ()
          _ -> assertFailure "Expected @originate method"

  , testCase "Method with @entrypoint decorator" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl EntryPoint "test" [] TInt _] ->
            return ()
          _ -> assertFailure "Expected @entrypoint method"

  , testCase "Method with @private decorator" $
      parseSuccess "contract Test { storage: { x: int }; @private helper(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl Private "helper" [] TInt _] ->
            return ()
          _ -> assertFailure "Expected @private method"

  , testCase "Method with parameters" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint add(a: int, b: int): int { return a + b; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl EntryPoint "add" params TInt _] -> do
            assertEqual "Should have 2 parameters" 2 (length params)
            case params of
              [FormalParameter "a" TInt, FormalParameter "b" TInt] ->
                return ()
              _ -> assertFailure "Unexpected parameter structure"
          _ -> assertFailure "Unexpected method structure"

  , testCase "Method with single parameter" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint inc(x: int): int { return x + 1; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ params _ _] ->
            assertEqual "Should have 1 parameter" 1 (length params)
          _ -> assertFailure "Unexpected method structure"

  , testCase "Method with empty parameter list" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ params _ _] ->
            assertEqual "Should have 0 parameters" 0 (length params)
          _ -> assertFailure "Unexpected method structure"
  ]

expressionTests :: TestTree
expressionTests = testGroup "Expression Parsing"
  [ testCase "Integer literal" $
      parseSuccess "contract Test { storage: { x: int }; @originate init(): int { return 42; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (CInt _ 42)])] ->
            return ()
          _ -> assertFailure $ "Expected integer literal 42, got: " ++ show contract

  , testCase "Variable reference" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Var _ "x")])] ->
            return ()
          _ -> assertFailure $ "Expected variable reference, got: " ++ show contract

  , testCase "Addition expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 1 + 2; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Add _ (CInt _ 1) (CInt _ 2))])] ->
            return ()
          _ -> assertFailure $ "Expected addition expression, got: " ++ show contract

  , testCase "Subtraction expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 5 - 3; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Sub _ (CInt _ 5) (CInt _ 3))])] ->
            return ()
          _ -> assertFailure $ "Expected subtraction expression, got: " ++ show contract

  , testCase "Chained addition" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 1 + 2 + 3; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt expr])] -> do
            -- Should parse as (1 + 2) + 3 due to left associativity
            case expr of
              Add _ (Add _ (CInt _ 1) (CInt _ 2)) (CInt _ 3) ->
                return ()
              _ -> assertFailure $ "Expected left-associative addition, got: " ++ show expr
          _ -> assertFailure $ "Unexpected expression structure: " ++ show contract

  , testCase "Mixed addition and subtraction" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 10 - 2 + 3; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt expr])] -> do
            -- Should parse as (10 - 2) + 3 due to left associativity
            case expr of
              Add _ (Sub _ (CInt _ 10) (CInt _ 2)) (CInt _ 3) ->
                return ()
              _ -> assertFailure $ "Expected left-associative mixed operations, got: " ++ show expr
          _ -> assertFailure $ "Unexpected expression structure: " ++ show contract

  , testCase "Parenthesized expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return (1 + 2); } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Add _ (CInt _ 1) (CInt _ 2))])] ->
            return ()
          _ -> assertFailure $ "Expected parenthesized addition, got: " ++ show contract

  , testCase "Unit expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return (); } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (Unit _)])] ->
            return ()
          _ -> assertFailure $ "Expected unit expression, got: " ++ show contract

  , testCase "Boolean expression (&&) and boolean type" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint check(): bool { return true && false; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "check" [] TBool (SequenceStmt [ReturnStmt (And _ (CBool _ True) (CBool _ False))])] ->
            return ()
          _ -> assertFailure $ "Expected boolean && expression, got: " ++ show contract

  , testCase "Not expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint notit(): bool { return !false; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "notit" [] TBool (SequenceStmt [ReturnStmt (Not _ (CBool _ False))])] ->
            return ()
          _ -> assertFailure $ "Expected !false, got: " ++ show contract

  , testCase "Relational expression (==)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint eq(): bool { return 1 == 2; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "eq" [] TBool (SequenceStmt [ReturnStmt (Eq _ (CInt _ 1) (CInt _ 2))])] ->
            return ()
          _ -> assertFailure $ "Expected 1 == 2, got: " ++ show contract

  , testCase "Mul/Div/Mod expressions" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint arith(): int { return 6 * 7; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "arith" [] TInt (SequenceStmt [ReturnStmt (Mul _ (CInt _ 6) (CInt _ 7))])] ->
            return ()
          _ -> assertFailure $ "Expected 6 * 7, got: " ++ show contract

  , testCase "Record type and record literal" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint get(): { a: int, b: bool } { return { a: 1, b: true }; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "get" [] (TRecord [("a", TInt), ("b", TBool)]) (SequenceStmt [ReturnStmt (Record _ [("a", CInt _ 1), ("b", CBool _ True)])])] ->
            return ()
          _ -> assertFailure $ "Expected record type/literal, got: " ++ show contract

  , testCase "Record field access (x.f)" $
      parseSuccess "contract Test { storage: { x: { a: int, b: bool } }; @entrypoint proj(): int { return x.a; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "proj" [] TInt
                (SequenceStmt [ReturnStmt (FieldAccess _ (Var _ "x") "a")])
            ] ->
              return ()
          _ -> assertFailure $ "Expected projection x.a, got: " ++ show contract

  , testCase "Chained field access (x.a.b)" $
      parseSuccess "contract Test { storage: { x: { a: { b: int } } }; @entrypoint proj2(): int { return x.a.b; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "proj2" [] TInt
                (SequenceStmt
                  [ReturnStmt (FieldAccess _ (FieldAccess _ (Var _ "x") "a") "b")])]
            -> return ()
          _ -> assertFailure $ "Expected chained projection x.a.b, got: " ++ show contract

  , testCase "Chained field access on record literal (..a.b)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint litproj2(): int { return { a: { b: 1 } }.a.b; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "litproj2" [] TInt
                (SequenceStmt
                  [ReturnStmt
                    (FieldAccess _
                      (FieldAccess _
                        (Record _ [("a", Record _ [("b", CInt _ 1)])])
                        "a")
                      "b")])]
            -> return ()
          _ -> assertFailure $ "Expected chained projection on record literal, got: " ++ show contract

  , testCase "Field access on record literal" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint litproj(): int { return { a: 1, b: true }.a; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "litproj" [] TInt
                (SequenceStmt [ReturnStmt (FieldAccess _ (Record _ [("a", CInt _ 1), ("b", CBool _ True)]) "a")])
            ] ->
              return ()
          _ -> assertFailure $ "Expected projection on record literal, got: " ++ show contract
  ]

statementTests :: TestTree
statementTests = testGroup "Statement Parsing"
  [ testCase "Return statement" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { return 42; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (CInt _ 42)])] ->
            return ()
          _ -> assertFailure $ "Expected return statement, got: " ++ show contract

  , testCase "Assignment statement" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { x = 10; return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [AssignmentStmt (LVar "x") (CInt _ 10), ReturnStmt (Var _ "x")])] ->
            return ()
          _ -> assertFailure "Expected assignment and return statements"

  , testCase "Multiple statements in block" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { x = 1; x = 2; return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt stmts)] ->
            assertEqual "Should have 3 statements" 3 (length stmts)
          _ -> assertFailure "Unexpected statement structure"

  , testCase "Assignment with expression" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint test(): int { x = 1 + 2; return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [AssignmentStmt (LVar "x") (Add _ (CInt _ 1) (CInt _ 2)), ReturnStmt (Var _ "x")])] ->
            return ()
          _ -> assertFailure "Expected assignment with expression"

  , testCase "If statement with else" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint f(): int { if (true) { return 1; } else { return 2; } } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "f" [] TInt (SequenceStmt [IfStmt (CBool _ True) (SequenceStmt [ReturnStmt (CInt _ 1)]) (Just (SequenceStmt [ReturnStmt (CInt _ 2)]))])] ->
            return ()
          _ -> assertFailure $ "Expected if/else, got: " ++ show contract

  , testCase "While statement" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint loop(): int { while (false) { x = 1; } return x; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ "loop" [] TInt (SequenceStmt [WhileStmt (CBool _ False) (SequenceStmt [AssignmentStmt (LVar "x") (CInt _ 1)]) , ReturnStmt (Var _ "x")])] ->
            return ()
          _ -> assertFailure $ "Expected while statement, got: " ++ show contract

  , testCase "Field assignment statement (x.a = ...)" $
      parseSuccess "contract Test { storage: { x: { a: int } }; @entrypoint fa(): int { x.a = 3; return x.a; } }" $ \contract ->
        case contract of
          Contract _ _
            [MethodDecl _ "fa" [] TInt
              (SequenceStmt
                [ AssignmentStmt (LField (LVar "x") "a") (CInt _ 3)
                , ReturnStmt (FieldAccess _ (Var _ "x") "a")
                ])] ->
              return ()
          _ -> assertFailure $ "Expected x.a assignment, got: " ++ show contract

  , testCase "Field assignment statement (x.a.b = ...)" $
      parseSuccess "contract Test { storage: { x: { a: { b: int } } }; @entrypoint fab(): int { x.a.b = 3; return x.a.b; } }" $ \contract ->
        case contract of
          Contract _ _
            [MethodDecl _ "fab" [] TInt
              (SequenceStmt
                [ AssignmentStmt
                    (LField (LField (LVar "x") "a") "b")
                    (CInt _ 3)
                , ReturnStmt
                    (FieldAccess _ (FieldAccess _ (Var _ "x") "a") "b")
                ])] ->
              return ()
          _ -> assertFailure $ "Expected x.a.b assignment, got: " ++ show contract

  , testCase "Storage expression read (storage.x)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint sr(): int { return storage.x; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "sr" [] TInt
                (SequenceStmt
                  [ReturnStmt (FieldAccess _ (StorageExpr _) "x")])
            ] ->
              return ()
          _ -> assertFailure $ "Expected storage read, got: " ++ show contract

  , testCase "Storage expression write (storage.x = ...)" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint sw(): int { storage.x = 10; return storage.x; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "sw" [] TInt
                (SequenceStmt
                  [ AssignmentStmt (LField LStorage "x") (CInt _ 10)
                  , ReturnStmt (FieldAccess _ (StorageExpr _) "x")
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected storage write, got: " ++ show contract

  , testCase "Var declaration + assignment to local var" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint v(): int { var y: int = 10; y = 11; return y; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "v" [] TInt
                (SequenceStmt
                  [ VarDeclStmt "y" TInt (CInt _ 10)
                  , AssignmentStmt (LVar "y") (CInt _ 11)
                  , ReturnStmt (Var _ "y")
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected var decl + assignment, got: " ++ show contract

  , testCase "Val declaration + returning local val" $
      parseSuccess "contract Test { storage: { x: int }; @entrypoint c(): int { val y: int = 10; return y; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "c" [] TInt
                (SequenceStmt
                  [ ValDeclStmt "y" TInt (CInt _ 10)
                  , ReturnStmt (Var _ "y")
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected val decl, got: " ++ show contract

  , testCase "Field assignment to local record (x.a = ... but local var)" $
      parseSuccess "contract Test { storage: { x: { a: int } }; @entrypoint fa2(): int { var t: { a: int } = x; t.a = 7; return t.a; } }" $ \contract ->
        case contract of
          Contract _ _
            [ MethodDecl _ "fa2" [] TInt
                (SequenceStmt
                  [ VarDeclStmt "t" (TRecord [("a", TInt)]) (Var _ "x")
                  , AssignmentStmt (LField (LVar "t") "a") (CInt _ 7)
                  , ReturnStmt (FieldAccess _ (Var _ "t") "a")
                  ])
            ] ->
              return ()
          _ -> assertFailure $ "Expected local record field assignment, got: " ++ show contract
  ]

typeCheckTests :: TestTree
typeCheckTests =
  testGroup
    "Type checker"
    [ testCase "Minimal well-typed contract" $
        typeCheckSuccess
          "contract C { storage: { x: int }; @originate init(): int { return 0; } }"
    , testCase "Return type mismatch" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): int { return true; } }"
    , testCase "Return type mismatch names the expected and inferred types" $
        typeCheckFailureWith "expected int, inferred bool"
          "contract C { storage: { x: int }; @originate init(): int { return true; } }"
    , testCase "Arithmetic requires int" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): int { return 1 + true; } }"
    , testCase "Cannot assign to val" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): int { val v: int = 1; v = 2; return 0; } }"
    , testCase "Equality requires same types" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): bool { return 1 == true; } }"
    , testCase "If condition must be bool" $
        typeCheckFailure
          "contract C { storage: { x: int }; @originate init(): int { if (1) { return 0; } else { return 1; } } }"
    , testCase "Storage field assignment matches storage type" $
        typeCheckSuccess
          "contract C { storage: { n: int }; @originate init(): unit { storage.n = 3; return (); } }"
    , testCase "Unknown storage field" $
        typeCheckFailure
          "contract C { storage: { n: int }; @originate init(): unit { storage.missing = 1; return (); } }"
    , testCase "Persisted storage decodes against contract storage type" $
        parseSuccess
          "contract C { storage: { n: int, b: bool }; @originate init(): unit { return (); } }"
          $ \c ->
            case contractInstanceFromStorageValue c (object ["n" .= (1 :: Int), "b" .= True]) of
              Left err -> assertFailure err
              Right (ContractInstance _ st) -> case st of
                Record _ [("n", CInt _ 1), ("b", CBool _ True)] -> return ()
                _ -> assertFailure $ "unexpected storage expr: " ++ show st
    ]

errorTests :: TestTree
errorTests = testGroup "Error Cases"
  [ testCase "Missing contract keyword" $
      parseFailure "MyContract { storage: { x: int }; @originate init(): int { return 0; } }"

  , testCase "Missing storage declaration" $
      parseFailure "contract Test { @originate init(): int { return 0; } }"

  , testCase "Invalid storage syntax" $
      parseFailure "contract Test { storage x: int; @originate init(): int { return 0; } }"

  , testCase "Missing method decorator (defaults to Private)" $
      parseSuccess "contract Test { storage: { x: int }; init(): int { return 0; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl Private "init" [] TInt _] ->
            return ()
          _ -> assertFailure "Expected method without decorator to default to Private"

  , testCase "Missing return type" $
      parseFailure "contract Test { storage: { x: int }; @entrypoint test() { return 0; } }"

  , testCase "Missing semicolon after statement" $
      parseFailure "contract Test { storage: { x: int }; @entrypoint test(): int { return 0 } }"

  , testCase "Invalid expression syntax" $
      parseFailure "contract Test { storage: { x: int }; @entrypoint test(): int { return +; } }"
  ]

listTests :: TestTree
listTests = testGroup "List Parsing"
  [ testCase "List type: list<int>" $
      parseSuccess "contract T { storage: { xs: list<int> }; @originate init(): unit { return (); } }" $ \contract ->
        case contract of
          Contract _ [("xs", TList TInt)] _ -> return ()
          _ -> assertFailure "Expected storage field xs of type TList TInt"

  , testCase "List type: list<list<int>>" $
      parseSuccess "contract T { storage: { xs: list<list<int>>}; @originate init(): unit {return (); } }" $ \contract ->
        case contract of
          Contract _ [("xs", TList( TList TInt))] _ -> return ()
          _ -> assertFailure "Expected storage field xs of type TList (TList TInt)"

  , testCase "List literal: empty" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { return []; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (ListLit _ [])])] -> return ()
          _ -> assertFailure "Expected empty ListLit"
  
  , testCase "List literal: one element" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { return [1]; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (ListLit _ [CInt _ 1])])] -> return ()
          _ -> assertFailure "Expected ListLit with one element"

  , testCase "List literal: three elements" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { return [1, 2, 3]; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (ListLit _ [(CInt _ 1), (CInt _ 2), (CInt _ 3)])])] -> return ()
          _ -> assertFailure "Expected ListLit with three elements"

  , testCase "List comprehension: single generator" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { return [x for x in xs]; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (ListComp _ (Var _ "x") [CompGen "x" (Var _ "xs")])])] -> return ()
          _ -> assertFailure "Expected ListComp with one generator"

  , testCase "List comprehension: two generators" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { return [x + y for x in xs for y in ys]; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (ListComp _ (Add _ (Var _ "x") (Var _ "y")) [CompGen "x" (Var _ "xs"), CompGen "y" (Var _ "ys")])])] -> return ()
          _ -> assertFailure "Expected ListComp with two generators"

  , testCase "List comprehension: generator and guard" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { return [x for x in xs if x > 0]; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (ListComp _ (Var _ "x") [CompGen "x" (Var _ "xs"), CompGuard (Gt _ (Var _ "x") (CInt _ 0))])])] -> return ()
          _ -> assertFailure "Expected ListComp with a generator and a guard"

  , testCase "List comprehension: generator, guard, generator" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { return [x for x in xs if x > 0 for y in ys]; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (ListComp _ (Var _ "x") [CompGen "x" (Var _ "xs"), CompGuard (Gt _ (Var _ "x") (CInt _ 0)), CompGen "y" (Var _ "ys")])])] -> return ()
          _ -> assertFailure "Expected clauses in written order: generator, guard, generator"

  , testCase "List literal: nested lists" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { return [[1, 2], [3]]; } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ReturnStmt (ListLit _ [ListLit _ [CInt _ 1, CInt _ 2], ListLit _ [CInt _ 3]])])] -> return ()
          _ -> assertFailure "Expected ListLit of two ListLits"

  , testCase "List comprehension: guard before generator is rejected" $
      parseFailure "contract T { storage: { x: int }; @entrypoint t(): unit { return [x if x > 0 for x in xs]; } }"

  , testCase "List comprehension: generator without `in` is rejected" $
      parseFailure "contract T { storage: { x: int }; @entrypoint t(): unit { return [x for x xs]; } }"

  , testCase "Reserved words: `for` is not a valid variable name" $
      parseFailure "contract T { storage: { x: int }; @entrypoint t(): unit { val for: int = 1; return (); } }"

  , testCase "Reserved words: `in` is not a valid variable name" $
      parseFailure "contract T { storage: { x: int }; @entrypoint t(): unit { val in: int = 1; return (); } }"

  , testCase "Reserved words: names that only start with `for` or `in` stay valid" $
      parseSuccess "contract T { storage: { x: int }; @entrypoint t(): unit { val index: int = 1; val format: int = 2; return (); } }" $ \contract ->
        case contract of
          Contract _ _ [MethodDecl _ _ _ _ (SequenceStmt [ValDeclStmt "index" _ _, ValDeclStmt "format" _ _, _])] -> return ()
          _ -> assertFailure "Expected two val declarations named index and format"
  ]

-- Contract whose storage holds a list, with an entrypoint f running @body@.
withListStorage :: String -> String
withListStorage body =
  "contract C { storage: { xs: list<int> }; @entrypoint f(): unit { " ++ body ++ " } }"

-- Note: `{ a: e }.a` is used below to reach the inference mode, where no annotation is given.
listLiteralTests :: TestTree
listLiteralTests = testGroup "Type checker: list literals"
  [ testGroup "Accepted"
      [ testCase "Literal annotated by val" $
          typeCheckSuccess $ withMethod "" "unit" "val xs: list<int> = [1, 2, 3]; return ();"
      , testCase "One element" $
          typeCheckSuccess $ withMethod "" "unit" "val xs: list<int> = [1]; return ();"
      , testCase "Empty list takes its type from the annotation" $
          typeCheckSuccess $ withMethod "" "unit" "val xs: list<int> = []; return ();"
      , testCase "Elements are arbitrary expressions" $
          typeCheckSuccess $ withMethod "x: int" "unit" "val xs: list<int> = [1 + 2, x, x * 2]; return ();"
      , testCase "Constructors in a list take the element type" $
          typeCheckSuccess $
            withMethod "" "unit" "val xs: list<variant { A | B }> = [#A, #B]; return ();"
      , testCase "Nested lists, including an empty inner list" $
          typeCheckSuccess $
            withMethod "" "unit" "val xs: list<list<int>> = [[1, 2], [3], []]; return ();"
      , testCase "List of records" $
          typeCheckSuccess $
            withMethod "" "unit" "val rs: list<{ a: int }> = [{ a: 1 }, { a: 2 }]; return ();"
      , testCase "Annotated by the return type" $
          typeCheckSuccess $ withMethod "" "list<int>" "return [1, 2];"
      , testCase "Empty list annotated by the return type" $
          typeCheckSuccess $ withMethod "" "list<int>" "return [];"
      , testCase "Assigned to a storage field" $
          typeCheckSuccess $ withListStorage "storage.xs = [1, 2]; storage.xs = []; return ();"
      , testCase "Inside a record literal assigned to storage" $
          typeCheckSuccess $ withListStorage "storage = { xs: [] }; return ();"
      , testCase "As a call argument" $
          typeCheckSuccess $
            "contract C { storage: { x: int }; @private g(xs: list<int>): int { return 0; } "
              ++ "@entrypoint f(): unit { val a: int = g([1, 2]); val b: int = g([]); return (); } }"
      , testCase "Inside a variant payload" $
          typeCheckSuccess $
            withMethod "" "unit" "val o: variant { L(list<int>) | N } = #L([1, 2]); return ();"
      , testCase "Inference: the type comes from the first element" $
          typeCheckSuccess $
            withMethod "" "unit" "val xs: list<int> = { a: [1, 2] }.a; return ();"
      , testCase "Inference: later elements are checked against the first" $
          typeCheckSuccess $
            withMethod "x: variant { A | B }" "unit"
              "val ys: list<variant { A | B }> = { a: [x, #A] }.a; return ();"
      ]
  , testGroup "Rejected"
      [ testCase "Mixed element types, annotated" $
          typeCheckFailureWith
            "element 2 of initializer of val `xs` has wrong type: expected int, inferred bool" $
            withMethod "" "unit" "val xs: list<int> = [1, true]; return ();"
      , testCase "Wrong element type, first position" $
          typeCheckFailureWith
            "element 1 of initializer of val `xs` has wrong type: expected bool, inferred int" $
            withMethod "" "unit" "val xs: list<bool> = [1]; return ();"
      , testCase "Mixed element types, inferred" $
          typeCheckFailureWith
            "element 2 of the list literal has wrong type: expected int, inferred bool" $
            withMethod "" "unit" "val xs: list<int> = { a: [1, true] }.a; return ();"
      , testCase "Error in a nested list names both positions" $
          typeCheckFailureWith
            "element 1 of element 2 of initializer of val `xs` has wrong type: expected int, inferred bool" $
            withMethod "" "unit" "val xs: list<list<int>> = [[1], [true]]; return ();"
      , testCase "Unknown tag inside a list" $
          typeCheckFailureWith
            "element 2 of initializer of val `xs` uses tag `C`, which is not part of variant { A | B }" $
            withMethod "" "unit" "val xs: list<variant { A | B }> = [#A, #C]; return ();"
      , testCase "Empty list without an annotation" $
          typeCheckFailureWith "Cannot infer the element type of `[]`; annotate it" $
            withMethod "" "unit" "val xs: list<int> = { a: [] }.a; return ();"
      , testCase "Constructors in a list without an annotation" $
          typeCheckFailureWith "Cannot infer the type of `#A`" $
            withMethod "" "unit" "val xs: list<variant { A | B }> = { a: [#A, #B] }.a; return ();"
      , testCase "Empty list where a non-list is expected" $
          typeCheckFailureWith
            "initializer of val `n` has wrong type: expected int, but `[]` builds a list" $
            withMethod "" "unit" "val n: int = []; return ();"
      , testCase "Non-empty list where a non-list is expected" $
          typeCheckFailureWith
            "initializer of val `n` has wrong type: expected int, inferred list<int>" $
            withMethod "" "unit" "val n: int = [1, 2]; return ();"
      , testCase "Empty list compared with a list: the type is found, the comparison is refused" $
          typeCheckFailureWith "Cannot compare values of type list<int>" $
            withMethod "xs: list<int>" "bool" "return [] == xs;"
      , testCase "Same on the right" $
          typeCheckFailureWith "Cannot compare values of type list<int>" $
            withMethod "xs: list<int>" "bool" "return xs == [];"
      ]
  ]

-- Type-check a contract and apply an assertion to the typed body of its first method.
typeCheckedBody :: String -> (TypedStmt -> Assertion) -> Assertion
typeCheckedBody input assertion = case parseContractFromString input of
  Left err -> assertFailure $ "Parse failed: " ++ show err
  Right c -> case typeCheckContract c of
    Left err -> assertFailure $ "Type check failed: " ++ err
    Right tc -> case contractMethods tc of
      m : _ -> assertion (methodBody m)
      [] -> assertFailure "The contract has no methods."

-- The other tests only ask whether a contract is accepted. These look at the annotated tree the
-- checker returns, which the interpreter and the code generator consume, and at the scope that is
-- restored after a construct that binds a name.
typedAstTests :: TestTree
typedAstTests = testGroup "Type checker: typed tree and scope"
  [ testGroup "Annotations"
      [ testCase "A constructor carries the whole expected variant type" $
          typeCheckedBody (withMethod "" "unit" "val o: variant { Some(int) | None } = #Some(1); return ();") $ \body ->
            case body of
              SequenceStmt [ValDeclStmt "o" _ (VariantCons t "Some" (CInt TInt 1)), _]
                | t == TVariant [("Some", TInt), ("None", TUnit)] -> return ()
              _ -> assertFailure $ "Unexpected typed body: " ++ show body
      , testCase "A constructor without payload carries unit in its payload" $
          typeCheckedBody (withMethod "" "unit" "val o: variant { Some(int) | None } = #None; return ();") $ \body ->
            case body of
              SequenceStmt [ValDeclStmt "o" _ (VariantCons _ "None" (Unit TUnit)), _] -> return ()
              _ -> assertFailure $ "Unexpected typed body: " ++ show body
      , testCase "An empty list carries the expected list type" $
          typeCheckedBody (withMethod "" "unit" "val xs: list<int> = []; return ();") $ \body ->
            case body of
              SequenceStmt [ValDeclStmt "xs" _ (ListLit (TList TInt) []), _] -> return ()
              _ -> assertFailure $ "Unexpected typed body: " ++ show body
      , testCase "A list literal carries list of the element type" $
          typeCheckedBody (withMethod "" "unit" "val xs: list<int> = [1, 2]; return ();") $ \body ->
            case body of
              SequenceStmt [ValDeclStmt "xs" _ (ListLit (TList TInt) [CInt TInt 1, CInt TInt 2]), _] -> return ()
              _ -> assertFailure $ "Unexpected typed body: " ++ show body
      , testCase "A comprehension carries the list type, and its parts are annotated" $
          typeCheckedBody (withMethod "xs: list<int>" "unit" "val bs: list<bool> = [x > 0 for x in xs]; return ();") $ \body ->
            case body of
              SequenceStmt
                [ ValDeclStmt "bs" _
                    (ListComp (TList TBool) (Gt TBool (Var TInt "x") (CInt TInt 0)) [CompGen "x" (Var (TList TInt) "xs")])
                , _ ] -> return ()
              _ -> assertFailure $ "Unexpected typed body: " ++ show body
      , testCase "A record literal carries the expected record type, with its constructors annotated" $
          typeCheckedBody (withMethod "" "unit" "val r: { s: variant { A | B } } = { s: #A }; return ();") $ \body ->
            let v = TVariant [("A", TUnit), ("B", TUnit)]
             in case body of
                  SequenceStmt [ValDeclStmt "r" _ (Record (TRecord [("s", tv)]) [("s", VariantCons tc "A" (Unit TUnit))]), _]
                    | tv == v && tc == v -> return ()
                  _ -> assertFailure $ "Unexpected typed body: " ++ show body
      , testCase "A match annotates the scrutinee and the name it binds" $
          typeCheckedBody (withMethod "r: variant { Ok(int) | Err }" "unit" "match (r) { Ok(v) => { storage.x = v; } Err => { return (); } } return ();") $ \body ->
            case body of
              SequenceStmt
                [ MatchStmt (Var (TVariant [("Ok", TInt), ("Err", TUnit)]) "r")
                    [ MatchCase (PTag "Ok" (Just "v")) (SequenceStmt [AssignmentStmt _ (Var TInt "v")])
                    , MatchCase (PTag "Err" Nothing) _ ]
                , _ ] -> return ()
              _ -> assertFailure $ "Unexpected typed body: " ++ show body
      ]
  , testGroup "Scope is restored"
      [ testCase "A parameter shadowed by a match binder is back after the match" $
          typeCheckSuccess $ withMethod "r: variant { Ok(int) | Err }, n: bool" "unit"
            "match (r) { Ok(n) => { storage.x = n; } Err => { return (); } } val b: bool = n; return ();"
      , testCase "...with its original type, not the binder's" $
          typeCheckFailureWith "initializer of val `c` has wrong type: expected int, inferred bool" $
            withMethod "r: variant { Ok(int) | Err }, n: bool" "unit"
              "match (r) { Ok(n) => { return (); } Err => { return (); } } val c: int = n; return ();"
      , testCase "A parameter shadowed by a generator is back after the comprehension" $
          typeCheckSuccess $ withMethod "n: bool, xs: list<int>" "unit"
            "val zs: list<int> = [n for n in xs]; val b: bool = n; return ();"
      , testCase "...with its original type, not the generator's" $
          typeCheckFailureWith "initializer of val `c` has wrong type: expected int, inferred bool" $
            withMethod "n: bool, xs: list<int>" "unit"
              "val zs: list<int> = [n for n in xs]; val c: int = n; return ();"
      , testCase "A name bound by a match can be bound again after it" $
          typeCheckSuccess $ withMethod "r: variant { Ok(int) | Err }" "unit"
            "match (r) { Ok(v) => { return (); } Err => { return (); } } val v: int = 1; return ();"
      ]
  , testGroup "Constructors where a bool or a payload is not allowed"
      [ testCase "A constructor as a comprehension guard" $
          typeCheckFailureWith "guard of the list comprehension has wrong type: expected bool, but `#A` builds a variant" $
            withMethod "xs: list<int>" "unit" "val zs: list<variant { A | B }> = [#A for x in xs if #A]; return ();"
      , testCase "A payload of explicit type unit cannot bind a name, like a missing payload" $
          typeCheckFailureWith "Tag `A` has no payload, so it cannot bind a name" $
            withMethod "r: variant { A(unit) | B }" "unit" "match (r) { A(v) => { return (); } _ => { return (); } } return ();"
      ]
  ]

comprehensionTests :: TestTree
comprehensionTests = testGroup "Type checker: list comprehensions"
  [ testGroup "Accepted"
      [ testCase "Map" $
          typeCheckSuccess $
            withMethod "xs: list<int>" "unit" "val zs: list<int> = [x + 1 for x in xs]; return ();"
      , testCase "Identity" $
          typeCheckSuccess $
            withMethod "xs: list<int>" "unit" "val zs: list<int> = [x for x in xs]; return ();"
      , testCase "Filter" $
          typeCheckSuccess $
            withMethod "xs: list<int>" "unit" "val zs: list<int> = [x for x in xs if x > 0]; return ();"
      , testCase "Two generators" $
          typeCheckSuccess $
            withMethod "xs: list<int>, ys: list<int>" "unit"
              "val zs: list<int> = [x + y for x in xs for y in ys]; return ();"
      , testCase "Guard uses the first generator, a second generator follows" $
          typeCheckSuccess $
            withMethod "xs: list<int>, ys: list<int>" "unit"
              "val zs: list<int> = [x + y for x in xs if x > 0 for y in ys]; return ();"
      , testCase "Guard uses both generators" $
          typeCheckSuccess $
            withMethod "xs: list<int>, ys: list<int>" "unit"
              "val zs: list<int> = [x for x in xs for y in ys if x < y]; return ();"
      , testCase "Element type may differ from the source type" $
          typeCheckSuccess $
            withMethod "xs: list<int>" "unit" "val bs: list<bool> = [x > 0 for x in xs]; return ();"
      , testCase "Source is a list literal" $
          typeCheckSuccess $
            withMethod "" "unit" "val zs: list<int> = [x for x in [1, 2, 3]]; return ();"
      , testCase "A generator over a name bound by an earlier generator" $
          typeCheckSuccess $
            withMethod "rows: list<list<int>>" "unit"
              "val zs: list<int> = [y for row in rows for y in row]; return ();"
      , testCase "Annotated by the return type" $
          typeCheckSuccess $ withMethod "xs: list<int>" "list<int>" "return [x for x in xs];"
      , testCase "Constructor in the body takes the element type" $
          typeCheckSuccess $
            withMethod "xs: list<int>" "unit"
              "val os: list<variant { A | B }> = [#A for x in xs]; return ();"
      , testCase "Constructor in the body uses the bound name" $
          typeCheckSuccess $
            withMethod "xs: list<int>" "unit"
              "val os: list<variant { Some(int) | None }> = [#Some(x) for x in xs]; return ();"
      , testCase "Storage on both sides" $
          typeCheckSuccess $ withListStorage "storage.xs = [x * 2 for x in storage.xs]; return ();"
      , testCase "As a call argument" $
          typeCheckSuccess $
            "contract C { storage: { x: int }; @private g(xs: list<int>): int { return 0; } "
              ++ "@entrypoint f(xs: list<int>): unit { val a: int = g([x for x in xs]); return (); } }"
      , testCase "Inference: the element type comes from the body" $
          typeCheckSuccess $
            withMethod "xs: list<int>" "unit" "val zs: list<int> = { a: [x + 1 for x in xs] }.a; return ();"
      , testCase "The generator name is gone after the comprehension" $
          typeCheckSuccess $
            withMethod "xs: list<int>" "unit"
              "val zs: list<int> = [x for x in xs]; val x: int = 1; return ();"
      , testCase "A generator name may shadow a parameter, like val does" $
          typeCheckSuccess $
            withMethod "x: int, xs: list<bool>" "unit" "val bs: list<bool> = [x for x in xs]; return ();"
      ]
  , testGroup "Rejected"
      [ testCase "Generator over a non-list" $
          typeCheckFailureWith
            "generator `for x in ...` needs a list, but the expression has type int" $
            withMethod "n: int" "unit" "val zs: list<int> = [x for x in n]; return ();"
      , testCase "Guard that is not bool" $
          typeCheckFailureWith
            "guard of the list comprehension has wrong type: expected bool, inferred int" $
            withMethod "xs: list<int>" "unit" "val zs: list<int> = [x for x in xs if x]; return ();"
      , testCase "Generator name used after the comprehension" $
          typeCheckFailureWith "Unknown variable `x`" $
            withMethod "xs: list<int>" "unit"
              "val zs: list<int> = [x for x in xs]; storage.x = x; return ();"
      , testCase "Guard uses a name from a generator that comes later" $
          typeCheckFailureWith "Unknown variable `y`" $
            withMethod "xs: list<int>, ys: list<int>" "unit"
              "val zs: list<int> = [x for x in xs if y > 0 for y in ys]; return ();"
      , testCase "Same name in two generators" $
          typeCheckFailureWith "Duplicate local `x`" $
            withMethod "xs: list<int>, ys: list<int>" "unit"
              "val zs: list<int> = [x for x in xs for x in ys]; return ();"
      , testCase "Generator name repeats a local" $
          typeCheckFailureWith "Duplicate local `x`" $
            withMethod "xs: list<int>" "unit"
              "val x: int = 1; val zs: list<int> = [x for x in xs]; return ();"
      , testCase "Body uses an unknown name" $
          typeCheckFailureWith "Unknown variable `z`" $
            withMethod "xs: list<int>" "unit" "val zs: list<int> = [z for x in xs]; return ();"
      , testCase "Unknown source" $
          typeCheckFailureWith "Unknown variable `nope`" $
            withMethod "" "unit" "val zs: list<int> = [x for x in nope]; return ();"
      , testCase "Source is an empty list without an annotation" $
          typeCheckFailureWith "Cannot infer the element type of `[]`" $
            withMethod "" "unit" "val zs: list<int> = [x for x in []]; return ();"
      , testCase "Element type does not match the annotation" $
          typeCheckFailureWith
            "element of initializer of val `zs` has wrong type: expected bool, inferred int" $
            withMethod "xs: list<int>" "unit" "val zs: list<bool> = [x + 1 for x in xs]; return ();"
      , testCase "Unknown tag in the body" $
          typeCheckFailureWith
            "element of initializer of val `os` uses tag `C`, which is not part of variant { A | B }" $
            withMethod "xs: list<int>" "unit" "val os: list<variant { A | B }> = [#C for x in xs]; return ();"
      , testCase "Constructor in the body without an annotation" $
          typeCheckFailureWith "Cannot infer the type of `#A`" $
            withMethod "xs: list<int>" "unit"
              "val os: list<variant { A | B }> = { a: [#A for x in xs] }.a; return ();"
      , testCase "Comprehension where a non-list is expected" $
          typeCheckFailureWith
            "initializer of val `n` has wrong type: expected int, inferred list<int>" $
            withMethod "xs: list<int>" "unit" "val n: int = [x for x in xs]; return ();"
      , testCase "Comparison: the type is found, the comparison is refused" $
          typeCheckFailureWith "Cannot compare values of type list<variant { A | B }>" $
            withMethod "xs: list<int>, ys: list<variant { A | B }>" "bool" "return [#A for x in xs] == ys;"
      ]
  ]

equalityTests :: TestTree
equalityTests = testGroup "Type checker: equality"
  [ testGroup "Accepted"
      [ testCase "Variable on the left, constructor on the right" $
          typeCheckSuccess $ withMethod "x: variant { A | B }" "bool" "return x == #A;"
      , testCase "Constructor on the left, variable on the right" $
          typeCheckSuccess $ withMethod "x: variant { A | B }" "bool" "return #A == x;"
      , testCase "!= is symmetric too" $
          typeCheckSuccess $ withMethod "x: variant { A | B }" "bool" "val p: bool = x != #B; return #B != x;"
      , testCase "Constructor with payload, on either side" $
          typeCheckSuccess $ withMethod "x: variant { Some(int) | None }" "bool"
            "val p: bool = x == #Some(1); val q: bool = #Some(1) == x; return #None == x;"
      , testCase "Payload is checked against the variable's type" $
          typeCheckSuccess $ withMethod "x: variant { Wrap(variant { A | B }) | N }" "bool"
            "return x == #Wrap(#A);"
      , testCase "Two variables of the same variant type" $
          typeCheckSuccess $ withMethod "x: variant { A | B }, y: variant { A | B }" "bool" "return x == y;"
      , testCase "Records, with or without variants inside" $
          typeCheckSuccess $ withMethod "r: { a: int, b: bool }, v: { s: variant { A | B } }" "bool"
            "val p: bool = r == { a: 1, b: true }; val q: bool = { a: 1, b: true } == r; val s: bool = v == { s: #A }; return { s: #B } == v;"
      , testCase "Two record literals" $
          typeCheckSuccess $ withMethod "" "bool" "return { a: 1 } == { a: 2 };"
      , testCase "unit is comparable" $
          typeCheckSuccess $ withMethod "" "bool" "return () == ();"
      ]
  , testGroup "Constructor on one side"
      [ testCase "Both sides need an expected type" $
          typeCheckFailureWith "Cannot infer the type of either side of this comparison" $
            withMethod "" "bool" "return #A == #B;"
      , testCase "Unknown tag on the right" $
          typeCheckFailureWith
            "right operand of equality uses tag `C`, which is not part of variant { A | B }" $
            withMethod "x: variant { A | B }" "bool" "return x == #C;"
      , testCase "Unknown tag on the left" $
          typeCheckFailureWith
            "left operand of equality uses tag `C`, which is not part of variant { A | B }" $
            withMethod "x: variant { A | B }" "bool" "return #C == x;"
      , testCase "Other side is not a variant" $
          typeCheckFailureWith
            "right operand of equality has wrong type: expected int, but `#A` builds a variant" $
            withMethod "x: int" "bool" "return x == #A;"
      , testCase "Wrong payload type" $
          typeCheckFailureWith "payload of `#Some` has wrong type: expected int, inferred bool" $
            withMethod "x: variant { Some(int) | None }" "bool" "return #Some(true) == x;"
      ]
  , testGroup "Same type is still required"
      [ testCase "int and bool keep the existing message" $
          typeCheckFailureWith "Equality requires operands of the same type (got int and bool)." $
            withMethod "" "bool" "return 1 == true;"
      , testCase "Variants with a different tag order are different types" $
          typeCheckFailureWith
            "Equality requires operands of the same type (got variant { A | B } and variant { B | A })." $
            withMethod "x: variant { A | B }, y: variant { B | A }" "bool" "return x == y;"
      ]
  , testGroup "Comparable"
      [ testCase "Lists are not comparable" $
          typeCheckFailureWith "Cannot compare values of type list<int>" $
            withMethod "xs: list<int>, ys: list<int>" "bool" "return xs == ys;"
      , testCase "!= on lists is rejected as well" $
          typeCheckFailureWith "Cannot compare values of type list<int>" $
            withMethod "xs: list<int>" "bool" "return xs != xs;"
      , testCase "A list in a storage field" $
          typeCheckFailureWith "Cannot compare values of type list<int>" $
            "contract C { storage: { xs: list<int> }; @entrypoint f(): bool { return storage.xs == storage.xs; } }"
      , testCase "A list inside a variant payload" $
          typeCheckFailureWith "Cannot compare values of type variant { A(list<int>) | B }" $
            withMethod "x: variant { A(list<int>) | B }" "bool" "return x == x;"
      , testCase "A list inside a record" $
          typeCheckFailureWith "Cannot compare values of type {n: int, xs: list<int>}" $
            withMethod "r: { n: int, xs: list<int> }" "bool" "return r == r;"
      , testCase "Comparable components make a comparable variant" $
          typeCheckSuccess $ withMethod "x: variant { A({ n: int, b: bool }) | B(unit) }" "bool" "return x == x;"
      ]
  ]

-- Entrypoint f(r: variant { Ok(int) | Err | Pending(bool) }) running @body@; storage is { x: int }.
withResult :: String -> String
withResult = withMethod "r: variant { Ok(int) | Err | Pending(bool) }" "unit"

matchTests :: TestTree
matchTests = testGroup "Type checker: match"
  [ testGroup "Accepted"
      [ testCase "Every tag covered, payload bound with its own type" $
          typeCheckSuccess $ withResult
            "match (r) { Ok(v) => { storage.x = v; } Err => { return (); } Pending(b) => { val c: bool = b; } } return ();"
      , testCase "Every tag covered, no names bound" $
          typeCheckSuccess $ withResult
            "match (r) { Ok => { return (); } Err => { return (); } Pending => { return (); } } return ();"
      , testCase "Wildcard covers the remaining tags" $
          typeCheckSuccess $ withResult
            "match (r) { Ok(v) => { storage.x = v; } _ => { return (); } } return ();"
      , testCase "Wildcard alone" $
          typeCheckSuccess $ withResult "match (r) { _ => { return (); } } return ();"
      , testCase "Wildcard that covers nothing extra is allowed" $
          typeCheckSuccess $ withResult
            "match (r) { Ok => { return (); } Err => { return (); } Pending => { return (); } _ => { return (); } } return ();"
      , testCase "Same name can be bound in different cases" $
          typeCheckSuccess $ withResult
            "match (r) { Ok(v) => { storage.x = v; } Pending(v) => { val c: bool = v; } Err => { return (); } } return ();"
      , testCase "A bound name may shadow a parameter, like val does" $
          typeCheckSuccess $ withMethod "r: variant { Ok(int) | Err }" "unit"
            "match (r) { Ok(r) => { storage.x = r; } Err => { return (); } } return ();"
      , testCase "Nested match on a bound payload" $
          typeCheckSuccess $ withMethod "r: variant { W(variant { A | B }) | N }" "unit"
            "match (r) { W(inner) => { match (inner) { A => { return (); } B => { return (); } } } N => { return (); } } return ();"
      , testCase "Scrutinee read from storage" $
          typeCheckSuccess $ withStateBody
            "match (storage.estado) { Aberto => { return (); } Fechado => { return (); } } return ();"
      , testCase "Statements after the match still see the outer names" $
          typeCheckSuccess $ withResult
            "match (r) { _ => { return (); } } storage.x = 1; return ();"
      ]
  , testGroup "Exhaustiveness"
      [ testCase "Missing tags are listed by name" $
          typeCheckFailureWith "match is not exhaustive: missing `Err`, `Pending`" $
            withResult "match (r) { Ok(v) => { return (); } } return ();"
      , testCase "A single missing tag" $
          typeCheckFailureWith "match is not exhaustive: missing `Pending`" $
            withResult "match (r) { Ok => { return (); } Err => { return (); } } return ();"
      , testCase "Match without cases" $
          typeCheckFailureWith "match has no cases" $ withResult "match (r) { } return ();"
      ]
  , testGroup "Cases"
      [ testCase "Tag handled twice" $
          typeCheckFailureWith "Tag `Err` is handled more than once" $
            withResult "match (r) { Err => { return (); } Err => { return (); } _ => { return (); } } return ();"
      , testCase "Tag not in the variant" $
          typeCheckFailureWith "Tag `Nope` is not part of variant { Ok(int) | Err | Pending(bool) }" $
            withResult "match (r) { Nope => { return (); } _ => { return (); } } return ();"
      , testCase "Case after the wildcard" $
          typeCheckFailureWith "Case `Err` comes after `_` and can never run" $
            withResult "match (r) { _ => { return (); } Err => { return (); } } return ();"
      , testCase "Second wildcard" $
          typeCheckFailureWith "Case `_` comes after `_` and can never run" $
            withResult "match (r) { _ => { return (); } _ => { return (); } } return ();"
      ]
  , testGroup "Scrutinee"
      [ testCase "Scrutinee is not a variant" $
          typeCheckFailureWith "match scrutinee must be a variant, but it has type int" $
            withResult "val n: int = 1; match (n) { _ => { return (); } } return ();"
      , testCase "Scrutinee cannot be inferred" $
          typeCheckFailureWith "Cannot infer the type of `#A`" $
            withResult "match (#A) { _ => { return (); } } return ();"
      ]
  , testGroup "Bound names"
      [ testCase "Name on a tag without payload" $
          typeCheckFailureWith "Tag `Err` has no payload, so it cannot bind a name" $
            withResult "match (r) { Err(e) => { return (); } _ => { return (); } } return ();"
      , testCase "Name repeats a local" $
          typeCheckFailureWith "Duplicate local `n`" $
            withResult "val n: int = 1; match (r) { Ok(n) => { return (); } _ => { return (); } } return ();"
      , testCase "Name is not visible after the match" $
          typeCheckFailureWith "Unknown variable `v`" $
            withResult "match (r) { Ok(v) => { return (); } _ => { return (); } } storage.x = v; return ();"
      , testCase "Locals of a case body are not visible after the match" $
          typeCheckFailureWith "Unknown variable `z`" $
            withResult "match (r) { Err => { val z: int = 1; } _ => { return (); } } storage.x = z; return ();"
      , testCase "Bound name is immutable" $
          typeCheckFailureWith "Cannot assign to immutable val `v`" $
            withResult "match (r) { Ok(v) => { v = 2; } _ => { return (); } } return ();"
      , testCase "Bound name has the payload type, so misuse is caught" $
          typeCheckFailureWith "initializer of val `c` has wrong type: expected bool, inferred int" $
            withResult "match (r) { Ok(v) => { val c: bool = v; } _ => { return (); } } return ();"
      ]
  ]

-- Contract whose storage holds a variant, with an entrypoint f running @body@.
withStateBody :: String -> String
withStateBody body =
  "contract C { storage: { estado: variant { Aberto | Fechado } }; @entrypoint f(): unit { " ++ body ++ " } }"

variantConsTests :: TestTree
variantConsTests = testGroup "Type checker: variant construction"
  [ testGroup "Accepted"
      [ testCase "Constructor with payload, annotated by val" $
          typeCheckSuccess $
            withMethod "" "unit" "val o: variant { Some(int) | None } = #Some(1); return ();"
      , testCase "Constructor without payload" $
          typeCheckSuccess $
            withMethod "" "unit" "val o: variant { Some(int) | None } = #None; return ();"
      , testCase "Constructor without payload, written with ()" $
          typeCheckSuccess $
            withMethod "" "unit" "val o: variant { Some(int) | None } = #None(); return ();"
      , testCase "Payload is an arbitrary expression" $
          typeCheckSuccess $
            withMethod "" "variant { Ok(int) | Err }" "return #Ok(1 + 2);"
      , testCase "Annotated by the return type" $
          typeCheckSuccess $
            withMethod "" "variant { Ok(int) | Err }" "return #Err;"
      , testCase "Assigned to a storage field" $
          typeCheckSuccess $ withStateBody "storage.estado = #Aberto; return ();"
      , testCase "Inside a record literal assigned to storage" $
          typeCheckSuccess $ withStateBody "storage = { estado: #Fechado }; return ();"
      , testCase "Inside a record literal in a val" $
          typeCheckSuccess $
            withMethod "" "unit" "val r: { s: variant { A | B } } = { s: #A }; return ();"
      , testCase "As a call argument" $
          typeCheckSuccess $
            "contract C { storage: { x: int }; @private g(o: variant { Some(int) | None }): int { return 0; } "
              ++ "@entrypoint f(): unit { val r: int = g(#Some(1)); return (); } }"
      , testCase "Variant nested in a variant payload" $
          typeCheckSuccess $
            withMethod "" "unit" "val w: variant { Wrap(variant { A | B }) | N } = #Wrap(#A); return ();"
      ]
  , testGroup "Rejected"
      [ testCase "Tag is not part of the expected type" $
          typeCheckFailureWith
            "initializer of val `o` uses tag `Other`, which is not part of variant { Some(int) | None }" $
            withMethod "" "unit" "val o: variant { Some(int) | None } = #Other(1); return ();"
      , testCase "Payload has the wrong type" $
          typeCheckFailureWith "payload of `#Some` has wrong type: expected int, inferred bool" $
            withMethod "" "unit" "val o: variant { Some(int) | None } = #Some(true); return ();"
      , testCase "Payload missing where one is expected" $
          typeCheckFailureWith "payload of `#Some` has wrong type: expected int, inferred unit" $
            withMethod "" "unit" "val o: variant { Some(int) | None } = #Some; return ();"
      , testCase "Payload given where none is expected" $
          typeCheckFailureWith "payload of `#None` has wrong type: expected unit, inferred int" $
            withMethod "" "unit" "val o: variant { Some(int) | None } = #None(1); return ();"
      , testCase "Expected type is not a variant" $
          typeCheckFailureWith
            "initializer of val `x` has wrong type: expected int, but `#A` builds a variant" $
            withMethod "" "unit" "val x: int = #A; return ();"
      , testCase "No expected type to take from" $
          typeCheckFailureWith "Cannot infer the type of `#A`; annotate it" $
            withMethod "" "int" "return #A + 1;"
      , testCase "Wrong tag inside a record literal names the field" $
          typeCheckFailureWith
            "field `s` of initializer of val `r` uses tag `C`, which is not part of variant { A | B }" $
            withMethod "" "unit" "val r: { s: variant { A | B } } = { s: #C }; return ();"
      , testCase "Wrong payload in a nested constructor" $
          typeCheckFailureWith "payload of `#A` has wrong type: expected unit, inferred int" $
            withMethod "" "unit" "val w: variant { Wrap(variant { A | B }) | N } = #Wrap(#A(1)); return ();"
      ]
  , testGroup "Record literals against a record type"
      [ testCase "Field type mismatch points at the field" $
          typeCheckFailureWith
            "field `a` of initializer of val `r` has wrong type: expected int, inferred bool" $
            withMethod "" "unit" "val r: { a: int } = { a: true }; return ();"
      , testCase "Field names that differ are reported as such" $
          typeCheckFailureWith
            "expected {s: variant { A | B }}, but the record literal has fields {t}" $
            withMethod "" "unit" "val r: { s: variant { A | B } } = { t: #A }; return ();"
      , testCase "Record literal where a non-record is expected keeps the old message" $
          typeCheckFailureWith "expected int, inferred {a: int}" $
            withMethod "" "unit" "val x: int = { a: 1 }; return ();"
      ]
  ]

-- Contract with a private method g(a: int, b: bool): int and an entrypoint f running @body@.
withCallBody :: String -> String
withCallBody body =
  "contract C { storage: { x: int }; @private g(a: int, b: bool): int { return a; } "
    ++ "@entrypoint f(): unit { " ++ body ++ " } }"

-- Where an expression appears decides the wording of its type error. These tests pin
-- the current messages, so replacing infer-then-compare by checkExpr cannot change them.
expectedTypeTests :: TestTree
expectedTypeTests = testGroup "Type checker: expected-type messages"
  [ testCase "return value" $
      typeCheckFailureWith "return value has wrong type: expected int, inferred bool" $
        withMethod "" "int" "return true;"
  , testCase "val initializer" $
      typeCheckFailureWith "initializer of val `y` has wrong type: expected int, inferred bool" $
        withMethod "" "unit" "val y: int = true; return ();"
  , testCase "var initializer" $
      typeCheckFailureWith "initializer of var `y` has wrong type: expected int, inferred bool" $
        withMethod "" "unit" "var y: int = true; return ();"
  , testCase "assignment to storage field" $
      typeCheckFailureWith "assignment has wrong type: expected int, inferred bool" $
        withMethod "" "unit" "storage.x = true; return ();"
  , testCase "assignment to local var" $
      typeCheckFailureWith "assignment has wrong type: expected bool, inferred int" $
        withMethod "" "unit" "var y: bool = true; y = 1; return ();"
  , testCase "call with correct arguments" $
      typeCheckSuccess $ withCallBody "val r: int = g(1, true); return ();"
  , testCase "first call argument" $
      typeCheckFailureWith "argument to `g` has wrong type: expected int, inferred bool" $
        withCallBody "val r: int = g(true, true); return ();"
  , testCase "second call argument" $
      typeCheckFailureWith "argument to `g` has wrong type: expected bool, inferred int" $
        withCallBody "val r: int = g(1, 2); return ();"
  , testCase "call argument errors are reported left to right" $
      typeCheckFailureWith "argument to `g` has wrong type: expected int, inferred bool" $
        withCallBody "val r: int = g(true, unknownName); return ();"
  , testCase "call arity" $
      typeCheckFailureWith "Function `g` expects 2 argument(s) but got 1." $
        withCallBody "val r: int = g(1); return ();"
  , testCase "call result is used with its declared type" $
      typeCheckFailureWith "initializer of val `r` has wrong type: expected bool, inferred int" $
        withCallBody "val r: bool = g(1, true); return ();"
  ]

-- Wraps one entrypoint into a contract, so type-check tests only show what matters.
withMethod :: String -> String -> String -> String
withMethod params ret body =
  "contract C { storage: { x: int }; @entrypoint f(" ++ params ++ "): " ++ ret ++ " { " ++ body ++ " } }"

variantTypeTests :: TestTree
variantTypeTests = testGroup "Type checker: variant types"
  [ testGroup "Equality"
      [ testCase "Same variant type is accepted" $
          typeCheckSuccess $
            withMethod "x: variant { A | B }" "unit" "val y: variant { A | B } = x; return ();"
      , testCase "Variant nested in record and list is accepted" $
          typeCheckSuccess $
            withMethod "x: { s: list<variant { A(int) | B }> }" "unit"
              "val y: { s: list<variant { A(int) | B }> } = x; return ();"
      , testCase "Tag order is part of the type" $
          typeCheckFailureWith "expected variant { B | A }, inferred variant { A | B }" $
            withMethod "x: variant { A | B }" "unit" "val y: variant { B | A } = x; return ();"
      , testCase "Payload type is part of the type" $
          typeCheckFailureWith "expected variant { A(bool) | B }, inferred variant { A(int) | B }" $
            withMethod "x: variant { A(int) | B }" "unit" "val y: variant { A(bool) | B } = x; return ();"
      ]
  , testGroup "Well-formedness"
      [ testCase "Duplicate tag in a storage field" $
          typeCheckFailureWith "Storage field `s` has an ill-formed type: duplicate tag `A` in variant { A | A }" $
            "contract C { storage: { s: variant { A | A } }; @entrypoint f(): unit { return (); } }"
      , testCase "Duplicate tag in a parameter" $
          typeCheckFailureWith "Parameter `p` has an ill-formed type: duplicate tag `A`" $
            withMethod "p: variant { A | A }" "unit" "return ();"
      , testCase "Duplicate tag in a return type" $
          typeCheckFailureWith "Return type of method `f` has an ill-formed type: duplicate tag `A`" $
            withMethod "" "variant { A | A }" "return ();"
      , testCase "Duplicate tag in a val type" $
          typeCheckFailureWith "Local `y` has an ill-formed type: duplicate tag `A`" $
            withMethod "x: variant { A | B }" "unit" "val y: variant { A | A } = x; return ();"
      , testCase "Duplicate tag in a var type" $
          typeCheckFailureWith "Local `y` has an ill-formed type: duplicate tag `A`" $
            withMethod "x: variant { A | B }" "unit" "var y: variant { A | A } = x; return ();"
      , testCase "Duplicate field in a record type" $
          typeCheckFailureWith "duplicate field `a` in {a: int, a: bool}" $
            withMethod "" "unit" "val r: { a: int, a: bool } = { a: 1, a: true }; return ();"
      , testCase "Duplicate field nested in a variant payload" $
          typeCheckFailureWith "duplicate field `a` in {a: int, a: bool}" $
            withMethod "x: variant { A({ a: int, a: bool }) | B }" "unit" "return ();"
      , testCase "Duplicate tag nested in a list" $
          typeCheckFailureWith "duplicate tag `A` in variant { A | A }" $
            withMethod "x: list<variant { A | A }>" "unit" "return ();"
      , testCase "Same tag at different nesting levels is allowed" $
          typeCheckSuccess $
            withMethod "x: variant { A(variant { A | B }) | B }" "unit" "return ();"
      , testCase "Same field name at different nesting levels is allowed" $
          typeCheckSuccess $
            withMethod "x: { a: { a: int } }" "unit" "return ();"
      ]
  ]
