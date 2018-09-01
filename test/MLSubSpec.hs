module MLSubSpec where

import Test.Hspec

import qualified Data.Map.Lazy as Map

import MLSub

spec :: Spec
spec = do
  describe "infer" $
    it "infer" $ do
      let tvar = TVar . Ident

      typeOf (infer (Context [PolyType (mempty, RecordType (Map.singleton (Label "a") Int))]) (App (Abs "x" (Var 0)) (Var 0))) (KindContext mempty) `shouldBe` return
        ( RecordType (Map.fromList [(Label "a", Int)])
        , KindContext $ Map.fromList [(Ident 0, mempty), (Ident 1, mempty)]
        )
      typeOf (infer (Context []) $ Abs "x" $ Var 0) (KindContext mempty) `shouldBe`
        return (tvar 0 :-> tvar 0, KindContext $ Map.singleton (Ident 0) mempty)
      typeOf (infer (Context []) $ Abs "x" $ Var 0 `Select` Label "b") (KindContext mempty) `shouldBe` return
        ( tvar 2 :-> tvar 1
        , KindContext (Map.fromList
          [ (Ident 0, mempty)
          , (Ident 1, mempty)
          , (Ident 2, RecordKind $ Map.singleton (Label "b") (tvar 1))
          ])
        )
      typeOf (infer (Context []) $ Abs "x" $ Record $ Map.singleton (Label "a") $ Var 0) (KindContext mempty) `shouldBe` return
        ( tvar 0 :-> RecordType (Map.singleton (Label "a") $ tvar 0)
        , KindContext $ Map.singleton (Ident 0) mempty
        )
      typeOf (infer (Context []) $ Abs "x" $ Record $ Map.fromList [(Label "a", Var 0), (Label "b", Var 0 `Select` Label "c")]) (KindContext mempty) `shouldBe` return
        ( tvar 2 :-> RecordType (Map.fromList
          [ (Label "a", tvar 2)
          , (Label "b", tvar 1)
          ])
        , KindContext $ Map.fromList
          [ (Ident 0, mempty)
          , (Ident 1, mempty)
          , (Ident 2, RecordKind (Map.singleton (Label "c") $ tvar 1))
          ]
        )
      typeOf (infer (Context []) $ Let (Abs "x" $ Var 0) $ Var 0) (KindContext mempty) `shouldBe` return
        ( tvar 1 :-> tvar 1
        , KindContext $ Map.singleton (Ident 1) mempty
        )
      typeOf (infer (Context []) $ Let (Abs "x" $ Var 0) $ Var 0 `App` (Abs "y" $ Var 0 `Select` Label "r")) (KindContext mempty) `shouldBe` return
        ( tvar 4 :-> tvar 3
        , KindContext $ Map.fromList
          [ (Ident 1, mempty)
          , (Ident 2, mempty)
          , (Ident 3, mempty)
          , (Ident 4, RecordKind (Map.singleton (Label "r") $ tvar 3))
          , (Ident 5, mempty)
          ]
        )
      typeOf (infer (Context []) $ Let (Abs "x" $ Var 0) $ Let (Var 0 `App` (Abs "y" $ Var 0 `Select` Label "r")) $ Var 1 `App` Record (Map.singleton (Label "e") (Var 0))) (KindContext mempty) `shouldBe` return
        ( RecordType $ Map.singleton (Label "e") (tvar 8 :-> tvar 7)
        , KindContext $ Map.fromList
          [ (Ident 1, mempty)
          , (Ident 2, mempty)
          , (Ident 5, mempty)
          , (Ident 6, mempty)
          , (Ident 7, mempty)
          , (Ident 8, RecordKind (Map.singleton (Label "r") $ tvar 7))
          , (Ident 9, mempty)
          ]
        )
      typeOf (infer (Context [PolyType (mempty, (RecordType $ Map.singleton (Label "q") Int) :-> Int)]) $ Abs "x" $ Var 1 `App` Record (Map.singleton (Label "q") (Var 0))) (KindContext mempty) `shouldBe` return
        ( Int :-> Int
        , KindContext $ Map.fromList
          [ (Ident 0, mempty)
          , (Ident 1, mempty)
          ]
        )
      typeOf (infer (Context []) $ Var 0) (KindContext mempty) `shouldBe` Left (UnboundVariable 0 $ Context [])
