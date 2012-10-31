module CodeGen (toCode
               , WhileL (..)
               , Expr (..)
               , BExpr (..)
               , sqrtPrgrm) where

import CodeGen.AG

toCode :: WhileL -> String
toCode w = sem_WhileL w 0

sqrtPrgrm :: WhileL
sqrtPrgrm =
  Seq (Seq (Assign R (EConst O)) (Assign Q (Plus (EConst (S O)) (Var N))))
    (While (Not (Eq (Plus (EConst (S O)) (Var R)) (Var Q))) (Seq (Assign P
    (Div2 (Plus (Var Q) (Var R)))) (If (Lt (Var N) (Mult (Var P) (Var P)))
    (Assign Q (Var P)) (Assign R (Var P)))))

