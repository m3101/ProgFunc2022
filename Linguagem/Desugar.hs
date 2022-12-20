module Desugar where

import AbsLI

desugarP :: Program -> Program
desugarP (Prog fs) = Prog (map desugarF fs)
       
desugarF :: Function -> Function
desugarF (Fun tR id decls stms) = Fun tR id decls (desugarS stms)
desugarS :: [Stm] -> [Stm]
desugarS [] = []
desugarS (s:stms) = case s of
                  SDecls tp id ids ->  (map (\x -> SDec (Dec tp x)) ([id]++ids)) ++ desugarS stms
                  SInit tp id exp  -> [SDec (Dec tp id),SAss id exp] ++ desugarS stms
                  SBlock stmsB     -> SBlock (desugarS stmsB) : desugarS stms
                  SDWhile stm  exp -> [stm, SWhile exp stm] ++  desugarS stms
                  _                -> s : desugarS (stms)
       
      

