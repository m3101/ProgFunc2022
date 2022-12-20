
module Main where

import Data.Generics


import LexLI
import ParLI
import AbsLI
import Interpreter 
import Typechecker  hiding (Environment,push)
import PrintLI

import ErrM

main = do
  interact calc
  putStrLn ""

calc s = 
  let parserResult = pProgram (myLexer s) in 
         case parserResult of
           Ok  ast  -> let astCore =  ast  
                           typeCheckResult  = typeCheckP astCore in 
                         case typeCheckResult of 
                               --Typechecker.OK _ -> printTree (optimizeP  astCore)
                               --Typechecker.OK _ -> show (optimizeP  astCore)
                               Typechecker.OK _ -> show (executeP $ optimizeP  astCore)
                               Typechecker.Erro s -> s 
           Bad s -> s 
  
{-
calc s = 
  let parserResult = pProgram (myLexer s) in 
         case parserResult of
           Ok  ast  -> let astCore = desugarP ast  
                           typeCheckResult  = typeCheckP astCore in 
                         case typeCheckResult of 
                               OK _ -> show (executeP $ optimizeP  astCore)
                               Erro s -> s 
           Bad s -> s 
       
-}     

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
       
      

-- Increase salary by percentage
--increase :: Float -> Company -> Company
--increase k = everywhere (mkT (incS k))      
      
optimizeP :: Program -> Program
optimizeP = everywhere (mkT optimizeE)    
--optimizeP (Prog fs) = Prog (map optimizeF fs)
       
{-
optimizeF :: Function -> Function
optimizeF (Fun tR id decls stms) = Fun tR id decls (fst(optimizeSL ([],[]) stms))
optimizeSL :: Environment -> [Stm] -> ([Stm], Environment) 
optimizeSL env [] = ([],env)
optimizeSL env stms =  foldl ( \(ostms,oenv) s -> let (nstm,nenv) = optimizeS oenv s  in 
                                                     case s of 
                                                        CDec _ _ _ -> (ostms,nenv)  
                                                        _          -> (ostms++[nstm],nenv)  
                              )
                             ([],env)  
                             stms

optimizeS :: Environment -> Stm -> (Stm,Environment)
optimizeS env stm = case stm of
                      SReturn exp -> (SReturn (optimizeE exp env), env)
                      SAss id exp -> (SAss id  (optimizeE exp env), env)
                      SDec (Dec tp id) -> (stm,env)
                      CDec tp id exp -> (SBlock [], updateShallowValue env id (eval env exp) )
                      SBlock stms -> (SBlock (fst(optimizeSL (push env) stms)), env)
                      SWhile exp stm -> let (ns,_) = optimizeS env stm in 
                                                           (SWhile (optimizeE exp env) ns , env)
                      SIf exp stmT stmE -> let (nsT,_) = optimizeS env stmT
                                               (nsE,_) = optimizeS env stmE in (SIf (optimizeE exp env) nsT nsE, env)
                      

-}

optimizeE :: Exp ->  Exp
optimizeE exp  =  if (isGround exp) 
                      then wrapValueExpression (eval ([],[]) exp)  
                      else exp
                

{-
optimizeE :: Exp -> Environment -> Exp
optimizeE exp env = if (isGround exp env) 
                then  wrapValueExpression (eval env exp)  
                else rCE exp env
-}                                  

rCE :: Exp -> Environment -> Exp 
rCE exp env = case exp of
                        ECon exp0 exp  -> ECon (rCE exp0 env)  (rCE exp env)
                        EAdd exp0 exp  -> EAdd (rCE exp0 env)  (rCE exp env)
                        ESub exp0 exp  -> ESub (rCE exp0 env)  (rCE exp env)
                        EMul exp0 exp  -> EMul (rCE exp0 env)  (rCE exp env)
                        EDiv exp0 exp  -> EDiv (rCE exp0 env)  (rCE exp env)
                        EOr  exp0 exp  -> EOr  (rCE exp0 env)  (rCE exp env) 
                        EAnd exp0 exp  -> EAnd (rCE exp0 env)  (rCE exp env)
                        ENot exp       -> ENot (rCE exp env)
                        EStr str       -> EStr str
                        ETrue          -> ETrue
                        EFalse         -> EFalse
                        EInt n         -> EInt n
                        EVar id        -> let r = lookupDeepValueA env id in 
                                                  case r of 
                                                    Interpreter.OK v  -> (wrapValueExpression v)
                                                    Interpreter.Erro _  -> exp 
                        
                                          
                        exp            -> exp 
                        
                
wrapValueExpression :: Valor -> Exp 
wrapValueExpression (ValorInt i) = EInt i
wrapValueExpression (ValorStr s) = EStr s
wrapValueExpression (ValorBool True) = ETrue
wrapValueExpression (ValorBool False) = EFalse

isGround :: Exp ->  Bool
isGround expr  =  everything (&&) (extQ (const True) 
                                        (\ x -> case x of 
                                                   EVar _ -> False 
                                                   _ -> True)) 
                              expr


{-
isGround :: Exp -> Environment -> Bool
isGround expr env = case expr of
                        ECon exp0 exp  -> (isGround exp0 env) && (isGround exp env)
                        EAdd exp0 exp  -> (isGround exp0 env) && (isGround exp env)
                        ESub exp0 exp  -> (isGround exp0 env) && (isGround exp env)
                        EMul exp0 exp  -> (isGround exp0 env) && (isGround exp env)
                        EDiv exp0 exp  -> (isGround exp0 env) && (isGround exp env)
                        EOr  exp0 exp  -> (isGround exp0 env) && (isGround exp env)
                        EAnd exp0 exp  -> (isGround exp0 env) && (isGround exp env)
                        ENot exp       -> isGround exp env
                        EStr str       -> True
                        ETrue          -> True
                        EFalse         -> True
                        EInt n         -> True
                        EVar id        -> let v = lookupDeepValueA env id in 
                                                  case v of 
                                                    Interpreter.OK _  -> True
                                                    Interpreter.Erro msg  -> False
                        Call id lexp   -> False 
                        
-}                      