module Optimizer where

import AbsLI
import Interpreter 

optimizeP :: Program -> Program
optimizeP (Prog fs) = Prog (map optimizeF fs)
       
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
                      SWhile exp stm -> let optExp = optimizeE exp env 
                                            optWhile = SWhile optExp (fst (optimizeS env stm))  in
                                          case optExp of
                                             EInt vExpWhile -> if (vExpWhile == 0)
                                                                 then (SBlock [],env)
                                                                 else (optWhile, env)
                                             _              ->  (optWhile, env)
                      SIf exp stmT stmE -> let optExp = optimizeE exp env 
                                               optThen = fst(optimizeS env stmT)
                                               optElse = fst(optimizeS env stmE) in 
                                              case optExp of
                                                 EInt vExpIf -> if (vExpIf == 0)
                                                                     then (optElse,env)
                                                                     else (optThen,env)
                                                 _              -> (SIf optExp optThen optElse , env)

optimizeE :: Exp -> Environment -> Exp
optimizeE exp env = case exp of
                       EStr str       -> EStr str
                       ETrue          -> ETrue
                       EFalse         -> EFalse
                       EInt n         -> EInt n
                       EVar id        -> let r = lookupDeepValueA env id in 
                                              case r of 
                                                 Interpreter.OK v  -> (wrapValueExpression v)
                                                 Interpreter.Erro _  -> exp 
                       eNot@(ENot exp)-> if (isLiteral exp) 
                                           then  wrapValueExpression (eval ([],[]) eNot )
                                           else  ENot (optimizeE  exp env)
                       eCon@(ECon exp0 exp) -> let optExp0 = optimizeE  exp0 env
                                                   optExp  = optimizeE  exp  env in 
                                                     if ( (isLiteral optExp0) && (isLiteral optExp) )
                                                       then wrapValueExpression (eval ([],[]) (ECon optExp0 optExp))
                                                       else ECon optExp0 optExp  
                       eAdd@(EAdd exp0 exp) -> let optExp0 = optimizeE  exp0 env
                                                   optExp  = optimizeE  exp  env in 
                                                     if ( (isLiteral optExp0) && (isLiteral optExp) ) 
                                                       then wrapValueExpression (eval ([],[]) (EAdd optExp0 optExp))
                                                       else EAdd optExp0 optExp  
                       eSub@(ESub exp0 exp) -> let optExp0 = optimizeE  exp0 env
                                                   optExp  = optimizeE  exp  env in 
                                                     if ( (isLiteral optExp0) && (isLiteral optExp) ) 
                                                       then wrapValueExpression (eval ([],[]) (ESub optExp0 optExp))
                                                       else ESub optExp0 optExp
                       eMul@(EMul exp0 exp) -> let optExp0 = optimizeE  exp0 env
                                                   optExp  = optimizeE  exp  env in 
                                                     if ( (isLiteral optExp0) && (isLiteral optExp) ) 
                                                       then wrapValueExpression (eval ([],[]) (EMul optExp0 optExp))
                                                       else EMul optExp0 optExp
                       eDiv@(EDiv exp0 exp) -> let optExp0 = optimizeE  exp0 env
                                                   optExp  = optimizeE  exp  env in 
                                                     if ( (isLiteral optExp0) && (isLiteral optExp) ) 
                                                       then wrapValueExpression (eval ([],[]) (EDiv optExp0 optExp))
                                                       else EDiv optExp0 optExp
                       eOr@(EOr  exp0 exp)  -> let optExp0 = optimizeE  exp0 env
                                                   optExp  = optimizeE  exp  env in 
                                                     if ( (isLiteral optExp0) && (isLiteral optExp) ) 
                                                       then wrapValueExpression (eval ([],[]) (EOr optExp0 optExp))
                                                       else EOr optExp0 optExp
                       eAnd@(EAnd exp0 exp) -> let optExp0 = optimizeE  exp0 env
                                                   optExp  = optimizeE  exp  env in 
                                                     if ( (isLiteral optExp0) && (isLiteral optExp) ) 
                                                       then wrapValueExpression (eval ([],[]) (EAnd optExp0 optExp))
                                                       else EAnd optExp0 optExp
                       Call id lexp   -> Call id (map (\expr ->  optimizeE expr env) lexp) 

                        
isLiteral :: Exp -> Bool
isLiteral exp = case exp of
                        EStr  _        -> True
                        ETrue          -> True
                        EFalse         -> True
                        EInt  _        -> True
                        _              -> False

wrapValueExpression :: Valor -> Exp 
wrapValueExpression (ValorInt i) = EInt i
wrapValueExpression (ValorStr s) = EStr s
wrapValueExpression (ValorBool True) = ETrue
wrapValueExpression (ValorBool False) = EFalse



