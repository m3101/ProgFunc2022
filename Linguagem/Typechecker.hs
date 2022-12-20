module Typechecker where

import AbsLI
import Prelude hiding (lookup)
import PrintLI


data Resultado a = OK a | Erro String                                   
         deriving (Eq, Ord, Show, Read)

instance Functor Resultado where
   fmap f (Erro a) = Erro a
   fmap f (OK a) = OK (f a)
instance Applicative Resultado where
   pure = OK
   (<*>) (OK f) (OK v) = OK (f v)
   (<*>) (Erro e) _ = Erro e
   (<*>) _ (Erro e) = Erro e
instance Monad Resultado where
   (>>=) (Erro a) f = Erro a
   (>>=) (OK a) f = f a

comErro :: Resultado a -> String -> Resultado a
comErro (OK a) _ = OK a
comErro (Erro e) s = Erro (e++s)

isError e = case e of
    OK _ -> False
    Erro _ -> True 

typeCheckP :: Program  -> Resultado [Resultado Environment]
typeCheckP (Prog fs) = do {
   env<-updatecF ([],[]) fs;
   OK (map (typeCheckFF env) fs)
}

-- Pergunta: Há como melhorar esse "if"?
typeCheckFF ::  Environment -> Function -> Resultado Environment
typeCheckFF environment f@(Fun tR id decls stms) = ensureDeadCodeFree stms
                                                   >> (if tR/=Tvoid then ensureCheckExecutionPathExhaustion stms else return stms)
                                                   >> typeCheckF environment f

{-
As funcoes "checkExecutionPathExhaustion" e "checkExecutionPathExhaustionS" colaboram
para checar se todo possivel fluxo de execucao do programa termina em comando "return",
em cujo caso a primeira funcao retorna true.
-}

ensureCheckExecutionPathExhaustion :: [Stm] -> Resultado [Stm]
ensureCheckExecutionPathExhaustion s = if checkExecutionPathExhaustion s then OK s else Erro "Nem todo caminho de execução tem comando return!"

checkExecutionPathExhaustion :: [Stm] -> Bool
checkExecutionPathExhaustion [] = False
checkExecutionPathExhaustion (s:stms) = if (checkExecutionPathExhaustionS s) 
                                             then (stms == [])
                                             else (checkExecutionPathExhaustion stms)

checkExecutionPathExhaustionS :: Stm -> Bool
checkExecutionPathExhaustionS x = case x of
                                     SReturn exp -> True
                                     SAss id exp -> False
                                     SDec (Dec tp id) -> False 
                                     CDec tp id  exp -> False
                                     SBlock stms -> checkExecutionPathExhaustion stms
                                     SWhile exp stm -> checkExecutionPathExhaustionS stm
                                     SIf exp stmT stmE -> (checkExecutionPathExhaustionS stmT) && 
                                                          (checkExecutionPathExhaustionS stmE)

ensureDeadCodeFree :: [Stm] -> Resultado [Stm]
ensureDeadCodeFree s = if deadCodeFree s then OK s else Erro "Há deadcode no Programa!"

deadCodeFree :: [Stm] -> Bool
deadCodeFree [] = True
deadCodeFree (s:stms) =  if  (deadCodeFreeS s)
                            then  if (checkExecutionPathExhaustionS s)  
                                     then (stms == [])
                                     else (deadCodeFree stms)
                            else False 


deadCodeFreeS  :: Stm -> Bool
deadCodeFreeS   x = case x of
                      SReturn exp -> True
                      SAss id exp -> True
                      SDec (Dec tp id) -> True 
                      CDec tp id  exp -> True
                      SBlock stms -> deadCodeFree stms
                      SWhile exp stm -> deadCodeFreeS stm
                      SIf exp stmT stmE -> (deadCodeFreeS stmT) && (deadCodeFreeS stmE)
                      

                                                  
typeCheckF ::  Environment -> Function -> Resultado Environment    
typeCheckF environment (Fun tR id decls stms) = tk newEnvironment (SBlock stms) tR
                                                  where typeBindings = map (\(Dec tp id) -> (id,(tp,"not constant"))) decls
                                                        newEnvironment = pushB  typeBindings environment 

                                                  
tk :: Environment -> Stm -> Type -> Resultado Environment


tk environment x  tR = case x of
-- SDecls tp id []  ->   
-- cDec@(SDecls tp id (i:is)) -> 
-- cAssInit@(SInit tp id exp)  -> 
-- cDWhile@(SDWhile stm exp) ->  
   cDec@(CDec tp id exp) -> do{
                              env<-updateShallowTypeA environment id (tp,"constant");
                              x<-tinf env exp;
                              tke env (EVar id) x
                            }`comErro` (" no comando: " ++ printTree cDec)
   SReturn exp  ->  tke environment exp tR
   cAss@(SAss id exp) -> do{
                           x<-if lookupDeepTypeA environment id /= "constant" then
                                 tinf environment exp
                              else Erro ("@typechecker: " ++ show id ++ " eh constante e nao pode ser redefinida no comando: " ++ printTree cAss);
                           tke environment (EVar id) x
                         }`comErro` (" no comando: " ++ printTree cAss)
   SBlock [] -> OK environment
   SBlock ( cDec@(SDec (Dec tp id)):stms) -> do{
                                                env<-updateShallowType environment id tp;
                                                tk env (SBlock stms) tR
                                             }`comErro` (" no comando:" ++ printTree cDec)
   SBlock (sb@(SBlock bls):stms) -> (
                                       tk(push environment) sb tR
                                       >>tk environment (SBlock stms) tR
                                    )`comErro` (" no comando:" ++ printTree sb)
   SBlock (s:stms) -> do{
                        env<-tk environment s tR;
                        tk env (SBlock stms) tR
                      }
   cWhile@(SWhile exp stm) -> (
                                 tke environment exp Tint
                                 >>tk environment stm tR
                              )`comErro` (" no comando" ++ printTree cWhile)
   cIf@(SIf exp stmT stmE) -> (
                                 tke environment exp Tint
                                 >>tk environment stmT tR
                                 >>tk environment stmE tR
                              ) `comErro` (" no comando" ++ printTree cIf)
                           
tke :: Environment -> Exp -> Type -> Resultado Environment
tke environment exp tp = do{
                           tipo<-tinf environment exp;
                           if tipo == tp then
                              OK environment
                           else Erro (" @typechecker:  A expressao "++ printTree exp ++ " tem tipo " ++ printTree tipo ++
                                       " mas o tipo esperado eh " ++ printTree tp)
                         }

combChecks :: Environment -> Exp -> Exp -> Type -> Resultado Type
combChecks environment exp1 exp2 tp =  tke environment exp1 tp >> tke environment exp2 tp >> OK tp

tinf :: Environment -> Exp -> Resultado Type
tinf environment x  =  case x of
    ECon exp0 exp  -> combChecks environment exp0 exp TStr
    EAdd exp0 exp  -> combChecks environment exp0 exp Tint
    ESub exp0 exp  -> combChecks environment exp0 exp Tint
    EMul exp0 exp  -> combChecks environment exp0 exp Tint
    EDiv exp0 exp  -> combChecks environment exp0 exp Tint
    EOr  exp0 exp  -> combChecks environment exp0 exp Tbool
    EAnd exp0 exp  -> combChecks environment exp0 exp Tbool
    ENot exp       -> tke environment exp Tbool >> OK Tbool
    EStr str       -> OK TStr  
    ETrue          -> OK Tbool 
    EFalse         -> OK Tbool  
    EInt n         -> OK Tint  
    EVar id        -> lookupDeepType environment id
    Call id lexp   -> do{
                        retorno<-lookupShallowFunction environment id;
                        let
                           (TFun (Fun tipoRetorno _ decls stms)) = retorno
                           parameterTypes =  map (\(Dec tp _ )-> tp) decls
                           tksArgs = zipWith (tke environment) lexp parameterTypes
                        in
                        if length decls == length lexp then
                           if not (any isError tksArgs) then
                              Erro " @typechecker: chamada de funcao invalida"
                           else OK tipoRetorno                              
                        else Erro " @typechecker: tamanhos diferentes de lista de argumentos e parametros"
                      }

type Annotation = String
type Environment = ([RContext],RContext)
type RContext = [(Ident,(Type,Annotation))]

pushB :: RContext -> Environment -> Environment
pushB typeBindings (sc,fnCtx) =  (  typeBindings : sc, fnCtx) 

push :: Environment -> Environment
push (sc,fnCtx) = ([]:sc,fnCtx)
 
pop :: Environment -> Environment
pop ((s:scs),fnCtx) = (scs,fnCtx)

lookupDeepTypeA :: Environment -> Ident -> Annotation
--lookupDeepType ([],fnCtx) id = Erro (printTree id ++ " nao esta no contexto. ")
lookupDeepTypeA ((s:scs),fnCtx) id =  let r = lookupShallow s id in
                                           case r of
                                              OK (_,a) -> a 
                                              Erro _ -> lookupDeepTypeA (scs,fnCtx) id

lookupDeepType :: Environment -> Ident -> Resultado Type
lookupDeepType ([],fnCtx) id = Erro ("@typechecker: " ++ printTree id ++ " nao esta no contexto. ")
lookupDeepType ((s:scs),fnCtx) id =  let r = lookupShallow s id in
                                         case r of
                                            OK (tp,_) -> OK tp
                                            Erro _ -> lookupDeepType (scs,fnCtx) id
                                            
lookupShallowFunction :: Environment -> Ident -> Resultado Type
lookupShallowFunction (sc,fnCtx) id =  let r =(lookupShallow fnCtx id) in
                                         case r of
                                            OK (tp,_) -> OK tp
                                            Erro msg -> Erro msg 


lookupShallow :: RContext -> Ident -> Resultado (Type,Annotation)
lookupShallow [] s = Erro ("@typechecker: " ++ printTree s ++ " nao esta no contexto. ")
lookupShallow ((i,v):cs) s
   | i == s = OK v
   | otherwise = lookupShallow cs s

updateShallowTypeA :: Environment -> Ident -> (Type,Annotation) -> Resultado Environment
updateShallowTypeA  ([],fnCtx) id (tp,a)     = OK ([[(id,(tp,a))]],fnCtx)
updateShallowTypeA  (s:sc,fnCtx) id (tp,a) = do{
                                                   ctx<-updateShallowA s id (tp,a);
                                                   OK (ctx:sc,fnCtx)
                                               }
                                                
updateShallowA :: RContext -> Ident -> (Type,Annotation) -> Resultado RContext
updateShallowA context id (tp,a) = if (elem id (map fst context))
                                     then Erro "@typechecker: tipo ja definido no contexto de tipos"
                                     else OK ((id,(tp,a)):context)

updateShallowType :: Environment -> Ident -> Type -> Resultado Environment
updateShallowType ([],fnCtx) id tp = OK ([[(id,(tp,"not constant"))]],fnCtx)
updateShallowType (s:sc,fnCtx) id tp = do{
                                          ctx<-updateShallowA s id (tp,"not constant");
                                          OK (ctx:sc,fnCtx)
                                       }

updatecF :: Environment -> [Function] -> Resultado Environment
updatecF e [] = OK e
updatecF (sc,c) (f@(Fun tp id params stms):fs) = do{
                                                   ctx<-updateShallowA c id (TFun f,"constant");
                                                   updatecF (sc,ctx) fs
                                                }