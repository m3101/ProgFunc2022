module Main where

import LexLI
import ParLI
import AbsLI
import Desugar
import Typechecer  hiding (Environment,push)
import Optimizer
import Interpreter 
import PrintLI
import ErrM

main = do
  interact calc
  putStrLn ""

calc soureCode = 
  let parserResult = pProgram (myLexer soureCode) in 
    case parserResult of
       Ok ast -> (let astCore = desugarP ast 
                      typeCheckResult = typeCheckP astCore in 
                      if (any isError typeCheckResult)  
                        then (show (filter isError typeCheckResult))  
                        else let optProgram = optimizeP astCore in 
                                   ">>>>>>> Programa original:<<<<<<< \n"  ++ (printTree ast)++ "\n" ++
                                   ">>>>>>> Programa otimizado:<<<<<<< \n" ++ (printTree optProgram) ++ "\n" ++ 
                                   ">>>>>>> Resultado da execucao:<<<<<<< \n" ++ (show (executeP optProgram)))
       Bad erorMessage -> erorMessage
  

  
