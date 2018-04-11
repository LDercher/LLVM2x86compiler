module Main where

import Compiler

import LL.Language
import LL.Parser
import LL.Lexer
import LL.Text

import X86 as X86
import X86.Text as X86
import X86.Loader as X86
import X86.Machine as X86
import X86.Simulator as X86
import X86.SimAsm as X86

import Control.Monad
import Data.List
import System.Environment

main = do progs <- mapM ((return . parse . alexScanTokens) <=< readFile) =<< getArgs
          putStrLn (textOf $ concatMap (compileFunction []) (concatMap functions progs))

doCompile inputs =
    do progs <- mapM ((return . parse . alexScanTokens) <=< readFile) inputs
       return (concatMap (compileFunction []) (concatMap functions progs))

toFile inputs output =
    do progs <- mapM ((return . parse . alexScanTokens) <=< readFile) inputs
       writeFile output (textOf $ concatMap (compileFunction []) (concatMap functions progs))

toScreen inputs =
    do progs <- mapM ((return . parse . alexScanTokens) <=< readFile) inputs
       putStrLn (textOf $ concatMap (compileFunction []) (concatMap functions progs))

traceExec watchList m =
    do putStrLn ("<" ++ show (getRIP m) ++ "> " ++ pad 30 (textOf instr) ++ " " ++ intercalate ", " [textOf op ++ " = " ++ show (getOperand op m) | op <- watchList])
       let m' = step m
       if getRIP m' == haltAddr
       then putStrLn ("Finished; RAX = " ++ show (getRegister RAX m'))
       else traceExec watchList m'
    where Inst instr = getMemory (getRIP m) m
          pad n s | length s >= n = s
                  | otherwise = s ++ replicate (n - length s) ' '
