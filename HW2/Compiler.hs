module Compiler where

import Data.Int
import Data.List
import Data.Maybe

import LL.Language as LL
import X86 as X86

import Debug.Trace


compile :: LL.Prog -> X86.Prog
compile p =
    compileGlobals (types p) (globals p) ++
    compileFunctions (types p) (functions p)

sizeOf :: Types -> Type -> Int64
sizeOf _ Void                    = 0
sizeOf _ I1                      = 8
sizeOf _ I8                      = 8
sizeOf _ I32                     = 8
sizeOf _ I64                     = 8
sizeOf _ (Ptr _)                 = 8
sizeOf named (Struct ts)         = sum $ map (sizeOf named) ts
sizeOf _ (Array n I8)            = n
sizeOf named (Array n (Named s)) = sizeOf named (Array n (fromJust (lookup s named)))
sizeOf named (Array n t)         = n * sizeOf named t
sizeOf _ (Fun _ _)               = 0
sizeOf named (Named s)           = sizeOf named (fromJust (lookup s named))

compileGlobals :: Types -> Globals -> X86.Prog
compileGlobals named = map (compileGlobal named)

compileGlobal named (label, _, init) = (label, True, Data (compileInit init))
    where compileInit (INull) = [Word (Literal 0)]
          compileInit (IGid label) = [Word (Label label)]
          compileInit (IInt i) = [Word (Literal i)]
          compileInit (IString s) = [String s]
          compileInit (IArray inits) = concatMap compileInit (map snd inits)
          compileInit (IStruct inits) = concatMap compileInit (map snd inits)

compileFunctions :: Types -> Functions -> X86.Prog
compileFunctions named = concatMap (compileFunction named)


-- You may find the following function helpful in implementing operations on temporary storage
-- locations

type TemporaryMap = [(String, X86.SourceOperand)]

temporaries :: Cfg -> [String]
temporaries (first,rest) = concatMap parseTemps (concatMap fst (map snd blocks))
                            where blocks = ("^",first):rest

parseTemps :: LL.Instruction -> [String]
parseTemps (Bin s _ _ _ _) = [s]
parseTemps (Alloca s _) = [s]
parseTemps (Load s _ _ ) = [s]
parseTemps (Store _ _ _) = []
parseTemps (Icmp s _ _ _ _) = [s]
parseTemps (Call s _ _ _) = [s]
parseTemps (Bitcast s _ _ _) = [s]
parseTemps (Gep s _ _ _) = [s] 

-- temporaries takes the first string from insts and puts them in list

compileFunction :: Types -> (String, Function) -> X86.Prog
compileFunction tys (n, (args, retT, cfg@(first,rest))) = [(n, True, Text ([pushq ~%RBP, movq ~%RSP ~%RBP, subq ~$(8 * fromIntegral(length tm)) ~%RSP] ++
                                                            map (\((t,n), reg) -> movq ~%reg ~~(fromJust (lookup n tm))) (zip args argRegs) ++
                                                            concatMap (\((t,n), i) -> [ movq ~#(8*1 + 8, RBP) ~%RAX, movq ~%RAX ~~(fromJust (lookup n tm))]) (zip (drop 6 args) [1..]) ++
                                                            compileBlock tys tm first ))] ++ map (\(n,b) -> (n, False, Text (compileBlock tys tm b))) rest
                                                where tm = map (\(i,n) -> (n, IndBoth (-8 * i) RBP)) (zip [1..] (temporaries cfg ++ map snd args))
                                                      argRegs = [RDI, RSI, RDX, RCX, R08, R09]


--function prologue
-- 1. Push rbp
-- 2. mov rsp into rbp
-- 3. sub from rsp sizof temps
-- function epilogue
-- 1. mvp rbp into rsp
-- 2. pop rbp
-- 3. retq
--temps of cfg
--sub space from rsp
--end function 

compileBlock :: Types -> TemporaryMap -> Block -> [X86.SourceInstr]
compileBlock ts tm (insts,term) = (concatMap (\n -> compileInstr ts tm n) insts) ++ (compileTerm tm term)

compileOperand :: TemporaryMap -> LL.Operand -> X86.SourceOperand
compileOperand tm (Const i) = Imm (Literal i)
compileOperand tm (Gid s) = IndImm (Label s)
compileOperand tm (Uid s) = fromJust (lookup s tm)

compileInstr :: Types -> TemporaryMap -> LL.Instruction -> [X86.SourceInstr]
compileInstr ty tm (Bin s opator typ opand1 opand2) = [movq ~~(compileOperand tm opand1) ~%RAX, opMap ~~(compileOperand tm opand2) ~%RAX, movq ~%RAX ~~(fromJust (lookup s tm))]
                                                        where opMap = case opator of
                                                                            Add -> addq
                                                                            Sub -> subq
                                                                            Mul -> imulq
                                                                            Lshr -> shlq
                                                                            Ashr -> sarq
                                                                            And -> andq
                                                                            Or -> orq
                                                                            Xor -> xorq
compileInstr ty tm (Alloca s t) = [subq ~$(sizeOf ty t) ~%RSP, movq ~%RSP ~~(fromJust (lookup s tm))] --sub rsp by sizeof t store new 
compileInstr ty tm (Load s t o) = [ movq ~~(compileOperand tm o) ~%RAX, movq ~#RAX ~%RAX, movq ~%RAX ~~(fromJust (lookup s tm))] --move thing pointed to by operand into string
compileInstr ty tm (Store t o1 o2) = [ movq ~~(compileOperand tm o1) ~%RAX, movq ~~(compileOperand tm o2) ~%RCX, movq ~%RAX ~#RCX]--move o1 into thing pointed at by o2 
compileInstr ty tm (Icmp s c t o1 o2) =  [ movq ~~(compileOperand tm o1) ~%RAX, cmpq ~~(compileOperand tm o2) ~%RAX, set c ~~(fromJust(lookup s tm))]--icmp ne i64 %19, note: zero temporary. and  use set to read condition flag and set tempr
compileInstr ty tm (Call s t s2 tos) = regI ++ stackI ++ [callq ~$$s2, movq ~%RAX ~~(fromJust(lookup s tm))] --put first 6 args in regs and then alloc stack space and cleanup when done
                                                  where firstArgRegs = [RDI, RSI, RDX, RCX, R08, R09]
                                                        regArgs = take 6 tos
                                                        stackArgs = drop 6 tos
                                                        regI = map (\(regi, (t,op)) -> movq ~~(compileOperand tm op) ~%regi) (zip firstArgRegs regArgs)
                                                        stackI = concatMap (\(t,op) -> [movq ~~(compileOperand tm op) ~%RAX, pushq ~%RAX]) stackArgs
compileInstr ty tm (Bitcast s t o t2) = [ movq ~~(compileOperand tm o) ~%RAX, movq ~%RAX ~~(fromJust(lookup s tm))]--changes operand from type t to type t2 really just a move  

compileTerm :: TemporaryMap -> Terminator -> [X86.SourceInstr]
compileTerm tm (Ret t Nothing) = [movq ~%RBP ~%RSP, popq ~%RBP, retq]
compileTerm tm (Ret t (Just o)) = [ movq ~~(compileOperand tm o) ~%RAX, movq ~%RBP ~%RSP, popq ~%RBP, retq]
compileTerm tm (Bra s) = [jmp ~$$ s]
compileTerm tm (CBr op s1 s2) = [ cmpq ~$1 ~~(compileOperand tm op), j Eq ~$$ s1, jmp ~$$ s2]

