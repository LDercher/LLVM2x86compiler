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
compileFunction tys (s,f) = error "i"--[(s,False,[])]


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
compileBlock ts tm (insts,term) = concatMap (compileInstr ts tm) insts ++ (compileTerm tm term)

compileOperand :: TemporaryMap -> LL.Operand -> X86.SourceOperand
compileOperand tm (Const i) = Imm (Literal i)
compileOperand tm (Gid s) = IndImm (Label s)
compileOperand tm (Uid s) = fromJust (lookup s tm)

compileInstr :: Types -> TemporaryMap -> LL.Instruction -> [X86.SourceInstr]
compileInstr ty tm (Bin s opator typ opand1 opand2) = binOp (Bin s opator typ opand1 opand2) tm
compileInstr ty tm (Alloca s t) = [(Subq, [Imm (Literal (sizeOf ty t)),Reg RSP])] --sub rsp by sizeof t store new 
compileInstr ty tm (Load s t o) = [(Movq,[(fromJust(lookup s tm)), Reg RAX]),(Movq,[IndReg RAX,Reg RAX]),(Movq,[Reg RAX,(compileOperand tm o)])] --move thing pointed to by operand into string
compileInstr ty tm (Store t o1 o2) = [(Movq, [(compileOperand tm o1),Reg RAX]),(Movq,[(compileOperand tm o2), Reg RCX]),(Movq,[Reg RAX, IndReg RCX])]--move o1 into thing pointed at by o2 
compileInstr ty tm (Icmp s c t o1 o2) =  [(Movq,[(Imm (Literal 0)),(fromJust(lookup s tm))]),(Cmpq, [(compileOperand tm o1),(compileOperand tm o2)]),(Set c,[(fromJust(lookup s tm))])]--icmp ne i64 %19, note: zero temporary. and  use set to read condition flag and set tempr
compileInstr ty tm (Call s t s2 tos) = error "i" --sub from rsp appropriate space and callq func name then add back to rsp put first 6 args in regs and then alloc stack space and cleanup when done
compileInstr ty tm (Bitcast s t o t2) = error "i"--changes operand from type t to type t2 really just a move

--cond2Op :: Condition -> X86.SourceOperand
--cond2Op 

binOp :: LL.Instruction -> TemporaryMap -> [X86.SourceInstr]
binOp (Bin s Add ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1),Reg RAX]), (Addq, [(compileOperand tm opand2),Reg RAX]), (Movq, [Reg RAX, (fromJust (lookup s tm))])]
binOp (Bin s Sub ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1), Reg RAX]), (Subq, [(compileOperand tm opand2), Reg RAX]), (Movq, [Reg RAX, (fromJust (lookup s tm))])]
binOp (Bin s Mul ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1), Reg RAX]), (Imulq, [(compileOperand tm opand2), Reg RAX]), (Movq, [Reg RAX, (fromJust(lookup s tm))])]
binOp (Bin s Shl ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1), Reg RAX]), (Shlq, [(compileOperand tm opand2),Reg RAX]), (Movq, [Reg RAX, (fromJust (lookup s tm))])]
binOp (Bin s Lshr ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1), Reg RAX]), (Shrq, [(compileOperand tm opand2),Reg RAX]), (Movq,[Reg RAX, (fromJust (lookup s tm))])]
binOp (Bin s Ashr ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1), Reg RAX]), (Sarq, [(compileOperand tm opand2),Reg RAX]), (Movq,[Reg RAX, (fromJust (lookup s tm))])]
binOp (Bin s And ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1), Reg RAX]), (Andq, [(compileOperand tm opand2),Reg RAX]), (Movq, [Reg RAX, (fromJust (lookup s tm))])]
binOp (Bin s Or ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1), Reg RAX]), (Orq, [(compileOperand tm opand2),Reg RAX]),(Movq,[Reg RAX, (fromJust (lookup s tm))])]
binOp (Bin s Xor ty opand1 opand2) tm = [(Movq ,[(compileOperand tm opand1), Reg RAX]), (Xorq, [(compileOperand tm opand2),Reg RAX]),(Movq,[Reg RAX, (fromJust (lookup s tm))])]
  

compileTerm :: TemporaryMap -> Terminator -> [X86.SourceInstr]
compileTerm tm (Ret t Nothing) = [(Retq,[])]
compileTerm tm (Ret t (Just o)) = [(Movq,[(compileOperand tm o), Reg RAX])]
compileTerm tm (Bra s) = [(Jmp, [(fromJust (lookup s tm))])]
compileTerm tm (CBr op s1 s2) = [(Cmpq ,[(compileOperand tm op),Imm (Literal 1)]),(J Eq,[(fromJust(lookup s1 tm))]),(Jmp,[(fromJust(lookup s2 tm))])]

