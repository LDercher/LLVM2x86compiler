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
temporaries = error "Unimplemented"

parseTemps :: Instruction -> [String]
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
compileFunction = error "Unimplemented"


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
compileBlock = error "Unimplemented"

compileOperand :: TemporaryMap -> LL.Operand -> X86.SourceOperand
compileOperand tm (Const i) = Imm (Literal i)
compileOperand tm (Gid s) = IndImm (Label s)
compileOperand tm (Uid s) = fromJust (lookup s tm)


{-- 

LL.operand
data Operand = Const Int64 | Gid String | Uid String
  deriving (Eq, Read, Show)

data Instruction
    = Bin String Operator Type Operand Operand  -- %uid = binop t op, op
    | Alloca String Type                        -- %uid = alloca t
    | Load String Type Operand                  -- %uid = load t, t* op
    | Store Type Operand Operand                -- store t op1, t* op2
    | Icmp String Condition Type Operand Operand -- %uid = icmp rel t op1 op2
    | Call String Type String [(Type, Operand)] -- %uid = call ret_ty name(t1 op1, t2 op2, ...)
    | Bitcast String Type Operand Type          -- %uid = bitcast t1 op to t2
    | Gep String Type Operand [Operand]         -- %uid = getelementptr t op, i64 op1, i64 op2
                                                --    .. or i32, if accessing struct...
  deriving (Eq, Read, Show)

X86.Operand

data Immediate =
    Literal Int64
  | Label String
  deriving (Eq, Show)

data Operand imm =
    Imm imm                 -- $5
  | Reg Register            -- %rax
  | IndImm imm              -- (label)
  | IndReg Register         -- (%rax)
  | IndBoth Int64 Register  -- -4(%rax)
  deriving (Eq, Read, Show)

type SourceOperand = Operand Immediate

type SourceInstr = Instruction Immediate

type Instruction imm = (Operation, [Operand imm])

data Operation =
    movq | Pushq | Popq
  | Leaq
  | Incq | Decq | Negq | Notq
  | Addq | Subq | Imulq | Xorq | Orq | Andq
  | Shlq | Sarq | Shrq
  | Jmp | J Condition
  | Cmpq | Set Condition
  | Callq | Retq
  deriving (Eq, Read, Show)
--}

compileInstr :: Types -> TemporaryMap -> LL.Instruction -> [X86.SourceInstr]
compileInstr ty tm (Bin s opator typ opand1 opand2) = binOp (Bin s opator typ opand1 opand2) tm
compileInstr ty tm (Alloca s t) = error "i" --sub rsp by sizeof t store new 
compileInstr ty tm (Load s t o) = error "i" --move thing pointed to by operand into string
compileInstr ty tm (Store t o1 o2) = error "i" --move o1 into thing pointed at by o2
compileInstr ty tm (Icmp s c t o1 o2) =  [cmpq (compileOperand tm s) c t (compileOperand o1 tm)(compileOperand o2 tm)]--icmp ne i64 %19, note: zero temporary. and  use set to read condition flag and set tempr
compileInstr ty tm (Call s t s2 tos) = error "i" --sub from rsp appropriate space and callq func name then add back to rsp put first 6 args in regs and then alloc stack space and cleanup when done
compileInstr ty tm (Bitcast s t o t2) = error "i" --changes operand from type t to type t2 really just a move


binOp :: LL.Instruction -> TemporaryMap -> [X86.SourceInstr]
binOp (Bin s Add ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, addq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
binOp (Bin s Sub ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, subq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
binOp (Bin s Mul ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, Imulq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
binOp (Bin s Shl ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, shlq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
binOp (Bin s Lshr ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, shrq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
binOp (Bin s Ashr ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, sarq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
binOp (Bin s And ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, andq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
binOp (Bin s Or ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, orq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
binOp (Bin s Xor ty opand1 opand2) tm = [movq (compileOperand tm opand1) RAX, xorq (compileOperand tm opand2) RAX, movq RAX (compileOperand tm s)]
  


  


  


compileTerm :: TemporaryMap -> Terminator -> [X86.SourceInstr]
compileTerm = error "Unimplemented"
