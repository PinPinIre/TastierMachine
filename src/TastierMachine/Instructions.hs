module TastierMachine.Instructions where
import Data.Int (Int8, Int16)
import Data.List (elem)

data Instruction = Add
                 | Sub
                 | Mul
                 | Div
                 | Equ
                 | Lss
                 | Gtr
                 | Neq
                 | Leq
                 | Geq
                 | Neg
                 | Load
                 | Sto
                 | StoI
                 | LoadI
                 | Call
                 | LoadG
                 | StoG
                 | Malloc
                 | Offset
                 | Const
                 | Enter
                 | ShiftL
                 | ShiftR
                 | Jmp
                 | FJmp
                 | Ret
                 | Leave
                 | Read
                 | Write
                 | WriteStr
                 | Halt
                 | Dup
                 | Nop
                 | Pop
                 deriving (Eq, Ord, Show, Enum)

data InstructionWord = Nullary Instruction
                     | Unary Instruction Int16
                     | Binary Instruction Int16 Int16
                     deriving (Eq, Show)

arguments :: Instruction -> Int
arguments i =
  if i `elem` [Load, Sto, Call] then 2
  else if i `elem` [LoadG, StoG, Const, Enter, Jmp, FJmp] then 1
  else 0
