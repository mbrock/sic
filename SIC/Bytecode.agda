module SIC.Bytecode where


open Oᴱ


lol = PUSH 5 ⟫ LOOP (PUSH 1 ⟫ DUP 2 ⟫ SUB) (DUP 1 ⟫ DUP 1 ⟫ SSTORE)
