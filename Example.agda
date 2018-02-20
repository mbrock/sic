module Example where

open import Sic

hello = act "poke"
          (iff (get 0) │ 0 ← (# 1))
      // act "frob"
          (1 ← (# 0))
