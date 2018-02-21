module Example where

open import Sic
open Dappsys

pow = act "cool" :: fyi₂ (# 1) (# 2) │ iff (# 0 ≡ # 1)
