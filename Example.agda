module Example where

open import Sic
open Dappsys

hello =
  act "cool" :: iff (get ①) │ ( u , t , ① ) ← u //
  act "frob" :: ⓪ ← ① │ fyi ⟨ u , t ⟩
