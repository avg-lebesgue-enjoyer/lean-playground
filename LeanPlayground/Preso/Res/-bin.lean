/-
  **FILE** `LeanPlayground/Preso/Res/-bin-/.lean`
  **PURPOSE** extra shit
-/

/- IMPORTS:-/

import LeanPlayground.Preso.Res.Maybe



/- SECTION: intro flashcards -/

section flashcards.motivation
  def classic_colouring_kit : String :=
    "4-colour theorem, and its computer-aided proof; should we trust the program?"
  def today's_sponsor : List String :=
    [ "That's why PROOF ASSISTANTS are developed."
    , "...is a computation system for encoding statements and proofs, and for verifying proofs against statements."
    ]
  def humans_suck : String :=
    "We all make MISTAKES. Computers are picky enough to CATCH them."
  def programmers_untrustworthy : String :=
    "VERIFYING CRITICAL SOFTWARE (e.g. as used in mathematical proof; computer security; NASA; etc.)"
  def robots_take_jobs : String :=
    "PROOF AUTOMATION is powerful (it deals with fiddly, menial stuff; you focus on serious stuff)"
  def robots_give_jobs : String :=
    "Automation makes VERIFYING systems ACCESSIBLE to non-mathematicians (therefore more *safe* code)"
end flashcards.motivation

section flashcards.real_world
  def Gonthier : List String :=
    [ "4-colour theorem formally verified by Georges Gonthier."
    , "SOURCE: Georges Gonthier. A computer-checked proof of the Four Color Theorem. Inria. 2023. hal-04034866"
    ]
  def Dafny : List String :=
    [ "Integrated programming and verification language: Dafny"
    , "SOURCE: https://dafny.org/"
    ]
  def Nasa : List String :=
    [ "Nasa Langley Formal Methods Research Program"
    , "SOURCE: https://shemesh.larc.nasa.gov/fm/"
    ]
end flashcards.real_world



/- SECTION: `Programming.lean` -/

-- Another useful `inductive` type:
-- ⚠: Can cut this out if we get rid of `get?`.
--    ^^ yeah, can defo do this; just checked `3Proving.lean` and `4Interactively.lean`
inductive List' (α : Type) : Type where
  | nil  : List' α
  | cons : α → List' α → List' α
-- Lean notation: `nil = []` and `cons = (· :: ·)`
#reduce (0 :: (1 :: (2 :: (3 :: []))))
-- ie. *`cons 0 (cons 1 (cons 2 (cons 3 nil)))`*

/-- `get? as n` should retrieve the element of `as` at index `n`.
    If that doesn't exist, return `nothing`.
    Indices start at `0`. -/
-- ⚠: This takes two minutes to talk about, and it *isn't* proofs.
-- ⚠: I can get my 7min mark if I just cut this out.
-- ⚠: Yeah I'mma do that. We can still keep
-- ⚠:    `(as : List α) → (i : Nat) → i < length as → α`
-- ⚠: at the end, just at the cost of not showing off `List.get?`.
def get? : List α → Nat → Maybe α :=
  sorry

#reduce get? [42, 100, 1337] 0 -- `just 42`
#reduce get? [42, 100, 1337] 1 -- `just 100`
#reduce get? [42, 100, 1337] 2 -- `just 1337`
#reduce get? [42, 100, 1337] 3 -- `nothing`
