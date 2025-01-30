/-
  **FILE** `LeanPlayground/Preso/Res/1False.lean`
  **PURPOSE** Flashcards for the introduction to the preso
-/


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
