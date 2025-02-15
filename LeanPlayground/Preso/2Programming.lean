/-
  **FILE** `LeanPlayground/Preso/2Programming.lean`
  **PURPOSE** Introduction to programming
-/
set_option pp.fieldNotation false
set_option linter.unusedVariables false

namespace ν

/- SECTION: Terms, Types and Functions -/

-- Everything in Lean is a **term**
example := 42
example := [0, 1, 2, 3]
example := fun x => x + 1
example := Nat

-- All terms are categorised by **types**
-- NOTE: `#check` each of the things above

-- *Computation* is about turning terms into other terms.
-- We do this using **functions**
-- NOTE: Give examples of functions
-- TESTING::
#eval (fun x => x + 1) (42)
#eval (fun x => x + 1)  42
#eval (fun x y => x + y) 4 2
-- ::TESTING

-- Functions are categorised by **function types** (`A → B`)
-- Let's write our own function of type `Nat → List Nat`:
-- TESTING::
def funny : Nat → List Nat :=
  fun x => [x, x]
#eval funny 6
-- ::TESTING

-- We can simulate "multiple arguments" with the following pattern:
--  `: A → (B → C)`   (aka. `A → B → C`)
-- TESTING::
def hilarious : Nat → (Nat → Nat) :=
  fun x y => x + (2 * y)
#eval hilarious 4 2
-- ::TESTING

/- SECTION: Inductive Types -/

-- To do *interesting* computation, we need to build our own types.
-- For this, we have **inductive** types.

inductive NatPair : Type where
  | intro : Nat → Nat → NatPair

-- `NatPair.intro` creates new `NatPair`s
def fourTwo : NatPair := NatPair.intro 4 2

-- Most importantly, we have **pattern matching** on inductive types:
def NatPair.sum : NatPair → Nat :=
  fun p =>
  match p with
  | intro x y => x + y
#eval NatPair.sum fourTwo

-- `NatPair` generalises to the **product type**:
inductive Product (α β : Type) : Type where
  | intro : α → β → Product α β
-- With "projection maps":
def Product.first : Product α β → α :=
  fun p =>
  match p with
  | intro a b => a
def Product.second : Product α β → β :=
  fun p =>
  match p with
  | intro a b => b
-- Lean uses the notation `· × ·` in place of `Product`:
#check Nat × String

-- `inductive` types can have more than one constructor; meet the **sum type**:
inductive Sum' (α β : Type) : Type where
  | inl : α → Sum' α β
  | inr : β → Sum' α β
-- Lean notation: `· ⊕ ·`
def addOneOrTimesTwo : Nat ⊕ Nat → Nat :=
  fun x =>
  match x with
  | .inl a => a + 1
  | .inr b => b * 2

-- A cool use of the sum type is in the **`Option`** type:
inductive Option' (α : Type) : Type where
  | none : Option' α
  | some : α → Option' α
-- It provides error behaviour:
def divide : Nat → Nat → Option Nat :=
  fun numerator divisor =>
  if divisor = 0
  then none
  else some (numerator / divisor)

-- Most impressively, `inductive` types can be **recursive**:
inductive List' (α : Type) : Type where
  | nil  : List' α
  | cons : α → List' α → List' α
-- Lean notation: `nil = []` and `cons = (· :: ·)`
#eval (0 :: (1 :: (2 :: (3 :: List.nil))))

-- This is enough power to start capturing mathematical ideas:
inductive ℕ : Type where
  | zero : ℕ
  | succ : ℕ → ℕ  -- `succ n` is "the successor of `n`", aka. `n + 1`.

-- We define functions on `inductive` data types using **recursion**:
def List.get'? : List α → Nat → Option α :=
  fun as n =>
  match as with
  | [] => none
  | (a :: as') =>
    match n with
    | .zero => a
    | .succ n' => List.get'? as' n' -- The `1 + n'`th element of `a :: as'` is the `n'`th element of `as'`.





/- TEST: Scratch crap that shouldn't be left here -/

-- TODO: Introduce, with examples etc., all the programming concepts that I've marked on the whiteboard.
--        `→` should be introduced pretty soon after the basics of *types*
--        `×`, `⊕` should be introduced via `inductive` definition
--        `inductive Nat` and `inductive List` should be in there for recursion and eventual induction.
--          `List` also subtly introduces *dependent types*, which is essential to understanding the definition of `=`.
-- TODO: Make them culminate into something that we can *reason* about later in the presentation, and prove interesting results for.
--  Should consider: **logic** via `×`, `⊕`, (dep.) `→` will be discussed in `3Proving.lean`
--  Should consider: **equality** via its `inductive` definition will be discussed in `3Proving.lean`
--  Should consider: we'll need examples of **types of mathematical objects** to actually do proofs on within `3Proving.lean`
--                   ^^ that said, some programming-oriented types (e.g. `List`) would be interesting too.
--                      Passing thought: how easy is it to verify that the piss-simple recursive `quicksort` is correct?
--                      ^^ It's too long for a presentation, but "after sorting, the list is now sorted" (although may not contain same elements)
--                          could be within reach (with some background lemmas, such as `filter_length_le` and `mem_filter`).
--                          ^^ Nope; you need to prove that indices are in-bounds, and that would take too long to explain.
--                      ^^ maybe a piss-simple `filter` instead?
--                          ^^ Proving termination is boring, and proving the set-filter contract is tedious
--                      ^^ Termination results could be interesting too, since Lean forces them upon us
--  Should consider: we'll need types amenable to **induction** with real juicy recursion.

namespace ν

inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α → List α
deriving Repr
export List (nil cons)

#check @nil
#check @cons

-- WARNING: I have no fkn clue why this `match` will update the types of `noneBranch` and `someBranch` for me.
def Option.bazorp.{u} {α β : Type u} : (oa : Option α) → (oa = none → β) → ((a : α) → (oa = some a) → β) → β :=
  fun oa noneBranch someBranch =>
  match oa with
  | none => noneBranch rfl
  | some a => someBranch a rfl

namespace List
  -- NOTE: This is easy to define. It's kinda like addition... funny that
  def append (xs ys : List α) : List α :=
    match xs with
    | nil => ys
    | cons x xs' => cons x (xs'.append ys)
  -- NOTE: This proof is rather easy to write and demonstrate
  theorem append_assoc : ∀ (xs ys zs : List α), (xs.append ys).append zs = xs.append (ys.append zs) := by
    intro xs ys zs
    match xs with
    | nil => rfl
    | cons x xs' =>
      calc  ((cons x xs').append ys).append zs
        _ = (cons x (xs'.append ys)).append zs := rfl
        _ = cons x ((xs'.append ys).append zs) := rfl
        _ = cons x (xs'.append (ys.append zs)) := by rw [append_assoc xs' ys zs]
        _ = (cons x xs').append (ys.append zs) := rfl
  -- NOTE: This notation is *much* nicer to read and present with
  theorem append_list_assoc : ∀ (xs ys zs : _root_.List α), (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
    intro xs ys zs
    match xs with
    | [] => rfl
    | x :: xs' =>
      calc  ((x :: xs') ++ ys) ++ zs
        _ = (x :: (xs' ++ ys)) ++ zs := rfl
        _ = x :: ((xs' ++ ys) ++ zs) := rfl
        _ = x :: (xs' ++ (ys ++ zs)) := by rw [append_list_assoc xs' ys zs]
        _ = (x :: xs') ++ (ys ++ zs) := rfl

  @[simp]
  def length (xs : List α) : Nat :=
    match xs with
    | nil => 0
    | cons _ xs' => .succ xs'.length

  -- NOTE: `List.get? : List α → Nat → Option α` with the theorem `∀ (xs : List α) (i : Nat), i < xs.length → xs.get? i ≠ none` might be a good one, too
  def get? (xs : List α) (i : Nat) : Option α :=
    match xs with
    | nil        => none
    | cons x xs' =>
      match i with
      | 0        => x
      | .succ i' => xs'.get? i'
  -- Yeah, this is easy to demonstrate, albeit a little time-consuming
  theorem get_in_bounds : ∀ (xs : List α) (i : Nat), i < xs.length → xs.get? i ≠ none := by
    intro xs i h_i_lt_length_xs
    match xs with
    | nil => contradiction
    | cons x xs' =>
      match i with
      | 0 => simp [get?]
      | .succ i' =>
        rw [get?]
        have : i' < xs'.length := by
          rw [length] at h_i_lt_length_xs
          apply Nat.lt_of_succ_lt_succ
          assumption
        apply get_in_bounds xs' i'
        assumption
  -- NOTE: This proof actually leads to a function with a pretty interesting type signature:
  def get (xs : List α) (i : Nat) : i < xs.length → α :=
    fun h =>
      Option.bazorp (xs.get? i) -- WARNING: I have no fkn clue why I need to define `Option.bazorp` manually
        (fun h' =>
          have := get_in_bounds xs i h
          absurd h' this
        )
        (fun a _ => a)
  #eval (cons 1 (cons 2 nil)).get 0 (by simp)
  -- Using `Option.bazorp` is really giving me the shits.
  -- NOTE: Success, but messy
  def getNoBazorp (xs : List α) (i : Nat) : i < xs.length → α :=
    fun h =>
      let it := xs.get? i -- Assign a **name** to the expression we'll `match` on
      have h_it_ain't_none : it ≠ none := get_in_bounds xs i h -- get useful assumptions about `it` **before** `match`ing it
      match it with -- Upon a `match it with ...`, anything in the current context that involves `it` will have `it` replaced by the results of the pattern-match
      | .none =>
        -- This `match` successfully replaced `it` by `none`,
        --  so now `h_it_ain't_none : none ≠ none`
        by contradiction
      | some x =>
        -- Similarly, `h_it_ain't_none : some x ≠ none`, not that it's useful here
        x
  -- NOTE: Bigger success. Do this.
  --       [5.] we're winning with this one
  def getNoBazorpNoIt (xs : List α) (i : Nat) : i < xs.length → α :=
    fun h_in_bounds =>
      match h_rep : xs.get? i with -- NOTE: This is how you bind the proof of what the thing reduces to into a name `h_rep`
      | none =>
        False.elim (by
          have get_not_none : xs.get? i ≠ .none
            := get_in_bounds xs i h_in_bounds
          contradiction -- with `h_rep : xs.get? i = none`
        )
      | some x => x
end List
end ν



#print List.get?
