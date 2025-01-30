/-
  **FILE** `LeanPlayground/Preso/2Programming.lean`
  **PURPOSE** Introduction to programming
-/

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
