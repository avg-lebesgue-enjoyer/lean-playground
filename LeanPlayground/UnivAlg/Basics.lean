/- @file LeanPlayground/UnivAlg/Basics.lean
 - The basic definitions (especially datatypes) behind this theory of universal algebra.
 -/

/- IMPORTS: -/
-- (none)



/- SECTION: Utilities -/

/-- `Vec n α : Type u` is the `n : Nat`-fold iterated product of `α : Type u`. -/
def Vec.{u} : Nat → Type u → Type u
  | 0,       _ => PUnit
  | .succ n, α => α × Vec n α

def makeVecFunctor : (n : Nat) → Functor (Vec n)
  | 0 => { map := fun _ _ => () }
  | .succ n => { map := fun f (a, as) => (f a, (makeVecFunctor n).map f as) }
instance instVecFunctor {n : Nat} : Functor (Vec n) where map := (makeVecFunctor n).map

def List.toVec.{u} {α : Type u} : (xs : List α) → Vec xs.length α
  | [] => PUnit.unit
  | (x :: xs) => (x, xs.toVec)

/--
  Given `xs : List α` and a function `f : {x : α // x ∈ xs} → β` acting on the members of `xs`,
  map `f` over `xs` to produce a `List β`.

  `smap` is short for `s`ubtype `map`.
-/
def List.smap.{u, u'} {α : Type u} {β : Type u'} (xs : List α) (f : {x : α // x ∈ xs} → β) : List β :=
  match xs with
  | [] => []
  | (x :: xs') =>
    have : x ∈ x :: xs' := List.mem_cons_self ..
    f ⟨x, ‹_›⟩ :: xs'.smap (fun ⟨y, h⟩ => f ⟨y, List.mem_cons.mpr (.inr h)⟩)

theorem List.smap_nil.{u, u'}
  {α : Type u} {β : Type u'}
  (f : {x : α // x ∈ []} → β)
  : [].smap f = []
  := rfl
theorem List.smap_cons.{u, u'}
  {α : Type u} {β : Type u'}
  (x : α) (xs : List α)
  (f : {a : α // a ∈ (x :: xs)} → β)
  : (x :: xs).smap f = f ⟨x, List.mem_cons_self ..⟩ :: xs.smap (fun ⟨y, h⟩ => f ⟨y, List.mem_cons.mpr (.inr h)⟩)
  := rfl

theorem List.length_smap.{u, u'}
  {α : Type u} {β : Type u'}
  (xs : List α)
  (f : {x : α // x ∈ xs} → β)
  : (xs.smap f).length = xs.length
  := by
    induction xs
    case nil => rfl
    case cons x xs ih => rw [List.length_cons, List.smap_cons, List.length_cons, ih]

theorem List.mem_smap.{u, u'}
  {α : Type u} {β : Type u'}
  {xs : List α}
  {f : {x : α // x ∈ xs} → β}
  {b : β}
  : b ∈ xs.smap f
  ↔ ∃ (a : { x // x ∈ xs }), f a = b
  := by
    constructor
    case mp =>
      induction xs
      case nil =>
        intro h
        contradiction -- `b ∈ [].smap f` is `b ∈ []` is `False`
      case cons x xs ih =>
        intro h
        rw [List.smap_cons, List.mem_cons] at h
        cases h
        case inl h =>
          have : x ∈ x :: xs := List.mem_cons.mpr (.inl rfl)
          exists ⟨x, ‹_›⟩
          rw [h]
        case inr h =>
          have ⟨⟨a, _⟩, _⟩ := ih h
          have : a ∈ x :: xs := mem_cons.mpr (.inr ‹a ∈ xs›)
          exists ⟨a, ‹_›⟩
    case mpr =>
      intro ⟨⟨x, h_x⟩, h_fx⟩
      induction xs
      case nil =>
        contradiction -- `h_x : x ∈ []`
      case cons y ys ih =>
        have := h_x
        rw [mem_cons] at this
        rw [smap_cons, mem_cons]
        cases this
        case inl h_x' => -- `h_x' : x = y`
          apply Or.inl
          rw [←h_fx]
          have : (⟨x, h_x⟩ : {a // a ∈ y :: ys}) = ⟨y, mem_cons_self y ys⟩ := by
            apply Subtype.eq
            show x = y
            exact ‹x = y›
          rw [this]
        case inr h_x =>
          apply Or.inr
          let f' : { x // x ∈ ys } → β := (fun x => f ⟨x.val, mem_cons.mpr (Or.inr x.property)⟩)
          show b ∈ ys.smap f'
          have := @ih f' h_x
          apply this
          rw [←h_fx]




/- SECTION: Equational classes (but not their models) -- inital definitions and setup -/

/-- A logical operation (function symbol), specified by an `.id` and `.arity`. -/
structure Operation : Type where
  id    : String
  arity : Nat
deriving Repr
@[inherit_doc Operation]
abbrev Op : Type := Operation

/-- A list of elements which return distinct values according to a discriminating function. -/
structure UniqueList.{u, u'} (α : Type u) {β : Type u'} (discriminate : α → β) : Type u where
  list : List α
  uq : ∀ (i j : Fin list.length), i ≠ j → discriminate (list.get i) ≠ discriminate (list.get j)
deriving Repr
@[inherit_doc UniqueList]
abbrev UqList := UniqueList
instance instMemUqList : Membership α (UqList α d) where
  mem uαs a := a ∈ uαs.list

/-- A list of operations, each with unique `.id`s. -/
def Operations : Type := UniqueList Operation Operation.id
deriving Repr
/-- The underlying list of operations. -/
def Operations.list : Operations → List Operation := UniqueList.list
/-- A proof that the operation IDs are distinct. -/
def Operations.uqIds
  : (ops : Operations)
  → (∀ (i j : Fin ops.list.length), i ≠ j → (ops.list.get i).id ≠ (ops.list.get j).id)
  := UniqueList.uq
@[inherit_doc Operations]
abbrev Ops : Type := Operations
instance instCoeOpsListOp : Coe Ops (List Op) where
  coe ops := ops.list
instance instMemOpOps : Membership Op Ops where
  mem ops op := op ∈ ops.list

/-- A list of distinct variable names. -/
def Variables : Type := UniqueList String id
deriving Repr
/-- The underlying list of variable names. -/
def Variables.list : Variables → List String := UniqueList.list
/-- A proof that the variable names are unique. -/
def Variables.uq
  : (vars : Variables)
  → (∀ (i j : Fin vars.list.length), i ≠ j → vars.list.get i ≠ vars.list.get j) := UniqueList.uq
@[inherit_doc Variables]
abbrev Vars : Type := Variables
instance instCoeVarsListString : Coe Vars (List String) where
  coe := Variables.list
instance instMemStringVars : Membership String Vars where
  mem vars string := string ∈ vars.list

-- FIXME: I'm pretty sure that I just need to completely rethink the structure of `Term`s here.
--  It's currently really messy, and hard to reason with in Lean4 (no `Term.brecOn`, so termination proofs
--  are awful).
-- It's a real shame that I can't have `Vec op.arity Term` as part of the `inductive` definition :/
-- I think the way to go is as follows:
--  `inductive Term (ops : Ops) (vars : Vars) : Type where              `
--  ` | var : (name : String) → Term ops vars                           `
--  ` | app : (op : Op) → (args : List (Term ops vars)) → Term ops vars `
--  `def Term.isLegal {ops : Ops} {vars : Vars} : Term ops vars → Prop              `
--  ` | .var name => name ∉ ops.ids ∧ name ∉ vars.ids                               `
--  ` | .app op args => args.length = op.arity ∧ ∀ (t : {t // t ∈ args}), t.val.isLegal `
--   /-- Legal terms. Use these in specifications. -/
--  `def TermL (ops : Ops) (vars : Vars) := { t : Term ops vars // t.isLegal }      `
--  `structure Equation (ops : Ops) (vars : Vars) : Type where`
--  `   lhs : TermL ops vars`
--  `   rhs : TermL ops vars`
--  etc.
/--
  The structure behind a term, but with no guarantee that it makes any sense.
  A term is comprised of `Var`iables with given `String` names, and `App`lications
  of `Operation` symbols to other terms.

  In `App op args`, `op` might not appear in `ops` and `args.length`
  might not be equal to `op.arity`.
  See also `Term`, which consists of only *legal* terms.
  See also `Term'.isLegal`.
-/
inductive Term' (ops : Ops) (vars : Vars) : Type where
  | var : (name : String) → Term' ops vars
  | app : (op : Op) → (args : List (Term' ops vars)) → Term' ops vars
deriving Repr
/-- Specification for whether a given `Term' ops` is legal. -/
def Term'.isLegal (ops : Ops) (vars : Vars) : Term' ops vars → Prop
  | var v       => v ∈ vars
  | app op args => (op ∈ ops) ∧ (args.length = op.arity) ∧ (∀ (a : Term' ops vars), a ∈ args → a.isLegal)
/-- A legal term over a given language `ops : Ops` of operations with variable names found in `vars : Vars`. -/
def Term (ops : Ops) (vars : Vars) : Type := { t : Term' ops vars // t.isLegal }

/-- An equation, consisting of a `Term` on the `lhs` of the equation, and another on its `rhs`. -/
structure Equation (ops : Ops) (vars : Vars) : Type where
  lhs : Term ops vars
  rhs : Term ops vars

/--
  An **equational class** -- a system with a language of function symbols and axioms
  encoded as universally quantified equations among legal composites of these function
  symbols.

  `ops  : Ops`  describes the list of operations in the class.
  `vars : Vars` describes the list of variable names universally quantified over in the list of equations.
  `eqs  : List (Equation ops vars)` is the list of equations to be satisfied in the equational class.
-/
structure EquationalClass : Type where
  ops  : Ops
  vars : Vars
  eqs  : List (Equation ops vars)



/- SECTION: Models of equational classes -/

/--
  Given a `carrier` type and some interpretations `opsInt` of specified `ops : Ops` as genuine operations
  on the `carrier`, interpret a `Term` as a function mapping a choice for the free variables in the `Term`
  to an element of the `carrier`.
-/
noncomputable -- code generator doesn't support `Subtype.recOn` yet :/
def Term.interpret.{u}
  {ops : Ops}
  {vars : Vars}
  (carrier : Type u)
  (opsInt : (op : { o : Op // o ∈ ops }) → (Vec op.val.arity carrier) → carrier)
  (term : Term ops vars)
  (subs : { v : String // v ∈ vars } → carrier)
  : carrier
  := term.recOn <| fun val =>
    match val with
    | .var v => fun p =>
      have : v ∈ vars := by {
        unfold Term'.isLegal at p
        exact p
      }
      subs ⟨v, ‹_›⟩
    | .app op args => fun p =>
      have : op ∈ ops := by {
        unfold Term'.isLegal at p
        exact p.left
      }
      have h_args_legal : ∀ (a : Term' ops vars), a ∈ args → a.isLegal ops vars := by {
        unfold Term'.isLegal at p
        exact p.right.right
      }
      let arg2Term : {a : Term' ops vars // a ∈ args} → Term ops vars :=
        fun a =>
        have : a.val.isLegal ops vars := h_args_legal a.val a.property
        ⟨a, ‹_›⟩
      let legalArgs : List (Term ops vars) := List.smap args arg2Term
      -- FIXME: This is the recursive call that's eating my ass
      let argVals : List carrier := legalArgs.smap (Term.interpret carrier opsInt · subs)
      have : argVals.length = op.arity := by {
        unfold argVals
        rw [List.length_smap]
        unfold legalArgs
        rw [List.length_smap]
        unfold Term'.isLegal at p
        exact p.right.left
      }
      let vecVals : Vec op.arity carrier := (this ▸ argVals.toVec)
      opsInt ⟨op, ‹_›⟩ vecVals
  termination_by term.val
  decreasing_by (repeat sorry)

-- structure Model.{u} (eqc : EquationalClass) where
--   carrier : Type u
--   ops : (op : { o : Op // o ∈ eqc.ops }) → (Vec op.val.arity carrier) → carrier
--   eqs : (eq : { e : Equation eqc.ops eqc.vars // e ∈ eqc.eqs }) → sorry -- FIXME: Codify a statement of the equation
