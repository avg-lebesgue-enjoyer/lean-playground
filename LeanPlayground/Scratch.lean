/- @file LeanPlayground/Scratch.lean
 - Scratch file for whatever stuff
 -/

/- SECTION: hmm -/
section hmm
  -- hmm
end hmm



/- SECTION: Not hmm -/
section not_hmm

  inductive Thing : Type where
  | itsTrue : Thing
  | itsForall : Thing → Thing

  abbrev Symbol := Nat

  def Symbol.nextSymbol : Symbol → Symbol := (· + 1)

  def Thing.toString' (s : Symbol) : Thing → String × Symbol
    | itsTrue => ("true", s)
    | itsForall p =>
      let (printedP, s') := p.toString' s.nextSymbol
      ( "∀x" ++ s.toSubscriptString ++ ", " ++ printedP
      , s' )
  def Thing.toString : Thing → String := Prod.fst ∘ Thing.toString' 0

  namespace Thing
    #eval itsForall (itsForall itsTrue) |>.toString
  end Thing

  -- .; monadic version?

  inductive Thing' : Type where
  | itsTrue' : Thing'
  | itsForall' : Thing' → Thing'

  #print set
  def Thing'.toString' : Thing' → StateT Symbol Id String
    | itsTrue' => liftM (m := Id) "true"
    | itsForall' p => do
      let s ← get
      set s.nextSymbol
      let printedP ← p.toString'
      pure <| "∀x" ++ s.toSubscriptString ++ ", " ++ printedP

  def Thing'.toString (t : Thing') : String := Prod.fst (Thing'.toString' t 0)

  namespace Thing'
    #eval itsForall' (itsForall' itsTrue') |>.toString
  end Thing'

  -- .; Trees?

  inductive BinTree (α : Type) : Type where
  | leaf : BinTree α
  | node : BinTree α → α → BinTree α → BinTree α

  abbrev IndentationLevel := String
  def IndentationLevel.next : IndentationLevel → IndentationLevel := ("| " ++ ·)

  theorem BinTree.zero_lt_sizeOf (t : BinTree α) : 0 < sizeOf t := by
    induction t
    case leaf =>
      simp_all only [leaf.sizeOf_spec, Nat.lt_add_one]
    case node =>
      simp_all only [node.sizeOf_spec, sizeOf_default, Nat.add_zero]
      rw [Nat.add_assoc, Nat.add_comm 1]
      apply Nat.zero_lt_succ
    -- [done.]

  def BinTree.toString' [ToString α] : BinTree α → StateT IndentationLevel Id String
    | leaf => liftM (m := Id) <| ""
    | node l a r => do
      let i ← getThe IndentationLevel
      set <| i.next
      let printedL ← BinTree.help l
      set <| i.next
      let printedR ← BinTree.help r
      set i
      pure <| i ++ toString a ++ printedL ++ printedR
    termination_by t => sizeOf t
    decreasing_by
      · simp [Nat.add_comm 1]
        apply zero_lt_sizeOf
      · simp [Nat.add_comm _ 1]
        apply zero_lt_sizeOf
    where BinTree.help : BinTree α → StateT IndentationLevel Id String
            | leaf => pure ""
            | n@(node ..) => do
              let printedN ← n.toString'
              pure <| "\n" ++ printedN
          termination_by n => sizeOf n + 1
  def BinTree.toString [ToString α] (t : BinTree α) : String :=
    t.toString' "" |>.fst
  def BinTree.print [ToString α] : BinTree α → IO Unit := IO.println ∘ BinTree.toString

  section yum_yum
    abbrev Yummers : Type := Nat

    def BinTree.eat [ToString α] : BinTree α → StateT IndentationLevel (StateT Yummers Id) String
      | leaf => "" |> liftM (m := Id)
      | node l a r => do
        let i ← getThe IndentationLevel
        set i.next
        let eatenL ← help l
        set i.next
        let eatenR ← help r
        set i
        modifyThe Yummers (· + 1)
        pure <| i ++ ToString.toString a ++ eatenL ++ eatenR
      termination_by t => sizeOf t
      decreasing_by
        · simp [Nat.add_comm 1]
          exact zero_lt_sizeOf ..
        · simp [Nat.add_comm _ 1]
          exact zero_lt_sizeOf ..
      where help : BinTree α → StateT IndentationLevel (StateT Yummers Id) String
            | leaf => pure ""
            | n@(node ..) => do pure <| "\n" ++ (← n.eat)
            termination_by n => sizeOf n + 1
    def BinTree.delicious [ToString α] (t : BinTree α) : IO Unit := do
      IO.println "Eating your tree, yum yum..."
      let ⟨⟨hierarchy, _⟩, numberOfNonLeafNodes⟩ : (String × IndentationLevel) × Yummers := t.eat |>.run "" |>.run 0 |>.run
      IO.println "Tree hierarchy:"
      IO.println hierarchy
      IO.println s!"Number of non-leaf nodes: {numberOfNonLeafNodes}"
  end yum_yum

  namespace BinTree
    def t₀ : BinTree Nat := leaf
    def t₁ : BinTree Nat := node leaf 0 leaf
    def t₂ : BinTree Nat := node t₁ 1 leaf
    def t₃ : BinTree Nat := node t₁ 1 t₁
    def t₄ : BinTree Nat :=
      node
        (node
          (node
            leaf
            0
            (node
              leaf
              1
              leaf))
          2
          (node
            leaf
            3
            leaf))
        4
        (node
          (node
            leaf
            5
            leaf)
          6
          leaf)
    #eval t₀.delicious
    #eval t₁.delicious
    #eval t₂.delicious
    #eval t₃.delicious
    #eval t₄.delicious
  end BinTree
end not_hmm



/- SECTION: Church numerals -/
section church
  variable (It : Type)

  inductive Expr (Name : Type) : Type where
    | var     : Name      → Expr Name
    | lambda  : Name      → Expr Name → Expr Name
    | apply   : Expr Name → Expr Name → Expr Name
  deriving Repr
  export Expr (var lambda)
  namespace Expr
    def toString {Name : Type} [ToString Name] : Expr Name → String
      | var x => ToString.toString x
      | lambda x e => s!"λ{x}. " ++ e.toString
      | apply f e => s!"({f.toString}) ({e.toString})" -- TODO: Parentheses here are fugly
    instance instToString [ToString Name] : ToString (Expr Name) where toString := Expr.toString
    instance instCoeNameExpr : Coe Name (Expr Name) where coe := var
    instance instAddExpr : Add (Expr Name) where add := apply

    def replace {Name : Type} [BEq Name] (source : Expr Name) (me : Name) (target : Expr Name) : Expr Name :=
      match source with
      | var x => if x == me then target else var x
      | lambda x e => lambda x <| if x == me then e else e.replace me target
      | apply e f => apply (e.replace me target) (f.replace me target)

    theorem one_le_sizeOf {Name : Type} : ∀ (e : Expr Name), 1 ≤ sizeOf e := by
      intro e ; cases e
      case var    => simp only [var.sizeOf_spec, sizeOf_default, Nat.add_zero, Nat.le_refl]
      case lambda => simp only [lambda.sizeOf_spec, sizeOf_default, Nat.add_zero, Nat.le_add_right]
      case apply  => simp only [apply.sizeOf_spec, Nat.add_assoc, Nat.le_add_right]

    theorem sizeOf_replace {Name : Type} [BEq Name]
      : ∀ {source target : Expr Name} {me : Name},
        sizeOf (source.replace me target) ≤ sizeOf source * sizeOf target
      := by
        intro source target me
        induction source
        case var x =>
          simp only [replace, var.sizeOf_spec, sizeOf_default, Nat.add_zero]
          split
          case isTrue  => simp only [Nat.one_mul, Nat.le_refl]
          case isFalse => simp only [var.sizeOf_spec, sizeOf_default, Nat.add_zero, Nat.one_mul, one_le_sizeOf]
        case lambda x e ih =>
          simp only [replace, lambda.sizeOf_spec, sizeOf_default, Nat.add_zero]
          have h_lhs : 1 ≤ sizeOf target := one_le_sizeOf ..
          split
          case isTrue =>
            have h_rhs : sizeOf e ≤ sizeOf e * sizeOf target :=
              calc sizeOf e
                _ = sizeOf e * 1 := by rw [Nat.mul_one]
                _ ≤ sizeOf e * sizeOf target := by apply Nat.mul_le_mul_left ; exact one_le_sizeOf ..
            simp only [Nat.add_mul, Nat.one_mul, h_lhs, h_rhs, Nat.add_le_add]
          case isFalse =>
            simp only [Nat.add_mul, Nat.one_mul, h_lhs, ih, Nat.add_le_add]
        case apply e f e_ih f_ih =>
          simp only [replace, apply.sizeOf_spec]
          admit

    -- Might not terminate... e.g. Y combinator
    partial def betaReduce {Name : Type} [BEq Name] : Expr Name → Expr Name
      | var x => var x
      | lambda x e => lambda x e.betaReduce
      | apply (lambda x e) f => e.replace x f |>.betaReduce
      | apply e f => apply e.betaReduce f.betaReduce

    #eval (lambda "x" "x" + "y" : Expr String).betaReduce
  end Expr

  def church : Nat → Expr String
    | 0 => lambda "f" (lambda "x" "x")
    | n + 1 => lambda "f" (lambda "x" ("f" + (church n + "f" + "x")))

  #eval (church 1).betaReduce.toString
end church



/- SECTION: Permutation -/
section perm
  def List.count' [BEq α] : List α → α → Nat
    | [], _ => 0
    | (a :: as), b => (if a == b then 1 else 0) + as.count' b

  def List.has [BEq α] (as : List α) (a : α) : Prop :=
    as.count' a ≠ 0

  def List.findElementIndex? [BEq α] (a : α) : List α → Option Nat
    | [] => none
    | (b :: as) => if a == b then some 0 else (1 + ·) <$> as.findElementIndex? a

  theorem List.findElementIndex_ne_none_of_has [BEq α] [law : LawfulBEq α] (a : α) (as : List α) (h : as.has a) : as.findElementIndex? a ≠ none := by
    induction as
    case nil => contradiction
    case cons b bs ih =>
      unfold has count' at h
      split at h
      case isTrue h h' =>
        have : (a == b) = true := by simp_all only [ne_eq, beq_iff_eq, Nat.add_eq_zero_iff,
          Nat.add_one_ne_zero, false_and, not_false_eq_true, beq_self_eq_true]
        unfold List.findElementIndex?
        simp only [this, ↓reduceIte, ne_eq, reduceCtorEq, not_false_eq_true]
      case isFalse h h' =>
        simp at h
        have h : bs.has a := h
        have h' : ¬ (a == b) = true := by simp_all only [ne_eq, beq_iff_eq, Nat.zero_add] ; rw [Eq.comm] ; assumption
        unfold List.findElementIndex?
        simp only [ne_eq] at ih
        simp only [h', Bool.false_eq_true, ↓reduceIte, Option.map_eq_map, ne_eq,
          Option.map_eq_none', h, ih, not_false_eq_true]

  def List.findElementIndex [BEq α] [LawfulBEq α] (a : α) (as : List α) (h : as.has a) : Nat :=
    match h_rep: as.findElementIndex? a with
    | some i => i
    | none => as.findElementIndex_ne_none_of_has a h h_rep |>.elim

end perm



/- SECTION: Funny dice game -/
section funny_dice_game
  -- NOTE: The optimal strategy here is deterministic

  def List._1to6 : List Nat := [1, 2, 3, 4, 5, 6]

  def List.minDistanceTo? (oracle : Float) (as : List Nat) : Option Nat := do
    let oas := as.map (Float.abs ∘ (· - oracle) ∘ Nat.toFloat)
    as.get? (← oas.findElementIndex? (← oas.min?))

  def lFrom𝔼Yn (𝔼Yn : Float) : Option Nat :=
    List._1to6.minDistanceTo? (𝔼Yn + 1/2)

  def 𝔼Y : Nat → Option Float
    | 0 => none
    | 1 => some 3.5
    | n + 1 => do
      let 𝔼Yn ← 𝔼Y n
      let lₙ := (← lFrom𝔼Yn 𝔼Yn).toFloat
      pure <| (21 - 𝔼Yn) / 6 + (1 + 2 * 𝔼Yn) / 12 * lₙ - 1/12 * lₙ^2

  #eval 𝔼Y 100
end funny_dice_game



/- SECTION: Funny verification -/
section funny_verification
  /--
    `xs.isPermutation as` returns `true` just when `xs` is a permutation of `as`, as decided by the
    `[BEq α]` instance.
  -/
  def List.isPermutation [BEq α] (xs : List α) : List α → Bool
    | [] => xs.isEmpty
    | (a :: as) => (xs.contains a) && ((xs.erase a).isPermutation as)

  theorem List.count_ne_zero_of_mem
    [BEq α] [LawfulBEq α]
    {a : α} {as : List α}
    (h : a ∈ as)
    : as.count a ≠ 0
    := by
      induction as
      case nil => contradiction
      case cons x xs ih =>
        simp_all only [ne_eq, mem_cons, count_cons, beq_iff_eq, Nat.add_eq_zero_iff,
          ite_eq_right_iff, Nat.add_one_ne_zero, imp_false, not_and, Classical.not_not]
        intro h_count_eq_0
        cases h
        case inl h => simp only [h]
        case inr h =>
          have := ih h
          contradiction

  theorem Nat.one_le_iff : ∀ (x : Nat), 1 ≤ x ↔ x ≠ 0 := by
    intro x
    constructor <;> intro h
    · intro h_x_eq_0
      rw [‹x = 0›] at h
      contradiction
    · have ⟨x', _⟩ : ∃x', x = succ x' := by
        simp_all only [ne_eq, succ_eq_add_one, exists_eq_add_one, not_false_eq_true,
          zero_lt_of_ne_zero]
      simp only [‹x = succ x'›, succ_eq_add_one, le_add_left]

  theorem List.isPermutation_correct [BEq α] [LawfulBEq α]
    : ∀ {xs as : List α},
      xs.isPermutation as
      → ∀ (z : α),
        xs.count z = as.count z
    := by
      intro xs as
      revert xs
      induction as
      case nil =>
        intro xs h_isPermutation z
        have : xs = [] := by simp_all only [isPermutation, isEmpty_eq_true]
        show count z xs = count z []
        rw [this]
      case cons a as ih =>
        intro xs h_isPermutation z
        have ⟨_, h_erase_isPermutation⟩: a ∈ xs ∧ (xs.erase a).isPermutation as = true := by
          simp_all only [isPermutation, elem_eq_mem, Bool.and_eq_true, decide_eq_true_eq, and_self]
        have : ∀ (z : α), count z (xs.erase a) = count z as :=
          ih h_erase_isPermutation
        simp only [count_cons, beq_iff_eq]
        simp only [count_erase, beq_iff_eq] at this
        rw [←this]
        cases h : a == z
        case true =>
          have h : a = z := by simp_all only [beq_iff_eq]
          simp only [↓reduceIte]
          have this := this z
          have := count_ne_zero_of_mem ‹a ∈ xs›
          rw [h] at this
          rw [Nat.sub_add_cancel]
          simp_all only [beq_iff_eq, beq_self_eq_true, ite_true, ne_eq, Nat.one_le_iff,
            not_false_eq_true]
        case false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, Nat.add_zero]
      -- [done.]

end funny_verification



/- SECTION: Polymorphic naturality -/
section «poly nat» namespace «poly nat» -- [hide:]

def natural
  {F G : Type → Type} [Functor F] [Functor G]
  (η : (α : Type) → F α → G α)
  : Prop
:=
  ∀ {α β : Type}, ∀ (f : α → β),
    η β ∘ Functor.map f = Functor.map f ∘ η α

instance i₂ {ε : Type} : Functor (ε × ·) where
  map f | (e, a) => (e, f a)
instance i₁ {ε : Type} : Functor (· × ε) where
  map f | (a, e) => (f a, e)

example
  : let s {ε : Type} : (α : Type) → ε × α → α × ε :=
      fun _ (e, a) => (a, e)
    ; ∀ {ε : Type}, natural (s (ε := ε))
  := by
    intro s ε
    unfold natural
    intro α β f
    funext (e, a)
    unfold Function.comp
    rfl
    -- [done.]

open Classical in
noncomputable def f (α : Type) (a : α) : α :=
  if h : α = Nat then
    (h ▸ 69)
  else
    a

-- NOTE: Not all polymorphic functions `: (α : Type) → α → α` are `id`.
example : f Nat 0 ≠ 0 := by
  unfold f
  simp only [↓reduceDIte, ne_eq, Nat.add_one_ne_zero, not_false_eq_true]
  -- [done.]

-- NOTE: Rules for "polymorphic functions" over one type:
--  Has type `{α : Type} → F α → G α` for some fixed functors `F`, `G`.
--  `F α` and `G α` are both `inductive` types, and hence are initial algebras
--    of **polynomial** endofunctors.
--  Built up from the following operations:
--    `πᵢ : α × ⋯ × α → fun {α}

open Classical in
inductive F (α : Type) where
  | it : (if α = Nat then Unit else Unit × Unit) → F α

#print F

end «poly nat» end «poly nat» -- [hide:]



/- SECTION: Fuzzy matching -/
section «fuzzy matching» -- [hide:]
namespace «fuzzy matching»

  def doAll (actions : List (α → Option α)) (a : α) : Option α :=
    match actions with
    | [] =>
      pure a
    | (action :: actions) => do
      doAll actions (← action a)

  def skipJustPast [BEq α] (me : α) : List α → Option (List α)
    | []        => none
    | (a :: as) => if a == me then as else skipJustPast me as

  def skipAll [BEq α] (these : List α) : List α → Option (List α) :=
    doAll (these.map skipJustPast)

  /-- Check whether the `haystack` contains the `needle` as a subsequence -/
  def _root_.List.fuzzyHas [BEq α] (haystack needle : List α) : Bool :=
    skipAll needle haystack |>.isSome

  /-- Check whether the `haystack` contains the `needle` as a subsequence -/
  def _root_.String.fuzzyHas (haystack needle : String) : Bool :=
    haystack.toList.fuzzyHas needle.toList

  /-- Forget data about a string to make it more amenable to fuzzy matching -/
  def _root_.String.forget (s : String) : String :=
          s |>.toList |>.filter Char.isAlphanum |>.map Char.toLower |>.asString

  /-- Check whether the `haystack` contains the `needle` as a subsequence,
      after forgetting data about each according to `String.forget`
  -/
  def _root_.String.looselyHas (haystack needle : String) : Bool :=
    haystack.forget.fuzzyHas needle.forget

end «fuzzy matching»

namespace «fuzzy matching examples»

  #eval "Amogus sus".fuzzyHas "Amogus"
  #eval "amogus sus".fuzzyHas "ogsu"
  #eval "Amogus sus".looselyHas "am Su"
  #eval "Right Adjoints Preserve Limits".looselyHas "rapl"
  #eval "Yoneda lemma".looselyHas "rapl"
  #eval "Yoneda-style arguments".looselyHas "yondus"

end «fuzzy matching examples»


end «fuzzy matching» -- [hide:]
