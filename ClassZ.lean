module

public import ClassEx
public import MHRank

@[expose] public section

/-!
# A finite theory of classes whose sets satisfy `𝗭𝗖` and the rank axioms

`thetaZ` is one sentence of `ℒₛₑₜ`, read in a structure of classes (`ClassEx.lean`):

* some element is a set, there is a universal class, a class included in a set is a set, and
  twelve instances of comprehension by a bounded condition `Φ` with class parameters
  (`CompAx Φ`: for a universal class `U` the class `{x ∈ U | Φ}` exists);
* the axioms of `𝗕𝗦𝗧` other than equality and the axiom of choice, with their quantifiers
  restricted to the sets (`relS`).

**`sets_models_zc`**: in every structure that satisfies `thetaZ`, the sets satisfy `𝗭𝗖`. The
separation schema comes from `fullsep_sets`.

`chiU` is a formula of three variables `d'`, `d`, `z`: "`z` is empty, `d'` is the successor of
`d`, they are sets, and among the sets the hierarchy of the iterated power sets of `ω` reaches
the level `d` (as in the rank axiom, with `d` in the place of the numeral)".
**`hasRank_sets`**: if it holds along a sequence `d 0, d 1, …`, the sets satisfy every rank
axiom.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### Restricting the quantifiers to a definable part -/

/-- The formula with its quantifiers restricted to `δ`. -/
def relD (δ : Semiformula ℒₛₑₜ Empty 1) :
    {n : ℕ} → Semiformula ℒₛₑₜ Empty n → Semiformula ℒₛₑₜ Empty n
  | _, .rel r v => .rel r v
  | _, .nrel r v => .nrel r v
  | _, ⊤ => ⊤
  | _, ⊥ => ⊥
  | _, φ ⋏ ψ => relD δ φ ⋏ relD δ ψ
  | _, φ ⋎ ψ => relD δ φ ⋎ relD δ ψ
  | n, ∀¹ φ => ∀¹ ((∼(Rew.subst (![#0] : Fin 1 → Semiterm ℒₛₑₜ Empty (n + 1)) ▹ δ)) ⋎ relD δ φ)
  | n, ∃¹ φ => ∃¹ ((Rew.subst (![#0] : Fin 1 → Semiterm ℒₛₑₜ Empty (n + 1)) ▹ δ) ⋏ relD δ φ)

theorem eval_relD {M : Type} [SetStructure M] (U : Set M) (δ : Semiformula ℒₛₑₜ Empty 1)
    (hδ : ∀ x : M, Eval (M := M) ![x] Empty.elim δ ↔ x ∈ U) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (e : Fin n → U),
      Eval (M := M) (fun i ↦ (e i : M)) Empty.elim (relD δ φ) ↔
        Eval (M := U) e Empty.elim φ := by
  have hsub : ∀ {n : ℕ} (x : M) (v : Fin n → M),
      Eval (M := M) (x :> v) Empty.elim
        (Rew.subst (![#0] : Fin 1 → Semiterm ℒₛₑₜ Empty (n + 1)) ▹ δ) ↔ x ∈ U := by
    intro n x v
    rw [eval_substs]
    have e1 : (Semiterm.val (M := M) (x :> v) Empty.elim ∘
        (![#0] : Fin 1 → Semiterm ℒₛₑₜ Empty (n + 1))) = ![x] := by
      funext i
      fin_cases i
      rfl
    rw [e1]
    exact hδ x
  have hc : ∀ {n : ℕ} (x : U) (e : Fin n → U),
      (fun i ↦ (((x :> e) i : U) : M)) = ((x : M) :> fun i ↦ (e i : M)) := by
    intro n x e; funext i; cases i using Fin.cases <;> rfl
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e; exact Iff.rfl
  | hfalsum => intro e; exact Iff.rfl
  | hrel r v =>
    intro e
    cases r with
    | eq =>
      show (v 0).val (M := M) _ _ = (v 1).val (M := M) _ _ ↔
        (v 0).val (M := U) e _ = (v 1).val (M := U) e _
      rw [tix_val, tix_val, tix_val, tix_val]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    | mem =>
      show (v 0).val (M := M) _ _ ∈ (v 1).val (M := M) _ _ ↔
        (v 0).val (M := U) e _ ∈ (v 1).val (M := U) e _
      rw [tix_val, tix_val, tix_val, tix_val]
      exact Iff.rfl
  | hnrel r v =>
    intro e
    cases r with
    | eq =>
      show ¬(v 0).val (M := M) _ _ = (v 1).val (M := M) _ _ ↔
        ¬(v 0).val (M := U) e _ = (v 1).val (M := U) e _
      rw [tix_val, tix_val, tix_val, tix_val]
      exact not_congr ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    | mem =>
      show ¬(v 0).val (M := M) _ _ ∈ (v 1).val (M := M) _ _ ↔
        ¬(v 0).val (M := U) e _ ∈ (v 1).val (M := U) e _
      rw [tix_val, tix_val, tix_val, tix_val]
      exact Iff.rfl
  | hand φ ψ ih1 ih2 => intro e; exact and_congr (ih1 e) (ih2 e)
  | hor φ ψ ih1 ih2 => intro e; exact or_congr (ih1 e) (ih2 e)
  | @hall n φ ih =>
    intro e
    have key : ∀ x : M, Eval (M := M) (x :> fun i ↦ (e i : M)) Empty.elim
        ((∼(Rew.subst (![#0] : Fin 1 → Semiterm ℒₛₑₜ Empty (n + 1)) ▹ δ)) ⋎ relD δ φ) ↔
        (x ∈ U → Eval (M := M) (x :> fun i ↦ (e i : M)) Empty.elim (relD δ φ)) := by
      intro x
      simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq,
        LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
      rw [hsub]
      exact ⟨fun h hx => h.resolve_left (not_not.mpr hx), fun h => by
        by_cases hx : x ∈ U
        · exact Or.inr (h hx)
        · exact Or.inl hx⟩
    constructor
    · intro h x
      have h1 := (key x.1).mp (h x.1) x.2
      rw [← hc x e] at h1
      exact (ih _).mp h1
    · intro h x
      refine (key x).mpr fun hx => ?_
      have h1 := (ih _).mpr (h ⟨x, hx⟩)
      rw [hc ⟨x, hx⟩ e] at h1
      exact h1
  | @hexs n φ ih =>
    intro e
    have key : ∀ x : M, Eval (M := M) (x :> fun i ↦ (e i : M)) Empty.elim
        ((Rew.subst (![#0] : Fin 1 → Semiterm ℒₛₑₜ Empty (n + 1)) ▹ δ) ⋏ relD δ φ) ↔
        (x ∈ U ∧ Eval (M := M) (x :> fun i ↦ (e i : M)) Empty.elim (relD δ φ)) := by
      intro x
      simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
      rw [hsub]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨hxU, h1⟩ := (key x).mp hx
      rw [← hc ⟨x, hxU⟩ e] at h1
      exact ⟨⟨x, hxU⟩, (ih _).mp h1⟩
    · rintro ⟨x, hx⟩
      have h1 := (ih _).mpr hx
      rw [hc x e] at h1
      exact ⟨x.1, (key x.1).mpr ⟨x.2, h1⟩⟩

def isSetU : UDef (k := 1) (fun V _ v ↦ IsSet (v 0)) :=
  (UDef.ex (UDef.mem 1 0)).congr fun _ _ _ => Iff.rfl

/-- The formula with its quantifiers restricted to the sets. -/
def relS {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) : Semiformula ℒₛₑₜ Empty n := relD isSetU.φ φ

theorem eval_relS {M : Type} [SetStructure M] {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n)
    (e : Fin n → SetsOf M) :
    Eval (M := M) (fun i ↦ (e i : M)) Empty.elim (relS φ) ↔
      Eval (M := SetsOf M) e Empty.elim φ :=
  eval_relD (SetsOf M) isSetU.φ (fun x => isSetU.eval M ![x]) φ e

theorem eval_relS0 {M : Type} [SetStructure M] (φ : Semiformula ℒₛₑₜ Empty 0) :
    Eval (M := M) ![] Empty.elim (relS φ) ↔ Eval (M := SetsOf M) ![] Empty.elim φ := by
  have e1 : (fun i ↦ (((![] : Fin 0 → SetsOf M) i : SetsOf M) : M)) = ![] := by
    funext i; exact i.elim0
  have := eval_relS φ (![] : Fin 0 → SetsOf M)
  rw [e1] at this
  exact this

/-- The conjunction of a list of sentences. -/
def conjL : List (Semiformula ℒₛₑₜ Empty 0) → Semiformula ℒₛₑₜ Empty 0
  | [] => ⊤
  | φ :: l => φ ⋏ conjL l

theorem eval_conjL {M : Type} [SetStructure M] : ∀ l : List (Semiformula ℒₛₑₜ Empty 0),
    Eval (M := M) ![] Empty.elim (conjL l) ↔ ∀ φ ∈ l, Eval (M := M) ![] Empty.elim φ
  | [] => ⟨fun _ φ hφ => absurd hφ (by simp), fun _ => trivial⟩
  | φ :: l => by
    show (Eval (M := M) ![] Empty.elim φ ∧ Eval (M := M) ![] Empty.elim (conjL l)) ↔ _
    rw [eval_conjL l]
    constructor
    · rintro ⟨h1, h2⟩ ψ hψ
      rcases List.mem_cons.mp hψ with rfl | h
      · exact h1
      · exact h2 ψ h
    · intro h
      exact ⟨h φ (by simp), fun ψ hψ => h ψ (List.mem_cons_of_mem _ hψ)⟩

/-! ### The axioms about the sets -/

/-- The axioms of `𝗕𝗦𝗧` other than equality, and the axiom of choice. -/
def bstL : List (Sentence ℒₛₑₜ) :=
  [“∃ e, !isEmpty e”,
   “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”,
   “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”,
   “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”,
   “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”,
   “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”,
   “∀ x, !isNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y”,
   Axiom.choice]

theorem bst_cases (φ : Sentence ℒₛₑₜ) (h : φ ∈ (𝗕𝗦𝗧 : SetTheory)) :
    φ ∈ (𝗘𝗤 ℒₛₑₜ : SetTheory) ∨ φ ∈ bstL := by
  cases h with
  | equality φ h => exact Or.inl h
  | empty_set => right; simp [bstL]
  | extensionality => right; simp [bstL]
  | pairing => right; simp [bstL]
  | union => right; simp [bstL]
  | power_set => right; simp [bstL]
  | infinity => right; simp [bstL]
  | foundation => right; simp [bstL]

/-- The axioms about the sets, as one sentence about the classes. -/
def thetaSet : Semiformula ℒₛₑₜ Empty 0 := conjL (bstL.map relS)

theorem eval_thetaSet {M : Type} [SetStructure M] :
    Eval (M := M) ![] Empty.elim thetaSet ↔
      ∀ φ ∈ bstL, Eval (M := SetsOf M) ![] Empty.elim φ := by
  unfold thetaSet
  rw [eval_conjL]
  constructor
  · intro h φ hφ
    exact (eval_relS0 φ).mp (h _ (List.mem_map.mpr ⟨φ, hφ, rfl⟩))
  · intro h ψ hψ
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hψ
    exact (eval_relS0 φ).mpr (h φ hφ)

/-! ### The axioms about the classes -/

section clsdefs

variable {V : Type} [SetStructure V]

/-- `U` is the class of all sets. -/
def IsUniv (U : V) : Prop := ∀ x, x ∈ U ↔ IsSet x

/-- **Comprehension for the bounded condition `Φ`**, with a universal class and three more
parameters. -/
def CompAx (Φ : Rel5) (V : Type) [SetStructure V] : Prop :=
  ∀ U : V, IsUniv U → ∀ C D a : V, ∃ E : V, ∀ x, x ∈ E ↔ (x ∈ U ∧ Φ V x U C D a)

/-- A class included in a set is a set. -/
def SubSP (V : Type) [SetStructure V] : Prop :=
  ∀ D a : V, IsSet a → ((∀ z, z ∈ D → z ∈ a) → IsSet D)

end clsdefs

def PhiCompl : Rel5 := fun _ _ x _ C _ _ ↦ ¬x ∈ C

def PhiInter : Rel5 := fun _ _ x _ C D _ ↦ x ∈ C ∧ x ∈ D

def PhiUnion : Rel5 := fun _ _ x _ C D _ ↦ x ∈ C ∨ x ∈ D

def PhiDom : Rel5 := fun _ _ x _ C _ _ ↦
  ∃ p, p ∈ C ∧ ∃ u, u ∈ p ∧ ∃ b, b ∈ u ∧ IsOp p b x

def PhiAll : Rel5 := fun _ _ x U C _ _ ↦ ∀ b, b ∈ U → ∃ p, p ∈ C ∧ IsOp p b x

def PhiW : Rel5 := fun _ _ x _ C _ _ ↦
  ∃ ℓ, ℓ ∈ C ∧ ∃ u, u ∈ x ∧ ∃ b, b ∈ u ∧ IsOp x b ℓ

def PhiW1 : Rel5 := fun _ _ x _ C _ _ ↦
  ∃ r, r ∈ C ∧ ∃ u, u ∈ x ∧ ∃ b, b ∈ u ∧ ∃ q, q ∈ u ∧ ∃ u', u' ∈ q ∧ ∃ z, z ∈ u' ∧
    ∃ ℓ, ℓ ∈ u' ∧ (IsOp q z ℓ ∧ (IsOp x b q ∧ IsOp r b ℓ))

def PhiE01 : Rel5 := fun _ _ x _ _ _ _ ↦
  ∃ u, u ∈ x ∧ ∃ b, b ∈ u ∧ ∃ q, q ∈ u ∧ ∃ u', u' ∈ q ∧ ∃ y, y ∈ u' ∧
    ∃ ℓ, ℓ ∈ u' ∧ (IsOp q y ℓ ∧ (IsOp x b q ∧ b ∈ y))

def PhiE10 : Rel5 := fun _ _ x _ _ _ _ ↦
  ∃ u, u ∈ x ∧ ∃ b, b ∈ u ∧ ∃ q, q ∈ u ∧ ∃ u', u' ∈ q ∧ ∃ y, y ∈ u' ∧
    ∃ ℓ, ℓ ∈ u' ∧ (IsOp q y ℓ ∧ (IsOp x b q ∧ y ∈ b))

def PhiE00 : Rel5 := fun _ _ x _ _ _ _ ↦
  ∃ u, u ∈ x ∧ ∃ b, b ∈ u ∧ ∃ ℓ, ℓ ∈ u ∧ (IsOp x b ℓ ∧ b ∈ b)

def PhiI01 : Rel5 := fun _ _ x _ _ _ _ ↦
  ∃ u, u ∈ x ∧ ∃ b, b ∈ u ∧ ∃ q, q ∈ u ∧ ∃ u', u' ∈ q ∧ ∃ ℓ, ℓ ∈ u' ∧
    (IsOp q b ℓ ∧ IsOp x b q)

def PhiSec : Rel5 := fun _ _ x _ C D a ↦ x ∈ a ∧ ∃ p, p ∈ C ∧ IsOp p x D

def phiComplB : BDef (k := 5) (fun V _ v ↦ PhiCompl V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.mem 0 2).not.congr fun _ _ _ => Iff.rfl

def phiInterB : BDef (k := 5) (fun V _ v ↦ PhiInter V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((BDef.mem 0 2).and (BDef.mem 0 3)).congr fun _ _ _ => Iff.rfl

def phiUnionB : BDef (k := 5) (fun V _ v ↦ PhiUnion V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((BDef.mem 0 2).or (BDef.mem 0 3)).congr fun _ _ _ => Iff.rfl

def phiDomB : BDef (k := 5) (fun V _ v ↦ PhiDom V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 2 (BDef.bex 0 (BDef.bex 0 (isOpB.comp ![2, 0, 3])))).congr fun _ _ _ => Iff.rfl

def phiAllB : BDef (k := 5) (fun V _ v ↦ PhiAll V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.ball 1 (BDef.bex 3 (isOpB.comp ![0, 1, 2]))).congr fun _ _ _ => Iff.rfl

def phiWB : BDef (k := 5) (fun V _ v ↦ PhiW V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 2 (BDef.bex 1 (BDef.bex 0 (isOpB.comp ![3, 0, 2])))).congr fun _ _ _ => Iff.rfl

def phiW1B : BDef (k := 5) (fun V _ v ↦ PhiW1 V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 2 (BDef.bex 1 (BDef.bex 0 (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 (BDef.bex 1
    ((isOpB.comp ![3, 1, 0]).and ((isOpB.comp ![7, 4, 3]).and
      (isOpB.comp ![6, 4, 0])))))))))).congr fun _ _ _ => Iff.rfl

def phiE01B : BDef (k := 5) (fun V _ v ↦ PhiE01 V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 (BDef.bex 1
    ((isOpB.comp ![3, 1, 0]).and ((isOpB.comp ![6, 4, 3]).and
      (BDef.mem 4 1))))))))).congr fun _ _ _ => Iff.rfl

def phiE10B : BDef (k := 5) (fun V _ v ↦ PhiE10 V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 1 (BDef.bex 0 (BDef.bex 0 (BDef.bex 1
    ((isOpB.comp ![3, 1, 0]).and ((isOpB.comp ![6, 4, 3]).and
      (BDef.mem 1 4))))))))).congr fun _ _ _ => Iff.rfl

def phiE00B : BDef (k := 5) (fun V _ v ↦ PhiE00 V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 1 ((isOpB.comp ![3, 1, 0]).and
    (BDef.mem 1 1))))).congr fun _ _ _ => Iff.rfl

def phiI01B : BDef (k := 5) (fun V _ v ↦ PhiI01 V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 1 (BDef.bex 0 (BDef.bex 0
    ((isOpB.comp ![2, 3, 0]).and (isOpB.comp ![5, 3, 2]))))))).congr fun _ _ _ => Iff.rfl

def phiSecB : BDef (k := 5) (fun V _ v ↦ PhiSec V (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  ((BDef.mem 0 4).and (BDef.bex 2 (isOpB.comp ![0, 1, 4]))).congr fun _ _ _ => Iff.rfl

def isUnivU : UDef (k := 1) (fun V _ v ↦ IsUniv (v 0)) :=
  (UDef.all ((UDef.mem 0 1).iff (isSetU.comp ![0]))).congr fun _ _ _ => Iff.rfl

def compU {Φ : Rel5} (d : BDef (k := 5) (fun V _ v ↦ Φ V (v 0) (v 1) (v 2) (v 3) (v 4))) :
    UDef (k := 0) (fun V _ _ ↦ CompAx Φ V) :=
  (UDef.all ((isUnivU.comp ![0]).imp (UDef.all (UDef.all (UDef.all (UDef.ex (UDef.all
    ((UDef.mem 0 1).iff ((UDef.mem 0 5).and
      ((UDef.ofB d).comp ![0, 5, 4, 3, 2])))))))))).congr fun _ _ _ => Iff.rfl

def subSU : UDef (k := 0) (fun V _ _ ↦ SubSP V) :=
  (UDef.all (UDef.all ((isSetU.comp ![0]).imp ((UDef.all ((UDef.mem 0 2).imp
    (UDef.mem 0 1))).imp (isSetU.comp ![1]))))).congr fun _ _ _ => Iff.rfl

/-- **The axioms about the classes.** -/
def ClsAx (V : Type) [SetStructure V] : Prop :=
  (∃ x : V, IsSet x) ∧ ((∃ U : V, IsUniv U) ∧ (SubSP V ∧ (CompAx PhiCompl V ∧
    (CompAx PhiInter V ∧ (CompAx PhiUnion V ∧ (CompAx PhiDom V ∧ (CompAx PhiAll V ∧
    (CompAx PhiW V ∧ (CompAx PhiW1 V ∧ (CompAx PhiE01 V ∧ (CompAx PhiE10 V ∧
    (CompAx PhiE00 V ∧ (CompAx PhiI01 V ∧ CompAx PhiSec V)))))))))))))

def clsU : UDef (k := 0) (fun V _ _ ↦ ClsAx V) :=
  ((UDef.ex (isSetU.comp ![0])).and ((UDef.ex (isUnivU.comp ![0])).and (subSU.and
    ((compU phiComplB).and ((compU phiInterB).and ((compU phiUnionB).and ((compU phiDomB).and
    ((compU phiAllB).and ((compU phiWB).and ((compU phiW1B).and ((compU phiE01B).and
    ((compU phiE10B).and ((compU phiE00B).and ((compU phiI01B).and
      (compU phiSecB))))))))))))))).congr fun _ _ _ => Iff.rfl

/-- **The theory of classes, as one sentence.** -/
def thetaZ : Semiformula ℒₛₑₜ Empty 0 := clsU.φ ⋏ thetaSet

theorem eval_thetaZ {M : Type} [SetStructure M] :
    Eval (M := M) ![] Empty.elim thetaZ ↔
      (ClsAx M ∧ ∀ φ ∈ bstL, Eval (M := SetsOf M) ![] Empty.elim φ) := by
  show (Eval (M := M) ![] Empty.elim clsU.φ ∧ Eval (M := M) ![] Empty.elim thetaSet) ↔ _
  rw [eval_thetaSet]
  exact and_congr_left fun _ => clsU.eval M ![]

/-! ### From the axioms to the closure conditions -/

section derive

variable {M : Type} [SetStructure M]

theorem isOp_up {p a b : M} (h : IsOp p a b) : ∃ d, d ∈ p ∧ (a ∈ d ∧ b ∈ d) := by
  obtain ⟨-, ⟨d, hd, hdab⟩, -⟩ := h
  exact ⟨d, hd, hdab.1, hdab.2.1⟩

/-- **The axioms about the classes give the closure conditions**, if the pairs of sets are
sets. -/
theorem classOK_of (hc : ClsAx M)
    (hpair : ∀ x y : M, IsSet x → IsSet y → ∃ p, IsSet p ∧ IsOp p x y) : ClassOK M := by
  obtain ⟨-, ⟨U, hU⟩, hsub, cCompl, cInter, cUnion, cDom, cAll, cW, cW1, cE01, cE10, cE00,
    cI01, cSec⟩ := hc
  have hUm : ∀ {x C : M}, x ∈ C → x ∈ U := fun {x C} h => (hU x).mpr ⟨C, h⟩
  refine ⟨⟨U, hU⟩, fun C => ?_, fun C D => ?_, fun C D => ?_, fun C => ?_, fun C => ?_,
    fun C => ?_, fun C => ?_, ?_, ?_, ?_, ?_, fun C ℓ₀ a => ?_, hsub, hpair⟩
  · obtain ⟨E, hE⟩ := cCompl U hU C U U
    exact ⟨E, fun x => (hE x).trans (and_congr_left fun _ => hU x)⟩
  · obtain ⟨E, hE⟩ := cInter U hU C D U
    exact ⟨E, fun x => (hE x).trans ⟨fun h => h.2, fun h => ⟨hUm h.1, h⟩⟩⟩
  · obtain ⟨E, hE⟩ := cUnion U hU C D U
    exact ⟨E, fun x => (hE x).trans ⟨fun h => h.2, fun h => ⟨h.elim hUm hUm, h⟩⟩⟩
  · obtain ⟨E, hE⟩ := cDom U hU C U U
    refine ⟨E, fun ℓ => (hE ℓ).trans (and_congr (hU ℓ) ?_)⟩
    constructor
    · rintro ⟨p, hp, u, -, b, -, hop⟩
      exact ⟨b, p, hop, hp⟩
    · rintro ⟨a, p, hop, hp⟩
      obtain ⟨d, hd, had, -⟩ := isOp_up hop
      exact ⟨p, hp, d, hd, a, had, hop⟩
  · obtain ⟨E, hE⟩ := cAll U hU C U U
    refine ⟨E, fun ℓ => (hE ℓ).trans (and_congr (hU ℓ) ?_)⟩
    constructor
    · intro h a ha
      obtain ⟨p, hp, hop⟩ := h a ((hU a).mpr ha)
      exact ⟨p, hop, hp⟩
    · intro h b hb
      obtain ⟨p, hop, hp⟩ := h b ((hU b).mp hb)
      exact ⟨p, hp, hop⟩
  · obtain ⟨E, hE⟩ := cW U hU C U U
    refine ⟨E, fun p => (hE p).trans (and_congr (hU p) ?_)⟩
    constructor
    · rintro ⟨ℓ, hℓ, u, -, b, -, hop⟩
      exact ⟨b, ℓ, hop, hℓ⟩
    · rintro ⟨a, ℓ, hop, hℓ⟩
      obtain ⟨d, hd, had, -⟩ := isOp_up hop
      exact ⟨ℓ, hℓ, d, hd, a, had, hop⟩
  · obtain ⟨E, hE⟩ := cW1 U hU C U U
    refine ⟨E, fun p => (hE p).trans (and_congr (hU p) ?_)⟩
    constructor
    · rintro ⟨r, hr, u, -, b, -, q, -, u', -, z, -, ℓ, -, hq, hp, hrop⟩
      exact ⟨b, z, ℓ, q, r, hq, hp, hrop, hr⟩
    · rintro ⟨a, z, ℓ, q, r, hq, hp, hrop, hr⟩
      obtain ⟨d, hd, had, hqd⟩ := isOp_up hp
      obtain ⟨d', hd', hzd', hℓd'⟩ := isOp_up hq
      exact ⟨r, hr, d, hd, a, had, q, hqd, d', hd', z, hzd', ℓ, hℓd', hq, hp, hrop⟩
  · obtain ⟨E, hE⟩ := cE01 U hU U U U
    refine ⟨E, fun p => (hE p).trans (and_congr (hU p) ?_)⟩
    constructor
    · rintro ⟨u, -, b, -, q, -, u', -, y, -, ℓ, -, hq, hp, hby⟩
      exact ⟨b, y, ℓ, q, hq, hp, hby⟩
    · rintro ⟨a, y, ℓ, q, hq, hp, hay⟩
      obtain ⟨d, hd, had, hqd⟩ := isOp_up hp
      obtain ⟨d', hd', hyd', hℓd'⟩ := isOp_up hq
      exact ⟨d, hd, a, had, q, hqd, d', hd', y, hyd', ℓ, hℓd', hq, hp, hay⟩
  · obtain ⟨E, hE⟩ := cE10 U hU U U U
    refine ⟨E, fun p => (hE p).trans (and_congr (hU p) ?_)⟩
    constructor
    · rintro ⟨u, -, b, -, q, -, u', -, y, -, ℓ, -, hq, hp, hby⟩
      exact ⟨b, y, ℓ, q, hq, hp, hby⟩
    · rintro ⟨a, y, ℓ, q, hq, hp, hay⟩
      obtain ⟨d, hd, had, hqd⟩ := isOp_up hp
      obtain ⟨d', hd', hyd', hℓd'⟩ := isOp_up hq
      exact ⟨d, hd, a, had, q, hqd, d', hd', y, hyd', ℓ, hℓd', hq, hp, hay⟩
  · obtain ⟨E, hE⟩ := cE00 U hU U U U
    refine ⟨E, fun p => (hE p).trans (and_congr (hU p) ?_)⟩
    constructor
    · rintro ⟨u, -, b, -, ℓ, -, hp, hbb⟩
      exact ⟨b, ℓ, hp, hbb⟩
    · rintro ⟨a, ℓ, hp, haa⟩
      obtain ⟨d, hd, had, hℓd⟩ := isOp_up hp
      exact ⟨d, hd, a, had, ℓ, hℓd, hp, haa⟩
  · obtain ⟨E, hE⟩ := cI01 U hU U U U
    refine ⟨E, fun p => (hE p).trans (and_congr (hU p) ?_)⟩
    constructor
    · rintro ⟨u, -, b, -, q, -, u', -, ℓ, -, hq, hp⟩
      exact ⟨b, ℓ, q, hq, hp⟩
    · rintro ⟨a, ℓ, q, hq, hp⟩
      obtain ⟨d, hd, had, hqd⟩ := isOp_up hp
      obtain ⟨d', hd', -, hℓd'⟩ := isOp_up hq
      exact ⟨d, hd, a, had, q, hqd, d', hd', ℓ, hℓd', hq, hp⟩
  · obtain ⟨E, hE⟩ := cSec U hU C ℓ₀ a
    refine ⟨E, fun x => (hE x).trans ?_⟩
    constructor
    · rintro ⟨-, hxa, p, hp, hop⟩
      exact ⟨hxa, p, hop, hp⟩
    · rintro ⟨hxa, p, hop, hp⟩
      exact ⟨hUm hxa, hxa, p, hp, hop⟩

/-- The pairs of sets are sets, from the axiom of pairing for the sets. -/
theorem pairS_of (hp : ∀ x y : SetsOf M, ∃ z : SetsOf M, ∀ w : SetsOf M, w ∈ z ↔ w = x ∨ w = y)
    (x y : M) (hx : IsSet x) (hy : IsSet y) : ∃ p, IsSet p ∧ IsOp p x y := by
  obtain ⟨s, hs⟩ := hp ⟨x, hx⟩ ⟨x, hx⟩
  obtain ⟨d, hd⟩ := hp ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨p, hpp⟩ := hp s d
  have hsm : ∀ c : M, c ∈ (s : M) ↔ c = x := fun c =>
    ⟨fun h => by
      have := (hs ⟨c, ⟨s, h⟩⟩).mp h
      rcases this with e | e <;> exact congrArg Subtype.val e,
    fun h => by
      subst h
      exact (hs ⟨c, hx⟩).mpr (Or.inl rfl)⟩
  have hdm : ∀ c : M, c ∈ (d : M) ↔ c = x ∨ c = y := fun c =>
    ⟨fun h => by
      have := (hd ⟨c, ⟨d, h⟩⟩).mp h
      rcases this with e | e
      · exact Or.inl (congrArg Subtype.val e)
      · exact Or.inr (congrArg Subtype.val e),
    fun h => by
      rcases h with h | h
      · subst h
        exact (hd ⟨c, hx⟩).mpr (Or.inl rfl)
      · subst h
        exact (hd ⟨c, hy⟩).mpr (Or.inr rfl)⟩
  have hpm : ∀ c : M, c ∈ (p : M) ↔ c = s ∨ c = d := fun c =>
    ⟨fun h => by
      have := (hpp ⟨c, ⟨p, h⟩⟩).mp h
      rcases this with e | e
      · exact Or.inl (congrArg Subtype.val e)
      · exact Or.inr (congrArg Subtype.val e),
    fun h => by
      rcases h with h | h
      · subst h
        exact (hpp s).mpr (Or.inl rfl)
      · subst h
        exact (hpp d).mpr (Or.inr rfl)⟩
  have hsing : IsSing (s : M) x := ⟨(hsm x).mpr rfl, fun c hc => (hsm c).mp hc⟩
  have hup : IsUp (d : M) x y :=
    ⟨(hdm x).mpr (Or.inl rfl), (hdm y).mpr (Or.inr rfl), fun c hc => (hdm c).mp hc⟩
  refine ⟨p, p.2, ⟨s, (hpm s).mpr (Or.inl rfl), hsing⟩, ⟨d, (hpm d).mpr (Or.inr rfl), hup⟩,
    fun z hz => ?_⟩
  rcases (hpm z).mp hz with rfl | rfl
  · exact Or.inl hsing
  · exact Or.inr hup

/-- **In a structure that satisfies `thetaZ`, the sets satisfy `𝗭𝗖`.** -/
theorem sets_models_zc (h : Eval (M := M) ![] Empty.elim thetaZ) :
    ∃ _ : Nonempty (SetsOf M), (SetsOf M)↓[ℒₛₑₜ] ⊧* 𝗭𝗖 := by
  obtain ⟨hc, hb⟩ := eval_thetaZ.mp h
  obtain ⟨x₀, hx₀⟩ := hc.1
  haveI : Nonempty (SetsOf M) := ⟨⟨x₀, hx₀⟩⟩
  refine ⟨inferInstance, ?_⟩
  have hpairing : ∀ x y : SetsOf M, ∃ z : SetsOf M, ∀ w : SetsOf M, w ∈ z ↔ w = x ∨ w = y := by
    have := hb “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y” (by simp [bstL])
    simpa using this
  have hOK : ClassOK M := classOK_of hc (pairS_of hpairing)
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with (hφ | hφ) | hφ
  · rcases bst_cases φ hφ with h' | h'
    · have : (SetsOf M)↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory) := inferInstance
      exact models_theory_iff.mp this φ h'
    · exact hb φ h'
  · cases hφ with
    | separation ψ =>
      suffices ∀ (ε : ℕ → SetsOf M) (x : SetsOf M), ∃ y : SetsOf M,
          ∀ z, z ∈ y ↔ z ∈ x ∧ Eval (M := SetsOf M) ![z] ε ψ by
        simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema,
          Matrix.constant_eq_singleton]
      exact fun ε x => fullsep_sets hOK ψ ε x
  · have e : φ = Axiom.choice := hφ
    rw [e]
    exact hb _ (by simp [bstL])

end derive

/-! ### The rank axioms among the sets -/

section rank

/-- `h` is the hierarchy of the iterated power sets of `ω` on the ordinals up to `θ`, `k` is a
member of `θ`, and `θ` does not map one-to-one into the set of the hierarchy at `k`. This is
the rank axiom with `k` in the place of the numeral. -/
def RankKAt {V : Type} [SetStructure V] (k θ h : V) : Prop :=
  MH.Ord θ ∧ (PowH h θ ∧ (k ∈ θ ∧ ∃ w, Pr h k w ∧ ¬∃ f, InjS f θ w))

def rankKAtU : UDef (k := 3) (fun V _ v ↦ RankKAt (v 0) (v 1) (v 2)) :=
  (((UDef.ofB ordB).comp ![1]).and ((powHU.comp ![2, 1]).and ((UDef.mem 0 1).and
    (UDef.ex (((UDef.ofB prB).comp ![3, 1, 0]).and
      (UDef.ex (injSU.comp ![0, 3, 1])).not))))).congr fun _ _ _ => Iff.rfl

def rankKU : UDef (k := 1) (fun V _ v ↦ ∃ h θ : V, RankKAt (v 0) θ h) :=
  (UDef.ex (UDef.ex (rankKAtU.comp ![2, 0, 1]))).congr fun _ _ _ => Iff.rfl

theorem hasRank_iff {n : ℕ} {V : Type} [SetStructure V] :
    HasRank n V ↔ ∃ k : V, IsNum n k ∧ ∃ h θ : V, RankKAt k θ h :=
  ⟨fun ⟨h, θ, hO, hP, k, hk, hkθ, hw⟩ => ⟨k, hk, h, θ, hO, hP, hkθ, hw⟩,
    fun ⟨k, hk, h, θ, hO, hP, hkθ, hw⟩ => ⟨h, θ, hO, hP, k, hk, hkθ, hw⟩⟩

/-- Among the sets, the hierarchy reaches the level `d`. -/
def SetRank (V : Type) [SetStructure V] (d : V) : Prop :=
  ∃ hd : IsSet d, ∃ h θ : SetsOf V, RankKAt (⟨d, hd⟩ : SetsOf V) θ h

def setRankU : UDef (k := 1) (fun V _ v ↦ SetRank V (v 0)) where
  φ := isSetU.φ ⋏ relS rankKU.φ
  eval V _ v := by
    show (Eval (M := V) v Empty.elim isSetU.φ ∧ Eval (M := V) v Empty.elim (relS rankKU.φ)) ↔ _
    have h1 : Eval (M := V) v Empty.elim isSetU.φ ↔ IsSet (v 0) := isSetU.eval V v
    rw [h1]
    constructor
    · rintro ⟨hd, h2⟩
      have e1 : (fun i ↦ (((fun _ : Fin 1 ↦ (⟨v 0, hd⟩ : SetsOf V)) i : SetsOf V) : V)) = v := by
        funext i
        have : i = 0 := Subsingleton.elim _ _
        subst this
        rfl
      rw [← e1] at h2
      have h3 := (eval_relS rankKU.φ (fun _ : Fin 1 ↦ (⟨v 0, hd⟩ : SetsOf V))).mp h2
      exact ⟨hd, (rankKU.eval (SetsOf V) _).mp h3⟩
    · rintro ⟨hd, h3⟩
      refine ⟨hd, ?_⟩
      have e1 : (fun i ↦ (((fun _ : Fin 1 ↦ (⟨v 0, hd⟩ : SetsOf V)) i : SetsOf V) : V)) = v := by
        funext i
        have : i = 0 := Subsingleton.elim _ _
        subst this
        rfl
      have h2 := (eval_relS rankKU.φ (fun _ : Fin 1 ↦ (⟨v 0, hd⟩ : SetsOf V))).mpr
        ((rankKU.eval (SetsOf V) (fun _ : Fin 1 ↦ (⟨v 0, hd⟩ : SetsOf V))).mpr h3)
      rw [e1] at h2
      exact h2

/-- **The instance of the family at `d`**: `z` is empty, `d'` is the successor of `d`, they are
sets, and among the sets the hierarchy reaches the level `d`. -/
def ChiR (V : Type) [SetStructure V] (d' d z : V) : Prop :=
  (∀ w : V, ¬w ∈ z) ∧ (SuccR d' d ∧ (IsSet d' ∧ (IsSet z ∧ SetRank V d)))

def chiU : UDef (k := 3) (fun V _ v ↦ ChiR V (v 0) (v 1) (v 2)) :=
  ((UDef.all (UDef.mem 0 3).not).and (((UDef.ofB succB).comp ![0, 1]).and
    ((isSetU.comp ![0]).and ((isSetU.comp ![2]).and (setRankU.comp ![1]))))).congr
    fun _ _ _ => Iff.rfl

/-- Relations with a bounded definition are absolute for a collection closed under members. -/
theorem bdef_subS {V : Type} [SetStructure V] {U : Set V} (hU : ∀ y ∈ U, ∀ z ∈ y, z ∈ U)
    {k : ℕ} {R : MRel k} (d : BDef R) (v : Fin k → U) :
    R U v ↔ R V (fun i ↦ (v i : V)) := by
  have h1 := eval_submodel_iff (U := U) hU d.bdd v (Empty.elim)
  have e : (fun x : Empty ↦ ((Empty.elim x : U) : V)) = (Empty.elim : Empty → V) :=
    funext fun x => x.elim
  rw [e] at h1
  exact (d.eval U v).symm.trans (h1.trans (d.eval V _))

/-- **If the instances hold along a sequence, the sets satisfy every rank axiom.** -/
theorem hasRank_sets {M : Type} [SetStructure M] (d : ℕ → M)
    (hd : ∀ j, ChiR M (d (j + 1)) (d j) (d 0)) (j : ℕ) : HasRank j (SetsOf M) := by
  have hU : ∀ y ∈ SetsOf M, ∀ z ∈ y, z ∈ SetsOf M := fun y _ z hz => ⟨y, hz⟩
  have hS : ∀ j, IsSet (d j) := fun j => by
    cases j with
    | zero => exact (hd 0).2.2.2.1
    | succ j => exact (hd j).2.2.1
  have hnum : ∀ j, IsNum j (⟨d j, hS j⟩ : SetsOf M) := by
    intro j
    induction j with
    | zero => exact fun w hw => (hd 0).1 w.1 hw
    | succ j ih =>
      refine ⟨⟨d j, hS j⟩, (hd j).2.1.2.1, ih, ?_⟩
      exact (bdef_subS hU succB ![(⟨d (j + 1), hS (j + 1)⟩ : SetsOf M), ⟨d j, hS j⟩]).mpr
        (hd j).2.1
  obtain ⟨hdj, h, θ, hr⟩ := (hd j).2.2.2.2
  exact hasRank_iff.mpr ⟨⟨d j, hS j⟩, hnum j, h, θ, hr⟩

end rank

end MH

end FFL.FirstOrder.SetTheory
