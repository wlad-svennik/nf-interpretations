module

public import HkModel

@[expose] public section

/-!
# Classes: every formula about the sets defines a class

A structure `M` for `ℒₛₑₜ` is read as a structure of classes: its *sets* are the elements that
are members of some element (`IsSet`, `SetsOf M`). `ClassOK M` lists finitely many closure
conditions on `M`, each a single sentence: a universal class, complements, intersections,
unions, the two projections of a class of pairs for the quantifiers, two operations that add an
entry to a list, the classes for the atomic formulas of the first two entries of a list,
sections, the pairs of sets are sets, and a class included in a set is a set.

An environment of sets is a list `⟨x₀, ⟨x₁, … ⟨x_{k-1}, t⟩⟩⟩` of Kuratowski pairs (`LEnv`), so
that binding a new variable `0` is one more pair in front.

* `atom_class`: the class of the lists whose entries `i` and `j` are in a relation, from the
  classes for the entries `0, 1`, `1, 0` and `0, 0`.
* **`class_ex`**: for every formula `φ` there is a class whose members are the lists of the
  environments in which `φ` is true in the structure of the sets.
* **`fullsep_sets`**: so the structure of the sets satisfies the separation schema.

Nothing is assumed of `M` but `ClassOK M`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

section cls

variable {M : Type} [SetStructure M]

/-- `x` is a set: a member of some element. -/
def IsSet (x : M) : Prop := ∃ Y : M, x ∈ Y

/-- The sets of a structure of classes. -/
abbrev SetsOf (M : Type) [SetStructure M] : Set M := {x | IsSet x}

theorem isS_fst {p a b : M} (h : IsOp p a b) : IsSet a := by
  obtain ⟨⟨s, -, hs⟩, -⟩ := h
  exact ⟨s, hs.1⟩

theorem isS_snd {p a b : M} (h : IsOp p a b) : IsSet b := by
  obtain ⟨-, ⟨d, -, hd⟩, -⟩ := h
  exact ⟨d, hd.2.1⟩

/-- `x` is the entry number `i` of the list `ℓ`. -/
def Nth : ℕ → M → M → Prop
  | 0, ℓ, x => ∃ ℓ', IsOp ℓ x ℓ'
  | i + 1, ℓ, x => ∃ y ℓ', IsOp ℓ y ℓ' ∧ Nth i ℓ' x

/-- `ℓ` is the list of the environment `e` followed by `t`. -/
def LEnv : {k : ℕ} → (Fin k → M) → M → M → Prop
  | 0, _, t, ℓ => ℓ = t
  | _ + 1, e, t, ℓ => ∃ ℓ', LEnv (fun i ↦ e i.succ) t ℓ' ∧ IsOp ℓ (e 0) ℓ'

theorem nth_of_lenv : ∀ {k : ℕ} (e : Fin k → M) (t ℓ : M), LEnv e t ℓ → ∀ i : Fin k,
    Nth i ℓ (e i)
  | 0, _, _, _, _, i => i.elim0
  | k + 1, e, t, ℓ, ⟨ℓ', hl, hop⟩, i => by
    cases i using Fin.cases with
    | zero => exact ⟨ℓ', hop⟩
    | succ j => exact ⟨e 0, ℓ', hop, nth_of_lenv (fun i ↦ e i.succ) t ℓ' hl j⟩

theorem lenv_cons {k : ℕ} {e : Fin k → M} {t ℓ ℓ' x : M} (h : LEnv e t ℓ')
    (hop : IsOp ℓ x ℓ') : LEnv (x :> e) t ℓ := ⟨ℓ', h, hop⟩

/-- **The closure conditions on a structure of classes.** -/
structure ClassOK (M : Type) [SetStructure M] : Prop where
  univ : ∃ U : M, ∀ x, x ∈ U ↔ IsSet x
  compl : ∀ C : M, ∃ E : M, ∀ x, x ∈ E ↔ (IsSet x ∧ ¬x ∈ C)
  inter : ∀ C D : M, ∃ E : M, ∀ x, x ∈ E ↔ (x ∈ C ∧ x ∈ D)
  union : ∀ C D : M, ∃ E : M, ∀ x, x ∈ E ↔ (x ∈ C ∨ x ∈ D)
  dom : ∀ C : M, ∃ E : M, ∀ ℓ, ℓ ∈ E ↔ (IsSet ℓ ∧ ∃ a p, IsOp p a ℓ ∧ p ∈ C)
  all : ∀ C : M, ∃ E : M, ∀ ℓ, ℓ ∈ E ↔ (IsSet ℓ ∧ ∀ a, IsSet a → ∃ p, IsOp p a ℓ ∧ p ∈ C)
  w : ∀ C : M, ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a ℓ, IsOp p a ℓ ∧ ℓ ∈ C)
  w1 : ∀ C : M, ∃ E : M, ∀ p, p ∈ E ↔
    (IsSet p ∧ ∃ a z ℓ q r, IsOp q z ℓ ∧ (IsOp p a q ∧ (IsOp r a ℓ ∧ r ∈ C)))
  e01 : ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a y ℓ q, IsOp q y ℓ ∧ (IsOp p a q ∧ a ∈ y))
  e10 : ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a y ℓ q, IsOp q y ℓ ∧ (IsOp p a q ∧ y ∈ a))
  e00 : ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a ℓ, IsOp p a ℓ ∧ a ∈ a)
  i01 : ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a ℓ q, IsOp q a ℓ ∧ IsOp p a q)
  sec : ∀ C ℓ₀ a : M, ∃ E : M, ∀ x, x ∈ E ↔ (x ∈ a ∧ ∃ p, IsOp p x ℓ₀ ∧ p ∈ C)
  subS : ∀ D a : M, IsSet a → (∀ z, z ∈ D → z ∈ a) → IsSet D
  pairS : ∀ x y : M, IsSet x → IsSet y → ∃ p, IsSet p ∧ IsOp p x y

variable (h : ClassOK M)

include h

/-- The class for the entries `0` and `m + 1`, from the class for the entries `0` and `1`. -/
theorem atom_zero_succ (ρ : M → M → Prop)
    (h01 : ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a y ℓ q, IsOp q y ℓ ∧ (IsOp p a q ∧ ρ a y))) :
    ∀ m : ℕ, ∃ C : M, ∀ ℓ, IsSet ℓ → ∀ x y, Nth 0 ℓ x → Nth (m + 1) ℓ y → (ℓ ∈ C ↔ ρ x y)
  | 0 => by
    obtain ⟨E, hE⟩ := h01
    refine ⟨E, fun ℓ hS x y hx hy => ?_⟩
    obtain ⟨ℓ', hop⟩ := hx
    obtain ⟨b, ℓ₁, hop1, ℓ₂, hop2⟩ := hy
    obtain ⟨rfl, rfl⟩ := op_inj hop hop1
    rw [hE]
    constructor
    · rintro ⟨-, a, y', ℓ'', q, hq, hp, hρ⟩
      obtain ⟨rfl, rfl⟩ := op_inj hp hop
      obtain ⟨rfl, -⟩ := op_inj hq hop2
      exact hρ
    · intro hρ
      exact ⟨hS, x, y, ℓ₂, ℓ', hop2, hop, hρ⟩
  | m + 1 => by
    obtain ⟨C, hC⟩ := atom_zero_succ ρ h01 m
    obtain ⟨D, hD⟩ := h.w1 C
    refine ⟨D, fun ℓ hS x y hx hy => ?_⟩
    obtain ⟨ℓ', hop⟩ := hx
    obtain ⟨b, ℓ₁, hop1, c, ℓ₂, hop2, hn⟩ := hy
    obtain ⟨rfl, rfl⟩ := op_inj hop hop1
    rw [hD]
    constructor
    · rintro ⟨-, a, z, ℓ'', q, r, hq, hp, hr, hrC⟩
      obtain ⟨rfl, rfl⟩ := op_inj hp hop
      obtain ⟨rfl, rfl⟩ := op_inj hq hop2
      exact (hC r ⟨C, hrC⟩ a y ⟨ℓ'', hr⟩ ⟨a, ℓ'', hr, hn⟩).mp hrC
    · intro hρ
      obtain ⟨r, hrS, hr⟩ := h.pairS x ℓ₂ (isS_fst hop) (isS_snd hop2)
      exact ⟨hS, x, c, ℓ₂, ℓ', r, hop2, hop, hr,
        (hC r hrS x y ⟨ℓ₂, hr⟩ ⟨x, ℓ₂, hr, hn⟩).mpr hρ⟩

/-- **The class of the lists whose entries `i` and `j` are in the relation `ρ`.** -/
theorem atom_class (ρ : M → M → Prop)
    (h01 : ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a y ℓ q, IsOp q y ℓ ∧ (IsOp p a q ∧ ρ a y)))
    (h10 : ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a y ℓ q, IsOp q y ℓ ∧ (IsOp p a q ∧ ρ y a)))
    (h00 : ∃ E : M, ∀ p, p ∈ E ↔ (IsSet p ∧ ∃ a ℓ, IsOp p a ℓ ∧ ρ a a)) :
    ∀ i j : ℕ, ∃ C : M, ∀ ℓ, IsSet ℓ → ∀ x y, Nth i ℓ x → Nth j ℓ y → (ℓ ∈ C ↔ ρ x y)
  | 0, 0 => by
    obtain ⟨E, hE⟩ := h00
    refine ⟨E, fun ℓ hS x y hx hy => ?_⟩
    obtain ⟨ℓ', hop⟩ := hx
    obtain ⟨ℓ'', hop'⟩ := hy
    obtain ⟨rfl, rfl⟩ := op_inj hop hop'
    rw [hE]
    constructor
    · rintro ⟨-, a, ℓ₁, hp, hρ⟩
      obtain ⟨rfl, -⟩ := op_inj hp hop
      exact hρ
    · intro hρ
      exact ⟨hS, x, ℓ', hop, hρ⟩
  | 0, m + 1 => atom_zero_succ h ρ h01 m
  | m + 1, 0 => by
    obtain ⟨C, hC⟩ := atom_zero_succ h (fun a b => ρ b a) h10 m
    exact ⟨C, fun ℓ hS x y hx hy => hC ℓ hS y x hy hx⟩
  | i + 1, j + 1 => by
    obtain ⟨C, hC⟩ := atom_class ρ h01 h10 h00 i j
    obtain ⟨D, hD⟩ := h.w C
    refine ⟨D, fun ℓ hS x y hx hy => ?_⟩
    obtain ⟨b, ℓ₁, hop1, hni⟩ := hx
    obtain ⟨b', ℓ₁', hop1', hnj⟩ := hy
    obtain ⟨rfl, rfl⟩ := op_inj hop1 hop1'
    rw [hD]
    constructor
    · rintro ⟨-, a, ℓ', hp, hC'⟩
      obtain ⟨rfl, rfl⟩ := op_inj hp hop1
      exact (hC ℓ' ⟨C, hC'⟩ x y hni hnj).mp hC'
    · intro hρ
      exact ⟨hS, b, ℓ₁, hop1, (hC ℓ₁ (isS_snd hop1) x y hni hnj).mpr hρ⟩

theorem mem_class (i j : ℕ) :
    ∃ C : M, ∀ ℓ, IsSet ℓ → ∀ x y, Nth i ℓ x → Nth j ℓ y → (ℓ ∈ C ↔ x ∈ y) :=
  atom_class h (fun a b => a ∈ b) h.e01 h.e10 h.e00 i j

theorem eq_class (i j : ℕ) :
    ∃ C : M, ∀ ℓ, IsSet ℓ → ∀ x y, Nth i ℓ x → Nth j ℓ y → (ℓ ∈ C ↔ x = y) := by
  obtain ⟨E, hE⟩ := h.i01
  obtain ⟨U, hU⟩ := h.univ
  obtain ⟨W, hW⟩ := h.w U
  refine atom_class h (fun a b => a = b) ⟨E, fun p => (hE p).trans ?_⟩
    ⟨E, fun p => (hE p).trans ?_⟩ ⟨W, fun p => (hW p).trans ?_⟩ i j
  · exact and_congr_right fun _ => ⟨fun ⟨a, ℓ, q, hq, hp⟩ => ⟨a, a, ℓ, q, hq, hp, rfl⟩,
      fun ⟨a, y, ℓ, q, hq, hp, e⟩ => ⟨a, ℓ, q, e ▸ hq, hp⟩⟩
  · exact and_congr_right fun _ => ⟨fun ⟨a, ℓ, q, hq, hp⟩ => ⟨a, a, ℓ, q, hq, hp, rfl⟩,
      fun ⟨a, y, ℓ, q, hq, hp, e⟩ => ⟨a, ℓ, q, e ▸ hq, hp⟩⟩
  · exact and_congr_right fun _ => ⟨fun ⟨a, ℓ, hp, _⟩ => ⟨a, ℓ, hp, rfl⟩,
      fun ⟨a, ℓ, hp, _⟩ => ⟨a, ℓ, hp, (hU ℓ).mpr (isS_snd hp)⟩⟩

omit h in
theorem coe_cons {k : ℕ} (x : SetsOf M) (e : Fin k → SetsOf M) :
    (fun i ↦ (((x :> e) i : SetsOf M) : M)) = ((x : M) :> fun i ↦ (e i : M)) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- **Every formula about the sets defines a class of lists.** -/
theorem class_ex : ∀ {k : ℕ} (φ : Semiformula ℒₛₑₜ Empty k), ∃ C : M,
    ∀ (e : Fin k → SetsOf M) (t ℓ : M), IsSet ℓ → LEnv (fun i ↦ (e i : M)) t ℓ →
      (ℓ ∈ C ↔ Eval (M := SetsOf M) e Empty.elim φ) := by
  intro k φ
  induction φ using Semiformula.rec' with
  | hverum =>
    obtain ⟨U, hU⟩ := h.univ
    exact ⟨U, fun e t ℓ hS _ => ⟨fun _ => trivial, fun _ => (hU ℓ).mpr hS⟩⟩
  | hfalsum =>
    obtain ⟨U, hU⟩ := h.univ
    obtain ⟨E, hE⟩ := h.compl U
    exact ⟨E, fun e t ℓ hS _ => ⟨fun hin => ((hE ℓ).mp hin).2 ((hU ℓ).mpr hS),
      fun hf => hf.elim⟩⟩
  | hrel r v =>
    cases r with
    | eq =>
      obtain ⟨C, hC⟩ := eq_class h (tix (v 0)) (tix (v 1))
      refine ⟨C, fun e t ℓ hS hl => ?_⟩
      have hn := nth_of_lenv _ t ℓ hl
      rw [hC ℓ hS _ _ (hn (tix (v 0))) (hn (tix (v 1)))]
      show _ ↔ (v 0).val (M := SetsOf M) e _ = (v 1).val (M := SetsOf M) e _
      rw [tix_val, tix_val]
      exact ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
    | mem =>
      obtain ⟨C, hC⟩ := mem_class h (tix (v 0)) (tix (v 1))
      refine ⟨C, fun e t ℓ hS hl => ?_⟩
      have hn := nth_of_lenv _ t ℓ hl
      rw [hC ℓ hS _ _ (hn (tix (v 0))) (hn (tix (v 1)))]
      show _ ↔ (v 0).val (M := SetsOf M) e _ ∈ (v 1).val (M := SetsOf M) e _
      rw [tix_val, tix_val]
      exact Iff.rfl
  | hnrel r v =>
    cases r with
    | eq =>
      obtain ⟨C, hC⟩ := eq_class h (tix (v 0)) (tix (v 1))
      obtain ⟨E, hE⟩ := h.compl C
      refine ⟨E, fun e t ℓ hS hl => ?_⟩
      have hn := nth_of_lenv _ t ℓ hl
      rw [hE, hC ℓ hS _ _ (hn (tix (v 0))) (hn (tix (v 1)))]
      show _ ↔ ¬(v 0).val (M := SetsOf M) e _ = (v 1).val (M := SetsOf M) e _
      rw [tix_val, tix_val]
      exact ⟨fun hh hh' => hh.2 (congrArg Subtype.val hh'),
        fun hh => ⟨hS, fun hh' => hh (Subtype.ext hh')⟩⟩
    | mem =>
      obtain ⟨C, hC⟩ := mem_class h (tix (v 0)) (tix (v 1))
      obtain ⟨E, hE⟩ := h.compl C
      refine ⟨E, fun e t ℓ hS hl => ?_⟩
      have hn := nth_of_lenv _ t ℓ hl
      rw [hE, hC ℓ hS _ _ (hn (tix (v 0))) (hn (tix (v 1)))]
      show _ ↔ ¬(v 0).val (M := SetsOf M) e _ ∈ (v 1).val (M := SetsOf M) e _
      rw [tix_val, tix_val]
      exact ⟨fun hh hh' => hh.2 hh', fun hh => ⟨hS, hh⟩⟩
  | hand φ ψ ih1 ih2 =>
    obtain ⟨C, hC⟩ := ih1
    obtain ⟨D, hD⟩ := ih2
    obtain ⟨E, hE⟩ := h.inter C D
    exact ⟨E, fun e t ℓ hS hl => (hE ℓ).trans (and_congr (hC e t ℓ hS hl) (hD e t ℓ hS hl))⟩
  | hor φ ψ ih1 ih2 =>
    obtain ⟨C, hC⟩ := ih1
    obtain ⟨D, hD⟩ := ih2
    obtain ⟨E, hE⟩ := h.union C D
    exact ⟨E, fun e t ℓ hS hl => (hE ℓ).trans (or_congr (hC e t ℓ hS hl) (hD e t ℓ hS hl))⟩
  | hall φ ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨D, hD⟩ := h.all C
    refine ⟨D, fun e t ℓ hS hl => (hD ℓ).trans ?_⟩
    constructor
    · rintro ⟨-, hall⟩ x
      obtain ⟨p, hp, hpC⟩ := hall x.1 x.2
      have hl' : LEnv (fun i ↦ (((x :> e) i : SetsOf M) : M)) t p := by
        rw [coe_cons]
        exact lenv_cons hl hp
      exact (hC (x :> e) t p ⟨C, hpC⟩ hl').mp hpC
    · intro hev
      refine ⟨hS, fun a ha => ?_⟩
      obtain ⟨p, hpS, hp⟩ := h.pairS a ℓ ha hS
      have hl' : LEnv (fun i ↦ ((((⟨a, ha⟩ : SetsOf M) :> e) i : SetsOf M) : M)) t p := by
        rw [coe_cons]
        exact lenv_cons hl hp
      exact ⟨p, hp, (hC ((⟨a, ha⟩ : SetsOf M) :> e) t p hpS hl').mpr (hev ⟨a, ha⟩)⟩
  | hexs φ ih =>
    obtain ⟨C, hC⟩ := ih
    obtain ⟨D, hD⟩ := h.dom C
    refine ⟨D, fun e t ℓ hS hl => (hD ℓ).trans ?_⟩
    constructor
    · rintro ⟨-, a, p, hp, hpC⟩
      have ha : IsSet a := isS_fst hp
      have hl' : LEnv (fun i ↦ ((((⟨a, ha⟩ : SetsOf M) :> e) i : SetsOf M) : M)) t p := by
        rw [coe_cons]
        exact lenv_cons hl hp
      exact ⟨⟨a, ha⟩, (hC ((⟨a, ha⟩ : SetsOf M) :> e) t p ⟨C, hpC⟩ hl').mp hpC⟩
    · rintro ⟨x, hev⟩
      obtain ⟨p, hpS, hp⟩ := h.pairS x.1 ℓ x.2 hS
      have hl' : LEnv (fun i ↦ (((x :> e) i : SetsOf M) : M)) t p := by
        rw [coe_cons]
        exact lenv_cons hl hp
      exact ⟨hS, x.1, p, hp, (hC (x :> e) t p hpS hl').mpr hev⟩

/-- The list of an environment of sets is a set. -/
theorem exists_lenv : ∀ {k : ℕ} (e : Fin k → SetsOf M) (t : M), IsSet t →
    ∃ ℓ : M, IsSet ℓ ∧ LEnv (fun i ↦ (e i : M)) t ℓ
  | 0, _, t, ht => ⟨t, ht, rfl⟩
  | k + 1, e, t, ht => by
    obtain ⟨ℓ', hS', hl'⟩ := exists_lenv (fun i ↦ e i.succ) t ht
    obtain ⟨p, hpS, hp⟩ := h.pairS (e 0).1 ℓ' (e 0).2 hS'
    exact ⟨p, hpS, ℓ', hl', hp⟩

/-- **The structure of the sets satisfies the separation schema.** -/
theorem fullsep_sets (ψ : SetTheorySemiproposition 1) (ε : ℕ → SetsOf M) (t : SetsOf M) :
    ∃ y : SetsOf M, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := SetsOf M) ![z] ε ψ := by
  classical
  let m := ψ.fvSup
  let ω : Rew ℒₛₑₜ ℕ 1 Empty (m + 1) :=
    Rew.bind (fun _ ↦ (#0 : Semiterm ℒₛₑₜ Empty (m + 1)))
      (fun k ↦ if h : k < m then (#(Fin.succ ⟨k, h⟩) : Semiterm ℒₛₑₜ Empty (m + 1)) else #0)
  have key : ∀ z : SetsOf M, Eval (M := SetsOf M) (z :> fun i : Fin m ↦ ε i) Empty.elim
      (ω ▹ ψ) ↔ Eval (M := SetsOf M) ![z] ε ψ := by
    intro z
    have e1 : (Semiterm.val (M := SetsOf M) (z :> fun i : Fin m ↦ ε i)
        Empty.elim ∘ ω ∘ Semiterm.bvar) = ![z] := by
      funext i
      simp [ω]
    rw [eval_rew, e1]
    refine eval_iff_of_funEqOn ψ ?_
    intro k hk
    have hk' : k < m := lt_fvSup_of_fvar? hk
    simp [ω, hk']
  obtain ⟨C, hC⟩ := class_ex h (ω ▹ ψ)
  obtain ⟨ℓ₀, hℓ₀S, hℓ₀⟩ := exists_lenv h (fun i : Fin m ↦ ε i) t.1 t.2
  obtain ⟨E, hE⟩ := h.sec C ℓ₀ t.1
  have hES : IsSet E := h.subS E t.1 t.2 fun z hz => ((hE z).mp hz).1
  refine ⟨⟨E, hES⟩, fun z => ?_⟩
  have h1 : z ∈ (⟨E, hES⟩ : SetsOf M) ↔ (z : M) ∈ E := Iff.rfl
  have h2 : z ∈ t ↔ (z : M) ∈ (t : M) := Iff.rfl
  rw [h1, hE, h2, ← key z]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨p, hp, hpC⟩
    have hl' : LEnv (fun i ↦ (((z :> fun i : Fin m ↦ ε i) i : SetsOf M) : M)) t.1 p := by
      rw [coe_cons]
      exact lenv_cons hℓ₀ hp
    exact (hC _ t.1 p ⟨C, hpC⟩ hl').mp hpC
  · intro hev
    obtain ⟨p, hpS, hp⟩ := h.pairS z.1 ℓ₀ z.2 hℓ₀S
    have hl' : LEnv (fun i ↦ (((z :> fun i : Fin m ↦ ε i) i : SetsOf M) : M)) t.1 p := by
      rw [coe_cons]
      exact lenv_cons hℓ₀ hp
    exact ⟨p, hp, (hC _ t.1 p hpS hl').mpr hev⟩

end cls

end MH

end FFL.FirstOrder.SetTheory
