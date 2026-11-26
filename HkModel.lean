module

public import HkCut

@[expose] public section

/-!
# The structure of an assignment

Inside a model `V` of `𝗠𝗛`. Let `S` be an assignment of truth values to the atomic sentences
of numbers that makes the axioms of equality true (`eqAx`, `EqOK`). The structure `Dom S` has
as elements the numbers that are the least in their class of the equality of `S`, with the
membership of `S` and true equality.

* `repD`: the least number of the class of a number.
* **`holds_eval`**: a formula that is true under `S` (`Holds`, with the witnesses of
  `HkHolds.lean` for the existential quantifiers) is true in `Dom S`.
* `eval_eqAx`: the axioms of equality are true in every structure.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### The axioms of equality -/

section eqax

/-- The relation symbols of `ℒₛₑₜ`. -/
abbrev eqS : (ℒₛₑₜ).Rel 2 := Language.Set.Rel.eq

abbrev memS : (ℒₛₑₜ).Rel 2 := Language.Set.Rel.mem

/-- Reflexivity. -/
def eqRefl : Semiformula ℒₛₑₜ Empty 0 := ∀¹ (.rel eqS ![#0, #0])

/-- Symmetry. -/
def eqSymm : Semiformula ℒₛₑₜ Empty 0 := ∀¹ ∀¹ ((.nrel eqS ![#1, #0]) ⋎ (.rel eqS ![#0, #1]))

/-- Transitivity. -/
def eqTrans : Semiformula ℒₛₑₜ Empty 0 :=
  ∀¹ ∀¹ ∀¹ ((.nrel eqS ![#2, #1]) ⋎ ((.nrel eqS ![#1, #0]) ⋎ (.rel eqS ![#2, #0])))

/-- Membership respects equality. -/
def eqCong : Semiformula ℒₛₑₜ Empty 0 :=
  ∀¹ ∀¹ ∀¹ ∀¹ ((.nrel eqS ![#3, #2]) ⋎ ((.nrel eqS ![#1, #0]) ⋎
    ((.nrel memS ![#3, #1]) ⋎ (.rel memS ![#2, #0]))))

/-- **The axioms of equality.** -/
def eqAx : Semiformula ℒₛₑₜ Empty 0 := eqRefl ⋏ (eqSymm ⋏ (eqTrans ⋏ eqCong))

theorem cnt_eqAx : cnt eqAx = 0 := rfl

/-- **The axioms of equality are true in every structure.** -/
theorem eval_eqAx (M : Type) [SetStructure M] : Eval (M := M) ![] Empty.elim eqAx := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    show x = x
    rfl
  · intro x y
    show ¬x = y ∨ y = x
    by_cases h : x = y
    · exact Or.inr h.symm
    · exact Or.inl h
  · intro x y z
    show ¬x = y ∨ (¬y = z ∨ x = z)
    by_cases h : x = y
    · by_cases h' : y = z
      · exact Or.inr (Or.inr (h.trans h'))
      · exact Or.inr (Or.inl h')
    · exact Or.inl h
  · intro a a' b b'
    show ¬a = a' ∨ (¬b = b' ∨ (¬a ∈ b ∨ a' ∈ b'))
    by_cases h : a = a'
    · by_cases h' : b = b'
      · by_cases h'' : a ∈ b
        · exact Or.inr (Or.inr (Or.inr (h ▸ h' ▸ h'')))
        · exact Or.inr (Or.inr (Or.inl h''))
      · exact Or.inr (Or.inl h')
    · exact Or.inl h

end eqax

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The assignment makes the axioms of equality true. -/
structure EqOK (S : V) : Prop where
  refl : ∀ t, t ∈ (om : V) → atm 1 t t ∈ S
  symm : ∀ a b, a ∈ (om : V) → b ∈ (om : V) → atm 1 a b ∈ S → atm 1 b a ∈ S
  trans : ∀ a b c, a ∈ (om : V) → b ∈ (om : V) → c ∈ (om : V) → atm 1 a b ∈ S →
    atm 1 b c ∈ S → atm 1 a c ∈ S
  cong : ∀ a a' b b', a ∈ (om : V) → a' ∈ (om : V) → b ∈ (om : V) → b' ∈ (om : V) →
    atm 1 a a' ∈ S → atm 1 b b' ∈ S → atm 0 a b ∈ S → atm 0 a' b' ∈ S

theorem eqOK_of_holds {S : V} {c : ℕ} (h : Holds S eqAx c ![]) : EqOK S := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun t ht => h1 t ht, fun a b ha hb hab => ?_, fun a b c ha hb hc hab hbc => ?_,
    fun a a' b b' ha ha' hb hb' haa hbb hab => ?_⟩
  · rcases h2 a ha b hb with h | h
    · exact absurd hab h
    · exact h
  · rcases h3 a ha b hb c hc with h | h | h
    · exact absurd hab h
    · exact absurd hbc h
    · exact h
  · rcases h4 a ha a' ha' b hb b' hb' with h | h | h | h
    · exact absurd haa h
    · exact absurd hbb h
    · exact absurd hab h
    · exact h

/-- `t` is the least number of its class. -/
def IsRep (S t : V) : Prop := t ∈ (om : V) ∧ ∀ t', t' ∈ t → ¬atm 1 t' t ∈ S

/-- **The structure of the assignment `S`**: the least numbers of the classes. -/
abbrev Dom (S : V) : Type := {t : V // IsRep S t}

instance domStructure (S : V) : SetStructure (Dom S) := ⟨fun y x ↦ atm 0 x.val y.val ∈ S⟩

theorem dom_mem_iff {S : V} {x y : Dom S} : x ∈ y ↔ atm 0 x.val y.val ∈ S := Iff.rfl

variable {S : V} (hE : EqOK S)

include hE

theorem exists_rep (t : V) (ht : t ∈ (om : V)) : ∃ r, IsRep S r ∧ atm 1 r t ∈ S := by
  obtain ⟨P, hP⟩ := exists_canP (V := V)
  let Z : V := sepB (k := 4) (BDef.bex 4 ((atomB 1).comp ![2, 3, 1, 4, 0])) (sc t)
    ![P, (om : V), t, S]
  have hZ : ∀ z, z ∈ Z ↔ z ∈ sc t ∧ ∃ α, α ∈ S ∧ AtomR P (om : V) 1 z t α :=
    fun z => mem_sepB _ _ _ z
  have hsc : ∀ z, z ∈ sc t → z ∈ (om : V) := fun z hz =>
    (ord_om (V := V)).1 _ (sc_mem_om ht) z hz
  have hZ' : ∀ z, z ∈ Z ↔ z ∈ sc t ∧ atm 1 z t ∈ S := fun z => (hZ z).trans
    ⟨fun ⟨hz, α, hα, hat⟩ => ⟨hz, (atomR_iff hP 1 (hsc z hz) ht).mp hat ▸ hα⟩,
      fun ⟨hz, h⟩ => ⟨hz, _, h, (atomR_iff hP 1 (hsc z hz) ht).mpr rfl⟩⟩
  have hOsc : Ord (sc t) := ord_sc (ord_mem ord_om ht)
  obtain ⟨r, hrZ, hmin⟩ := ord_least Z (fun z hz => ord_mem hOsc ((hZ' z).mp hz).1)
    ⟨t, (hZ' t).mpr ⟨self_mem_sc t, hE.refl t ht⟩⟩
  obtain ⟨hrsc, hrt⟩ := (hZ' r).mp hrZ
  have hro := hsc r hrsc
  refine ⟨r, ⟨hro, fun t' ht' h => ?_⟩, hrt⟩
  have ht'sc : t' ∈ sc t := hOsc.1 r hrsc t' ht'
  have ht'o := hsc t' ht'sc
  rcases hmin t' ((hZ' t').mpr ⟨ht'sc, hE.trans t' r t ht'o hro ht h hrt⟩) with h' | h'
  · exact mem_irrefl t' (h' ▸ ht')
  · exact mem_asymm h' ht'

omit hE in
theorem rep_unique' (hE : EqOK S) {r r' : V} (hr : IsRep S r) (hr' : IsRep S r')
    (h : atm 1 r r' ∈ S) : r = r' := by
  rcases ord_tri (ord_mem ord_om hr.1) (ord_mem ord_om hr'.1) with h' | h' | h'
  · exact absurd h (hr'.2 r h')
  · exact h'
  · exact absurd (hE.symm r r' hr.1 hr'.1 h) (hr.2 r' h')

/-- **The least number of the class of `t`.** -/
noncomputable def repD (t : V) (ht : t ∈ (om : V)) : Dom S :=
  ⟨Classical.choose (exists_rep hE t ht), (Classical.choose_spec (exists_rep hE t ht)).1⟩

theorem repD_equiv (t : V) (ht : t ∈ (om : V)) : atm 1 (repD hE t ht).val t ∈ S :=
  (Classical.choose_spec (exists_rep hE t ht)).2

theorem repD_mem_om (t : V) (ht : t ∈ (om : V)) : (repD hE t ht).val ∈ (om : V) :=
  (repD hE t ht).2.1

theorem repD_eq_iff {t t' : V} (ht : t ∈ (om : V)) (ht' : t' ∈ (om : V)) :
    repD hE t ht = repD hE t' ht' ↔ atm 1 t t' ∈ S := by
  have h1 := repD_equiv hE t ht
  have h2 := repD_equiv hE t' ht'
  have o1 := repD_mem_om hE t ht
  have o2 := repD_mem_om hE t' ht'
  constructor
  · intro e
    rw [e] at h1
    exact hE.trans _ _ _ ht o2 ht' (hE.symm _ _ o2 ht h1) h2
  · intro h
    refine Subtype.ext (rep_unique' hE (repD hE t ht).2 (repD hE t' ht').2 ?_)
    exact hE.trans _ _ _ o1 ht o2 h1 (hE.trans _ _ _ ht ht' o2 h (hE.symm _ _ o2 ht' h2))

theorem repD_self (d : Dom S) : repD hE d.val d.2.1 = d :=
  Subtype.ext (rep_unique' hE (repD hE d.val d.2.1).2 d.2 (repD_equiv hE d.val d.2.1))

theorem repD_mem_iff {t t' : V} (ht : t ∈ (om : V)) (ht' : t' ∈ (om : V)) :
    repD hE t ht ∈ repD hE t' ht' ↔ atm 0 t t' ∈ S := by
  have h1 := repD_equiv hE t ht
  have h2 := repD_equiv hE t' ht'
  have o1 := repD_mem_om hE t ht
  have o2 := repD_mem_om hE t' ht'
  rw [dom_mem_iff]
  exact ⟨fun h => hE.cong _ _ _ _ o1 ht o2 ht' h1 h2 h,
    fun h => hE.cong _ _ _ _ ht o1 ht' o2 (hE.symm _ _ o1 ht h1) (hE.symm _ _ o2 ht' h2) h⟩

omit hE in
theorem tix_val {M : Type} [SetStructure M] {n : ℕ} (t : Semiterm ℒₛₑₜ Empty n) (v : Fin n → M) :
    t.val (M := M) v Empty.elim = v (tix t) := by
  match t with
  | #x => rfl
  | &x => exact Empty.elim x
  | .func f _ => exact Empty.elim f

/-- **A formula that is true under `S` is true in the structure of `S`.** -/
theorem holds_eval : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ) (e : Fin n → V)
    (he : ∀ i, e i ∈ (om : V)), Holds S φ c e →
      Eval (M := Dom S) (fun i ↦ repD hE (e i) (he i)) Empty.elim φ := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c e he _; trivial
  | hfalsum => intro c e he h; exact h.elim
  | hrel r v =>
    intro c e he h
    cases r with
    | eq =>
      show (v 0).val (M := Dom S) _ _ = (v 1).val (M := Dom S) _ _
      rw [tix_val, tix_val]
      exact (repD_eq_iff hE (he _) (he _)).mpr h
    | mem =>
      show (v 0).val (M := Dom S) _ _ ∈ (v 1).val (M := Dom S) _ _
      rw [tix_val, tix_val]
      exact (repD_mem_iff hE (he _) (he _)).mpr h
  | hnrel r v =>
    intro c e he h
    cases r with
    | eq =>
      show ¬(v 0).val (M := Dom S) _ _ = (v 1).val (M := Dom S) _ _
      rw [tix_val, tix_val]
      exact fun h' => h ((repD_eq_iff hE (he _) (he _)).mp h')
    | mem =>
      show ¬(v 0).val (M := Dom S) _ _ ∈ (v 1).val (M := Dom S) _ _
      rw [tix_val, tix_val]
      exact fun h' => h ((repD_mem_iff hE (he _) (he _)).mp h')
  | hand φ ψ ih1 ih2 => intro c e he h; exact ⟨ih1 c e he h.1, ih2 _ e he h.2⟩
  | hor φ ψ ih1 ih2 => intro c e he h; exact h.imp (ih1 c e he) (ih2 _ e he)
  | hall φ ih =>
    intro c e he h d
    have h' := ih c (d.val :> e) (cons_mem_om d.2.1 he) (h d.val d.2.1)
    have e1 : (fun i ↦ repD hE ((d.val :> e) i) (cons_mem_om d.2.1 he i)) =
        (d :> fun i ↦ repD hE (e i) (he i)) := by
      funext i
      cases i using Fin.cases with
      | zero => exact repD_self hE d
      | succ j => rfl
    rw [e1] at h'
    exact h'
  | hexs φ ih =>
    intro c e he h
    have hw := sk_mem_om c (tup_mem_om e he)
    have h' := ih _ (sk c (tup e) :> e) (cons_mem_om hw he) h
    have e1 : (fun i ↦ repD hE ((sk c (tup e) :> e) i) (cons_mem_om hw he i)) =
        (repD hE (sk c (tup e)) hw :> fun i ↦ repD hE (e i) (he i)) := by
      funext i
      cases i using Fin.cases with
      | zero => rfl
      | succ j => rfl
    rw [e1] at h'
    exact ⟨_, h'⟩

omit hE in
theorem dom_nonempty (hE : EqOK S) : Nonempty (Dom S) := ⟨repD hE ∅ empty_mem_om⟩

end model

end MH

end FFL.FirstOrder.SetTheory
