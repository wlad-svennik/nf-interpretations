module

public import MGraphH
public import MHRankZ

@[expose] public section

set_option autoImplicit false

/-!
# The rank axioms pass from a model of `𝗠` to its pointed graphs

Continues `MGraphH.lean`. `V` is a model of `𝗠`.

* `eval_isoG`: a formula has the same meaning in two structures with a membership relation
  that are isomorphic.
* `jX X a`, the class of the membership graph of a transitive set `X` pointed at `a`, is
  one-to-one on `X` (`jX_inj`) and preserves membership (`jX_mem_iff`); its values form a
  transitive set of `QG V` (`jX_tr`). So relations with a bounded definition hold of members
  of `X` in `V` exactly when they hold of their images in `QG V` (`jabs`).
* `sub_jX`: if `X` has the subsets of its members as members, every subset in `QG V` of the
  image of a member of `X` is the image of a member of `X`.
* **`hasRank_qg : HasRank n V → HasRank n (QG V)`**.
* **`consistent_mhr_of_consistent_mr : Con(𝗠 + rank axioms) → Con(𝗠𝗛𝗥)`**.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-! ### Isomorphic structures -/

section iso

variable {A B : Type} [SetStructure A] [SetStructure B]

lemma val_isoG (π : A → B) {ξ : Type*} {n : ℕ} (t : Semiterm ℒₛₑₜ ξ n) (e : Fin n → A)
    (ε : ξ → A) :
    t.val (M := B) (fun i ↦ π (e i)) (fun x ↦ π (ε x)) = π (t.val (M := A) e ε) := by
  match t with
  | #x => rfl
  | &x => rfl
  | .func f _ => exact Empty.elim f

/-- **A formula has the same meaning in isomorphic structures.** -/
theorem eval_isoG (π : A → B) (hsur : Function.Surjective π)
    (hmem : ∀ a a' : A, π a ∈ π a' ↔ a ∈ a') (heq : ∀ a a' : A, π a = π a' ↔ a = a')
    {ξ : Type*} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ξ n) (e : Fin n → A) (ε : ξ → A),
      Eval (M := B) (fun i ↦ π (e i)) (fun x ↦ π (ε x)) φ ↔ Eval (M := A) e ε φ := by
  have hcons : ∀ {n : ℕ} (a : A) (e : Fin n → A),
      (π a :> fun i ↦ π (e i)) = fun i ↦ π ((a :> e) i) := by
    intro n a e; funext i; cases i using Fin.cases <;> rfl
  have hrel : ∀ {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ξ n)
      (e : Fin n → A) (ε : ξ → A),
      Eval (M := B) (fun i ↦ π (e i)) (fun x ↦ π (ε x)) (Semiformula.rel r v) ↔
        Eval (M := A) e ε (Semiformula.rel r v) := by
    intro n k r v e ε
    cases r with
    | eq =>
      show ((v 0).val (M := B) _ _ = (v 1).val (M := B) _ _) ↔
        ((v 0).val (M := A) e ε = (v 1).val (M := A) e ε)
      rw [val_isoG, val_isoG]
      exact heq _ _
    | mem =>
      show ((v 0).val (M := B) _ _ ∈ (v 1).val (M := B) _ _) ↔
        ((v 0).val (M := A) e ε ∈ (v 1).val (M := A) e ε)
      rw [val_isoG, val_isoG]
      exact hmem _ _
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e ε; exact Iff.rfl
  | hfalsum => intro e ε; exact Iff.rfl
  | hrel r v => intro e ε; exact hrel r v e ε
  | hnrel r v =>
    intro e ε
    show Eval (M := B) _ _ (∼Semiformula.rel r v) ↔ Eval (M := A) _ _ (∼Semiformula.rel r v)
    simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
    exact not_congr (hrel r v e ε)
  | hand φ ψ ih1 ih2 =>
    intro e ε
    show Eval (M := B) _ _ (φ ⋏ ψ) ↔ Eval (M := A) _ _ (φ ⋏ ψ)
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
    rw [ih1 e ε, ih2 e ε]
  | hor φ ψ ih1 ih2 =>
    intro e ε
    show Eval (M := B) _ _ (φ ⋎ ψ) ↔ Eval (M := A) _ _ (φ ⋎ ψ)
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    rw [ih1 e ε, ih2 e ε]
  | hall φ ih =>
    intro e ε
    show Eval (M := B) _ _ (∀¹ φ) ↔ Eval (M := A) _ _ (∀¹ φ)
    rw [eval_all, eval_all]
    constructor
    · intro H a
      have h1 := H (π a)
      rw [hcons] at h1
      exact (ih _ ε).mp h1
    · intro H b
      obtain ⟨a, rfl⟩ := hsur b
      rw [hcons]
      exact (ih _ ε).mpr (H a)
  | hexs φ ih =>
    intro e ε
    show Eval (M := B) _ _ (∃¹ φ) ↔ Eval (M := A) _ _ (∃¹ φ)
    rw [eval_ex, eval_ex]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨a, rfl⟩ := hsur b
      rw [hcons] at hb
      exact ⟨a, (ih _ ε).mp hb⟩
    · rintro ⟨a, ha⟩
      refine ⟨π a, ?_⟩
      rw [hcons]
      exact (ih _ ε).mpr ha

end iso

/-- Relations with a bounded definition are absolute for the structure of the members of a
transitive set. -/
theorem bdef_tr {V : Type} [SetStructure V] {k : ℕ} {R : MRel k} (d : BDef R) {X : V}
    (hX : MH.Tr X) (v : Fin k → extSet X) : R (extSet X) v ↔ R V (fun i ↦ (v i : V)) := by
  have h1 := eval_submodel_iff (U := extSet X) (fun y hy z hz => hX y hy z hz) d.bdd v
    (Empty.elim)
  have e : (fun x : Empty ↦ ((Empty.elim x : extSet X) : V)) = (Empty.elim : Empty → V) :=
    funext fun x => x.elim
  rw [e] at h1
  exact (d.eval (extSet X) v).symm.trans (h1.trans (d.eval V _))

namespace MG

open MH

section defs

variable {V : Type} [SetStructure V]

/-- `⟨a, b⟩ ∈ B` for a member `b` of `X` other than `a`. -/
def DiffB (a X B : V) : Prop := ∃ b, b ∈ X ∧ (Pr B a b ∧ ¬a = b)

/-- `s` is a subset of a member of `X₀`. -/
def SubOf (s X₀ : V) : Prop := ∃ b, b ∈ X₀ ∧ ∀ z, z ∈ s → z ∈ b

end defs

def diffBB : BDef (k := 3) (fun V _ v ↦ DiffB (v 0) (v 1) (v 2)) :=
  (BDef.bex 1 ((prB.comp ![3, 1, 0]).and (BDef.eq 1 0).not)).congr fun _ _ _ => Iff.rfl

def subOfB : BDef (k := 2) (fun V _ v ↦ SubOf (v 0) (v 1)) :=
  (BDef.bex 1 (BDef.ball 1 (BDef.mem 0 1))).congr fun _ _ _ => Iff.rfl

section rank

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

/-! ### Sets of the model -/

/-- Transitive containment. -/
theorem m_tco (x : V) : ∃ t : V, (∀ z, z ∈ x → z ∈ t) ∧ Tr t := by
  have h : ∀ x : V, ∃ t : V, (∀ z ∈ x, z ∈ t) ∧ ∀ y ∈ t, ∀ z ∈ y, z ∈ t := by
    simpa [models_iff, Axiom.transitiveContainment, isSubsetOf] using
      Theory.models V 𝗠 (Or.inr rfl)
  obtain ⟨t, h1, h2⟩ := h x
  exact ⟨t, h1, fun y hy z hz => h2 y hy z hz⟩

/-- A transitive set with `a` and `b` as members that has the subsets of its members as
members. -/
theorem exists_supertr (a b : V) : ∃ X : V, Tr X ∧ (a ∈ X ∧ (b ∈ X ∧
    ∀ x, x ∈ X → ∀ w : V, (∀ z, z ∈ w → z ∈ x) → w ∈ X)) := by
  have hab : ∃ p : V, a ∈ p ∧ b ∈ p := ⟨{a, b}, by simp, by simp⟩
  obtain ⟨p, hap, hbp⟩ := hab
  obtain ⟨X₀, hsub, hX₀⟩ := m_tco p
  let X : V := sepB (k := 1) subOfB (℘ X₀) ![X₀]
  have h0 : ∀ s, s ∈ X ↔ s ∈ ℘ X₀ ∧ SubOf s X₀ := fun s => mem_sepB subOfB (℘ X₀) ![X₀] s
  have hXm : ∀ s, s ∈ X ↔ ∃ c, c ∈ X₀ ∧ ∀ z, z ∈ s → z ∈ c := fun s =>
    (h0 s).trans ⟨fun k => k.2, fun k => ⟨mem_power_iff.mpr fun z hz =>
      let ⟨c, hc, hs⟩ := k
      hX₀ c hc z (hs z hz), k⟩⟩
  have hin : ∀ c, c ∈ X₀ → c ∈ X := fun c hc => (hXm c).mpr ⟨c, hc, fun z hz => hz⟩
  refine ⟨X, fun y hy z hz => ?_, hin a (hsub a hap), hin b (hsub b hbp), fun x hx w hw => ?_⟩
  · obtain ⟨c, hc, hyc⟩ := (hXm y).mp hy
    exact hin z (hX₀ c hc z (hyc z hz))
  · obtain ⟨c, hc, hxc⟩ := (hXm x).mp hx
    exact (hXm w).mpr ⟨c, hc, fun z hz => hxc z (hw z hz)⟩

/-- The nodes of a graph whose edges are pairs of members of `A` are members of `A`. -/
theorem fld_sub {E A : V} (hE : ∀ e, e ∈ E → e ∈ prodS A A) : ∀ z, z ∈ fld E → z ∈ A := by
  intro z hz
  rw [fld] at hz
  obtain ⟨s, hs, hzs⟩ := mem_sUnion_iff.mp hz
  obtain ⟨e, he, hse⟩ := mem_sUnion_iff.mp hs
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_prodS.mp (hE e he)
  rcases mem_kp.mp hse with e1 | e1
  · rw [e1] at hzs
    rw [show z = a by simpa using hzs]
    exact ha
  · rw [e1] at hzs
    rcases (show z = a ∨ z = b by simpa using hzs) with e2 | e2
    · rw [e2]
      exact ha
    · rw [e2]
      exact hb

theorem numR_zero' : NumR (∅ : V) :=
  ⟨ord_empty, Or.inl fun z hz => absurd hz (by simp), fun y hy => absurd hy (by simp)⟩

theorem numR_sc' {a : V} (h : NumR a) : NumR (sc a) := by
  refine ⟨ord_sc h.1, Or.inr ⟨a, self_mem_sc a, succR_iff_sc.mpr rfl⟩, fun y hy => ?_⟩
  rcases mem_sc.mp hy with e | hy'
  · rw [e]
    exact h.2.1
  · exact h.2.2 y hy'

theorem vec1_mem {X a : V} (ha : a ∈ X) : ∀ i : Fin 1, (![a] : Fin 1 → V) i ∈ X := by
  intro i
  fin_cases i
  exact ha

theorem vec2_mem {X a b : V} (ha : a ∈ X) (hb : b ∈ X) :
    ∀ i : Fin 2, (![a, b] : Fin 2 → V) i ∈ X := by
  intro i
  fin_cases i
  · exact ha
  · exact hb

theorem vec3_mem {X a b c : V} (ha : a ∈ X) (hb : b ∈ X) (hc : c ∈ X) :
    ∀ i : Fin 3, (![a, b, c] : Fin 3 → V) i ∈ X := by
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc

/-! ### The membership graph of a transitive set -/

theorem gX_ok (X : V) : ∀ c x, Pr (EX X) c x → c ∈ X ∧ x ∈ X :=
  fun _ _ h => ⟨(pr_EX.mp h).1, (pr_EX.mp h).2.1⟩

theorem fld_EX (X : V) : ∀ c, c ∈ fld (EX X) → c ∈ X :=
  fld_sub fun _ he => relB_sub (BDef.mem 0 1) X X ![] he

/-- **A bisimulation of the membership graph of a transitive set with itself relates only
equal members.** -/
theorem bis_ex_eq {X : V} (hX : Tr X) {B : V} (hB : IsBisG B (EX X) (EX X)) :
    ∀ a b, a ∈ X → b ∈ X → Pr B a b → a = b := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨a₀, b₀, ha₀, hb₀, hab₀, hne₀⟩ := hcon
  let D : V := sepB (k := 2) diffBB X ![X, B]
  have hD : ∀ a, a ∈ D ↔ a ∈ X ∧ DiffB a X B := fun a => mem_sepB diffBB X ![X, B] a
  obtain ⟨a, haD, hmin⟩ := m_found D ⟨a₀, (hD a₀).mpr ⟨ha₀, b₀, hb₀, hab₀, hne₀⟩⟩
  obtain ⟨ha, b, hb, hab, hne⟩ := (hD a).mp haD
  obtain ⟨f, g⟩ := isBisG_iff.mp hB a b hab
  apply hne
  refine mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · have hzX : z ∈ X := hX a ha z hz
    obtain ⟨z', hz', hzz'⟩ := f z (pr_EX.mpr ⟨hzX, ha, hz⟩)
    have hz'X : z' ∈ X := (pr_EX.mp hz').1
    have e : z = z' := by
      by_contra hne'
      exact hmin z ((hD z).mpr ⟨hzX, z', hz'X, hzz', hne'⟩) hz
    rw [e]
    exact (pr_EX.mp hz').2.2
  · have hzX : z ∈ X := hX b hb z hz
    obtain ⟨z₁, hz₁, hzz⟩ := g z (pr_EX.mpr ⟨hzX, hb, hz⟩)
    have hz₁X : z₁ ∈ X := (pr_EX.mp hz₁).1
    have e : z₁ = z := by
      by_contra hne'
      exact hmin z₁ ((hD z₁).mpr ⟨hz₁X, z, hzX, hzz, hne'⟩) (pr_EX.mp hz₁).2.2
    rw [← e]
    exact (pr_EX.mp hz₁).2.2

/-- **`jX X` is one-to-one on a transitive set `X`.** -/
theorem jX_inj {X a b : V} (hX : Tr X) (ha : a ∈ X) (hb : b ∈ X) (h : jX X a = jX X b) :
    a = b := by
  have h' : Bis (EX X) a (EX X) b := mkQ_eq.mp h
  obtain ⟨B, hB, hab⟩ := h'
  exact bis_ex_eq hX hB a b ha hb hab

/-- **`jX X` preserves membership** between the members of a transitive set `X`. -/
theorem jX_mem_iff {X a b : V} (hX : Tr X) (ha : a ∈ X) (hb : b ∈ X) :
    jX X a ∈ jX X b ↔ a ∈ b := by
  rw [mem_jX hX hb]
  constructor
  · rintro ⟨c, hc, e⟩
    rw [jX_inj hX ha (hX b hb c hc) e]
    exact hc
  · intro h
    exact ⟨a, h, rfl⟩

/-- The class whose members are the classes `jX X a` for `a ∈ X`. -/
noncomputable def JX (X : V) : QG V := mkS (gX X X) X (gX_ok X) X

theorem mem_JX {X : V} {x : QG V} : x ∈ JX X ↔ ∃ a, a ∈ X ∧ x = jX X a :=
  mem_mkS (gX X X) X (gX_ok X) (fun _ h => h)

theorem jX_tr {X : V} (hX : Tr X) : Tr (JX X) := by
  intro y hy z hz
  obtain ⟨b, hb, rfl⟩ := mem_JX.mp hy
  obtain ⟨a, ha, rfl⟩ := (mem_jX hX hb).mp hz
  exact mem_JX.mpr ⟨a, hX b hb a ha, rfl⟩

/-- **Relations with a bounded definition hold of members of a transitive set `X` exactly
when they hold of their images in `QG V`.** -/
theorem jabs {k : ℕ} {R : MRel k} (d : BDef R) {X : V} (hX : Tr X) (v : Fin k → V)
    (hv : ∀ i, v i ∈ X) : R (QG V) (fun i ↦ jX X (v i)) ↔ R V v := by
  let π : extSet X → extSet (JX X) := fun a =>
    ⟨jX X (a : V), show jX X (a : V) ∈ JX X from mem_JX.mpr ⟨(a : V), a.2, rfl⟩⟩
  have hsur : Function.Surjective π := by
    intro u
    obtain ⟨a, ha, e⟩ := mem_JX.mp u.2
    exact ⟨⟨a, ha⟩, Subtype.ext e.symm⟩
  have hmem : ∀ a a' : extSet X, π a ∈ π a' ↔ a ∈ a' := fun a a' => jX_mem_iff hX a.2 a'.2
  have heq : ∀ a a' : extSet X, π a = π a' ↔ a = a' := fun a a' =>
    ⟨fun h => Subtype.ext (jX_inj hX a.2 a'.2 (congrArg Subtype.val h)), fun h => by rw [h]⟩
  let v' : Fin k → extSet X := fun i => ⟨v i, hv i⟩
  have h1 : R (extSet X) v' ↔ R V v := bdef_tr d hX v'
  have h3 : R (extSet (JX X)) (fun i ↦ π (v' i)) ↔ R (QG V) (fun i ↦ jX X (v i)) :=
    bdef_tr d (jX_tr hX) _
  have h2 := eval_isoG π hsur hmem heq d.φ v' Empty.elim
  have e : (fun x : Empty ↦ π (Empty.elim x)) = (Empty.elim : Empty → extSet (JX X)) :=
    funext fun x => x.elim
  rw [e] at h2
  exact h3.symm.trans (((d.eval (extSet (JX X)) _).symm.trans
    (h2.trans (d.eval (extSet X) v'))).trans h1)

theorem jX_empty {X : V} (hX : Tr X) (h0 : (∅ : V) ∈ X) : jX X ∅ = (∅ : QG V) := by
  refine qg_ext _ _ fun z => ⟨fun hz => ?_, fun hz => absurd hz (by simp)⟩
  obtain ⟨a, ha, -⟩ := (mem_jX hX h0).mp hz
  exact absurd ha (by simp)

theorem jX_sc {X a : V} (hX : Tr X) (hs : sc a ∈ X) : jX X (sc a) = sc (jX X a) := by
  have ha : a ∈ X := hX _ hs a (self_mem_sc a)
  refine qg_ext _ _ fun z => ⟨fun hz => ?_, fun hz => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := (mem_jX hX hs).mp hz
    rcases mem_sc.mp hc with e | hc'
    · exact mem_sc.mpr (Or.inl (by rw [e]))
    · exact mem_sc.mpr (Or.inr ((mem_jX hX ha).mpr ⟨c, hc', rfl⟩))
  · rcases mem_sc.mp hz with e | hz'
    · exact (mem_jX hX hs).mpr ⟨a, self_mem_sc a, e⟩
    · obtain ⟨c, hc, rfl⟩ := (mem_jX hX ha).mp hz'
      exact (mem_jX hX hs).mpr ⟨c, mem_sc.mpr (Or.inr hc), rfl⟩

/-- **Every subset in `QG V` of the image of a member of `X` is the image of a member of
`X`**, when `X` is transitive and has the subsets of its members as members. -/
theorem sub_jX {X x : V} (hX : Tr X)
    (hsub : ∀ x, x ∈ X → ∀ w : V, (∀ z, z ∈ w → z ∈ x) → w ∈ X) (hx : x ∈ X) (z : QG V)
    (hz : ∀ w, w ∈ z → w ∈ jX X x) : ∃ z₀, (∀ c, c ∈ z₀ → c ∈ x) ∧ z = jX X z₀ := by
  obtain ⟨gz, rfl⟩ := exists_rep z
  let P : V := ℘ (prodS X (nodes gz))
  let z₀ : V := sepB (k := 4) memChB x ![P, EX X, gz.E, gz.p]
  have h0 : ∀ c, c ∈ z₀ ↔ c ∈ x ∧ MemCh c P (EX X) gz.E gz.p :=
    fun c => mem_sepB memChB x ![P, EX X, gz.E, gz.p] c
  have hz₀ : ∀ c, c ∈ z₀ ↔ c ∈ x ∧ jX X c ∈ mkQ gz := by
    intro c
    rw [h0]
    refine and_congr_right fun hc => ?_
    have h1 : (∃ d, Pr gz.E d gz.p ∧ Bis (EX X) c gz.E d) ↔ jX X c ∈ mkQ gz := Iff.rfl
    exact (memCh_iff' (fld_EX X) (hX x hx c hc) (fld_sub_nodes gz)).trans h1
  have hz₀x : ∀ c, c ∈ z₀ → c ∈ x := fun c hc => ((hz₀ c).mp hc).1
  have hz₀X : z₀ ∈ X := hsub x hx z₀ hz₀x
  refine ⟨z₀, hz₀x, qg_ext _ _ fun w => ?_⟩
  rw [mem_jX hX hz₀X]
  constructor
  · intro hw
    obtain ⟨c, hc, rfl⟩ := (mem_jX hX hx).mp (hz w hw)
    exact ⟨c, (hz₀ c).mpr ⟨hc, hw⟩, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ((hz₀ c).mp hc).2

/-- **The pairs in the image of a member of `X`** are the images of its pairs. -/
theorem pr_jX {X h : V} (hX : Tr X) (hh : h ∈ X) {a b : QG V} :
    Pr (jX X h) a b ↔
      ∃ α x, α ∈ X ∧ (x ∈ X ∧ (Pr h α x ∧ (a = jX X α ∧ b = jX X x))) := by
  constructor
  · rintro ⟨p, hp, hop⟩
    obtain ⟨e, he, rfl⟩ := (mem_jX hX hh).mp hp
    have heX : e ∈ X := hX h hh e he
    obtain ⟨u, hu, hau⟩ := pr_fst_mem hop
    obtain ⟨u₀, hu₀, rfl⟩ := (mem_jX hX heX).mp hu
    have hu₀X : u₀ ∈ X := hX e heX u₀ hu₀
    obtain ⟨α, hα, rfl⟩ := (mem_jX hX hu₀X).mp hau
    obtain ⟨d, hd, hbd⟩ := pr_snd_mem hop
    obtain ⟨d₀, hd₀, rfl⟩ := (mem_jX hX heX).mp hd
    have hd₀X : d₀ ∈ X := hX e heX d₀ hd₀
    obtain ⟨x, hx, rfl⟩ := (mem_jX hX hd₀X).mp hbd
    have hαX : α ∈ X := hX u₀ hu₀X α hα
    have hxX : x ∈ X := hX d₀ hd₀X x hx
    have habs : IsOp (jX X e) (jX X α) (jX X x) ↔ IsOp e α x :=
      jabs isOpB hX ![e, α, x] (vec3_mem heX hαX hxX)
    exact ⟨α, x, hαX, hxX, ⟨e, he, habs.mp hop⟩, rfl, rfl⟩
  · rintro ⟨α, x, hαX, hxX, ⟨e, he, hop⟩, rfl, rfl⟩
    have heX : e ∈ X := hX h hh e he
    have habs : IsOp (jX X e) (jX X α) (jX X x) ↔ IsOp e α x :=
      jabs isOpB hX ![e, α, x] (vec3_mem heX hαX hxX)
    exact ⟨jX X e, (mem_jX hX hh).mpr ⟨e, he, rfl⟩, habs.mpr hop⟩

/-! ### The rank axioms -/

/-- **A rank axiom that holds in `V` holds in the pointed graphs of `V`.** -/
theorem hasRank_qg {n : ℕ} (hR : HasRank n V) : HasRank n (QG V) := by
  obtain ⟨h, θ, hθ, H, k, hk, hkθ, w, hw, hno⟩ := hR
  obtain ⟨hfn, htot, hzero, hsucc, hlim⟩ := H
  obtain ⟨X, hX, hhX, hθX, hsub⟩ := exists_supertr h θ
  have hpr : ∀ α x, Pr h α x → α ∈ X ∧ x ∈ X := by
    intro α x hp
    have h1 : kp α x ∈ X := hX h hhX _ (pr_iff.mp hp)
    have h2 : ({α, x} : V) ∈ kp α x := mem_kp.mpr (Or.inr rfl)
    have h3 : ({α, x} : V) ∈ X := hX _ h1 _ h2
    have h4 : α ∈ ({α, x} : V) := by simp
    have h5 : x ∈ ({α, x} : V) := by simp
    exact ⟨hX _ h3 α h4, hX _ h3 x h5⟩
  have hP : ∀ a b : QG V, Pr (jX X h) a b ↔
      ∃ α x, α ∈ X ∧ (x ∈ X ∧ (Pr h α x ∧ (a = jX X α ∧ b = jX X x))) :=
    fun a b => pr_jX hX hhX
  have hPi : ∀ α x, Pr h α x → Pr (jX X h) (jX X α) (jX X x) := fun α x hp =>
    (hP _ _).mpr ⟨α, x, (hpr α x hp).1, (hpr α x hp).2, hp, rfl, rfl⟩
  have hmem : ∀ {a : V}, a ∈ X → ∀ y : QG V, y ∈ jX X a ↔ ∃ c, c ∈ a ∧ y = jX X c :=
    fun ha y => mem_jX hX ha
  have hkX : k ∈ X := hX θ hθX k hkθ
  have hwX : w ∈ X := (hpr k w hw).2
  have hle : ∀ α : QG V, (α ∈ jX X θ ∨ α = jX X θ) →
      ∃ α₀, (α₀ ∈ θ ∨ α₀ = θ) ∧ α = jX X α₀ := by
    rintro α (hα | hα)
    · obtain ⟨α₀, h0, e⟩ := (hmem hθX α).mp hα
      exact ⟨α₀, Or.inl h0, e⟩
    · exact ⟨θ, Or.inr rfl, hα⟩
  refine ⟨jX X h, jX X θ, (jabs ordB hX ![θ] (vec1_mem hθX)).mpr hθ, ⟨?_, ?_, ?_, ?_, ?_⟩,
    jX X k, (jabs (isNumB n) hX ![k] (vec1_mem hkX)).mpr hk, (jX_mem_iff hX hkX hθX).mpr hkθ,
    jX X w, hPi k w hw, ?_⟩
  · -- the hierarchy is a function
    intro α x x' h1 h2
    obtain ⟨α₀, x₀, hα₀, hx₀, hp, e1, e2⟩ := (hP _ _).mp h1
    obtain ⟨α₁, x₁, hα₁, hx₁, hp', e1', e2'⟩ := (hP _ _).mp h2
    have e := jX_inj hX hα₀ hα₁ (e1.symm.trans e1')
    rw [← e] at hp'
    rw [e2, e2', hfn α₀ x₀ x₁ hp hp']
  · -- it is defined up to `θ`
    intro α hα
    obtain ⟨α₀, h0, e⟩ := hle α hα
    obtain ⟨x₀, hp⟩ := htot α₀ h0
    rw [e]
    exact ⟨jX X x₀, hPi α₀ x₀ hp⟩
  · -- the value at zero
    intro α x hp hemp z
    obtain ⟨α₀, x₀, hα₀, hx₀, hp₀, e1, e2⟩ := (hP _ _).mp hp
    have hemp₀ : ∀ c, ¬c ∈ α₀ := fun c hc =>
      hemp (jX X c) (by rw [e1]; exact (hmem hα₀ _).mpr ⟨c, hc, rfl⟩)
    have hz₀ : ∀ c, c ∈ x₀ ↔ NumR c := hzero α₀ x₀ hp₀ hemp₀
    rw [e2]
    constructor
    · intro hz
      obtain ⟨c, hc, e⟩ := (hmem hx₀ z).mp hz
      rw [e]
      exact (jabs numB hX ![c] (vec1_mem (hX x₀ hx₀ c hc))).mpr ((hz₀ c).mp hc)
    · intro hz
      have hzom : z ∈ (om : QG V) := numR_iff.mp hz
      have h0x : (∅ : V) ∈ x₀ := (hz₀ ∅).mpr numR_zero'
      have hbase : (∅ : QG V) ∈ jX X x₀ :=
        (hmem hx₀ _).mpr ⟨∅, h0x, (jX_empty hX (hX x₀ hx₀ ∅ h0x)).symm⟩
      have hstep : ∀ m : QG V, m ∈ (om : QG V) → m ∈ jX X x₀ → sc m ∈ jX X x₀ := by
        intro m _ ih
        obtain ⟨c, hc, e⟩ := (hmem hx₀ m).mp ih
        have hsc : sc c ∈ x₀ := (hz₀ _).mpr (numR_sc' ((hz₀ c).mp hc))
        rw [e]
        exact (hmem hx₀ _).mpr ⟨sc c, hsc, (jX_sc hX (hX x₀ hx₀ _ hsc)).symm⟩
      exact om_ind (V := QG V) (k := 1) (BDef.mem 0 1) ![jX X x₀] hbase hstep z hzom
  · -- the value at a successor
    intro α β x y hα hsc hpx hpy z
    obtain ⟨α₀, x₀, hα₀, hx₀, hp₀, e1, e2⟩ := (hP _ _).mp hpx
    obtain ⟨β₀, y₀, hβ₀, hy₀, hq₀, e3, e4⟩ := (hP _ _).mp hpy
    rw [e1] at hα hsc
    rw [e3] at hsc
    have hα₀θ : α₀ ∈ θ := (jX_mem_iff hX hα₀ hθX).mp hα
    have hsc₀ : SuccR β₀ α₀ := (jabs succB hX ![β₀, α₀] (vec2_mem hβ₀ hα₀)).mp hsc
    have hK : ∀ z₀, z₀ ∈ y₀ ↔ ∀ c, c ∈ z₀ → c ∈ x₀ := hsucc α₀ β₀ x₀ y₀ hα₀θ hsc₀ hp₀ hq₀
    rw [e2, e4]
    constructor
    · intro hz w hw
      obtain ⟨z₀, hz₀, e⟩ := (hmem hy₀ z).mp hz
      rw [e] at hw
      obtain ⟨c, hc, e'⟩ := (hmem (hX y₀ hy₀ z₀ hz₀) w).mp hw
      exact (hmem hx₀ w).mpr ⟨c, (hK z₀).mp hz₀ c hc, e'⟩
    · intro hz
      obtain ⟨z₀, hz₀, e⟩ := sub_jX hX hsub hx₀ z hz
      exact (hmem hy₀ z).mpr ⟨z₀, (hK z₀).mpr hz₀, e⟩
  · -- the value at a limit
    intro β y hβ hlimβ hpy z
    obtain ⟨β₀, y₀, hβ₀, hy₀, hq₀, e1, e2⟩ := (hP _ _).mp hpy
    rw [e1] at hβ hlimβ
    have hβ₀θ : β₀ ∈ θ ∨ β₀ = θ := by
      rcases hβ with hβ | hβ
      · exact Or.inl ((jX_mem_iff hX hβ₀ hθX).mp hβ)
      · exact Or.inr (jX_inj hX hβ₀ hθX hβ)
    have hlim₀ : LimR β₀ := by
      obtain ⟨⟨c, hc⟩, hs⟩ := hlimβ
      obtain ⟨c₀, hc₀, -⟩ := (hmem hβ₀ c).mp hc
      refine ⟨⟨c₀, hc₀⟩, fun α₀ hα₀ => ?_⟩
      obtain ⟨α', hα', hsc⟩ := hs (jX X α₀) ((hmem hβ₀ _).mpr ⟨α₀, hα₀, rfl⟩)
      obtain ⟨α₁, hα₁, e⟩ := (hmem hβ₀ α').mp hα'
      rw [e] at hsc
      exact ⟨α₁, hα₁, (jabs succB hX ![α₁, α₀]
        (vec2_mem (hX β₀ hβ₀ α₁ hα₁) (hX β₀ hβ₀ α₀ hα₀))).mp hsc⟩
    have hK : ∀ z₀, z₀ ∈ y₀ ↔ ∃ α, α ∈ β₀ ∧ ∃ x, Pr h α x ∧ z₀ ∈ x :=
      hlim β₀ y₀ hβ₀θ hlim₀ hq₀
    rw [e1, e2]
    constructor
    · intro hz
      obtain ⟨z₀, hz₀, e⟩ := (hmem hy₀ z).mp hz
      obtain ⟨α₀, hα₀, x₀, hp₀, hzx⟩ := (hK z₀).mp hz₀
      exact ⟨jX X α₀, (hmem hβ₀ _).mpr ⟨α₀, hα₀, rfl⟩, jX X x₀, hPi α₀ x₀ hp₀,
        (hmem (hpr α₀ x₀ hp₀).2 z).mpr ⟨z₀, hzx, e⟩⟩
    · rintro ⟨α, hα, x, hpx, hzx⟩
      obtain ⟨α₀, hα₀, e⟩ := (hmem hβ₀ α).mp hα
      obtain ⟨α₁, x₀, hα₁, hx₀, hp₀, e', e''⟩ := (hP _ _).mp hpx
      have e3 : α₀ = α₁ := jX_inj hX (hX β₀ hβ₀ α₀ hα₀) hα₁ (e.symm.trans e')
      rw [← e3] at hp₀
      rw [e''] at hzx
      obtain ⟨z₀, hz₀, e4⟩ := (hmem hx₀ z).mp hzx
      exact (hmem hy₀ z).mpr ⟨z₀, (hK z₀).mpr ⟨α₀, hα₀, x₀, hp₀, hz₀⟩, e4⟩
  · -- `θ` does not map one-to-one into the value at `n`
    rintro ⟨f, hf1, hf2⟩
    apply hno
    obtain ⟨ρ, -, hρ⟩ := exists_rho (gX X X) X (gX_ok X) X (fun _ hc => hc) f
    have hρ' : ∀ a b, Pr ρ a b ↔ a ∈ X ∧ (b ∈ X ∧ Pr f (jX X a) (jX X b)) := hρ
    refine ⟨ρ, fun u hu => ?_, fun u u' v hu hu' h1 h2 => ?_⟩
    · have huX : u ∈ X := hX θ hθX u hu
      obtain ⟨v', hv', hrl⟩ := hf1 (jX X u) ((hmem hθX _).mpr ⟨u, hu, rfl⟩)
      obtain ⟨v, hv, e⟩ := (hmem hwX v').mp hv'
      rw [e] at hrl
      have hvX : v ∈ X := hX w hwX v hv
      have h1 : Pr f (jX X u) (jX X v) := pr_iff.mpr (hin_rl_iff.mp hrl)
      exact ⟨v, hv, hin_rl_iff'.mpr (pr_iff.mp ((hρ' u v).mpr ⟨huX, hvX, h1⟩))⟩
    · have h1' := (hρ' u v).mp (pr_iff.mpr (hin_rl_iff'.mp h1))
      have h2' := (hρ' u' v).mp (pr_iff.mpr (hin_rl_iff'.mp h2))
      have e := hf2 (jX X u) (jX X u') (jX X v) ((hmem hθX _).mpr ⟨u, hu, rfl⟩)
        ((hmem hθX _).mpr ⟨u', hu', rfl⟩) (hin_rl_iff.mpr (pr_iff.mp h1'.2.2))
        (hin_rl_iff.mpr (pr_iff.mp h2'.2.2))
      exact jX_inj hX h1'.1 h2'.1 e

end rank

end MG

/-! ### The theory and the consistency statement -/

/-- Mathias's `𝗠` with the rank axioms for every `n`. -/
abbrev MathiasMRanks : SetTheory := 𝗠 ∪ Set.range Axiom.rank

@[inherit_doc] notation "𝗠𝗥" => MathiasMRanks

instance : 𝗘𝗤 _ ⪯ 𝗠𝗥 :=
  let : 𝗘𝗤 _ ⪯ 𝗠 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

/-- **The pointed graphs of a model of `𝗠` with the rank axioms are a model of `𝗠𝗛𝗥`.** -/
theorem qg_models_mhr {M : Type} [SetStructure M] [Nonempty M] (hTR : M↓[ℒₛₑₜ] ⊧* 𝗠𝗥) :
    haveI : M↓[ℒₛₑₜ] ⊧* 𝗠 :=
      models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hTR φ (Or.inl hφ)
    (MG.QG M)↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗥 := by
  have hM : M↓[ℒₛₑₜ] ⊧* 𝗠 :=
    models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hTR φ (Or.inl hφ)
  have hr : ∀ n, MH.HasRank n M := fun n =>
    models_rank_iff.mp (models_theory_iff.mp hTR _ (Or.inr ⟨n, rfl⟩))
  exact models_mhr_of MG.qgModelsMH fun n => MG.hasRank_qg (hr n)

/-- **If `𝗠` with the rank axioms is consistent, so is `𝗠𝗛` with the rank axioms.** -/
theorem consistent_mhr_of_consistent_mr (h : Entailment.Consistent 𝗠𝗥) :
    Entailment.Consistent 𝗠𝗛𝗥 := by
  by_contra hU
  refine Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable ?_) h
  apply SetTheory.complete.{0}
  intro M _ _ hTR
  exfalso
  apply hU
  have hM : M↓[ℒₛₑₜ] ⊧* 𝗠 :=
    models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hTR φ (Or.inl hφ)
  have : (MG.QG M)↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗥 := qg_models_mhr hTR
  exact consistent_of_model 𝗠𝗛𝗥 (MG.QG M)

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MG.jabs
#print axioms FFL.FirstOrder.SetTheory.MG.hasRank_qg
#print axioms FFL.FirstOrder.SetTheory.qg_models_mhr
#print axioms FFL.FirstOrder.SetTheory.consistent_mhr_of_consistent_mr
