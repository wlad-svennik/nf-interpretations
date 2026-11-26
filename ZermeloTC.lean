module

public import MGraphRank
public import Foundation.FirstOrder.SetTheory.Ordinal

@[expose] public section

set_option autoImplicit false

/-!
# From Zermelo set theory to `𝗠`: the sets included in a transitive set

`𝗭` does not have transitive containment as an axiom. In a model `K` of `𝗭`, let `WT K` be the
collection of the sets that are included in a transitive set.

* `isMacBase_wt`, **`wtModelsM : (WT K) ⊧ 𝗠`**. Separation is needed only in the structures of
  the members of a set, and there it comes from separation in `K` for a formula with all
  quantifiers bounded by that set (`rlv`).
* `val_tr`: the values of the hierarchy of a rank axiom are transitive. The induction uses
  separation in `K` for a formula that is not bounded; the case distinction on an ordinal
  (empty, successor, limit) is made in the model `WT K` of `𝗠` (`z_ord_cases`).
* **`hasRank_wt : HasRank n K → HasRank n (WT K)`**, with the hierarchy cut down to its pairs.
* **`consistent_mr_of_consistent_zr : Con(𝗭𝗥) → Con(𝗠𝗥)`**.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-- Relations with a bounded definition are absolute for a transitive collection. -/
theorem bdef_sub {V : Type} [SetStructure V] {U : Set V} (hU : ∀ y ∈ U, ∀ z ∈ y, z ∈ U)
    {k : ℕ} {R : MRel k} (d : BDef R) (v : Fin k → U) :
    R U v ↔ R V (fun i ↦ (v i : V)) := by
  have h1 := eval_submodel_iff (U := U) hU d.bdd v (Empty.elim)
  have e : (fun x : Empty ↦ ((Empty.elim x : U) : V)) = (Empty.elim : Empty → V) :=
    funext fun x => x.elim
  rw [e] at h1
  exact (d.eval U v).symm.trans (h1.trans (d.eval V _))

namespace ZT

open MH

section defs

variable {V : Type} [SetStructure V]

/-- `x` is included in a transitive set. -/
def InTr (x : V) : Prop := ∃ t : V, Tr t ∧ ∀ z, z ∈ x → z ∈ t

/-- `p = ⟨α, x⟩` for an `α` that is a member of `θ` or `θ`. -/
def GoodP (p θ : V) : Prop :=
  ∃ d, d ∈ p ∧ ∃ α, α ∈ d ∧ ∃ x, x ∈ d ∧ (IsOp p α x ∧ (α ∈ θ ∨ α = θ))

theorem inTr_mem {x y : V} (hx : InTr x) (hy : y ∈ x) : InTr y :=
  let ⟨t, ht, h⟩ := hx
  ⟨t, ht, fun z hz => ht y (h y hy) z hz⟩

theorem inTr_of_tr {t : V} (ht : Tr t) : InTr t := ⟨t, ht, fun _ h => h⟩

theorem numR_mem {y z : V} (hy : NumR y) (hz : z ∈ y) : NumR z :=
  ⟨ord_mem hy.1 hz, hy.2.2 z hz, fun u hu => hy.2.2 u (hy.1.1 z hz u hu)⟩

end defs

/-- The sets that are included in a transitive set. -/
def WT (V : Type) [SetStructure V] : Set V := {x | InTr x}

theorem wt_tr {V : Type} [SetStructure V] : ∀ y ∈ WT V, ∀ z ∈ y, z ∈ WT V :=
  fun _ hy _ hz => inTr_mem hy hz

def goodPB : BDef (k := 2) (fun V _ v ↦ GoodP (v 0) (v 1)) :=
  (BDef.bex 0 (BDef.bex 0 (BDef.bex 1 ((isOpB.comp ![3, 1, 0]).and
    ((BDef.mem 1 4).or (BDef.eq 1 4)))))).congr fun _ _ _ => Iff.rfl

/-- Some value of `h` at `α` is not transitive. -/
def badVF : FDef (k := 2) (fun V _ v ↦ ∃ x, Pr (v 1) (v 0) x ∧ ¬Tr x) :=
  (FDef.ex (((prB.comp ![2, 1, 0]).toFDef).and ((trB.comp ![0]).not.toFDef))).congr
    fun _ _ _ => Iff.rfl

/-- In a model of `𝗠`, an ordinal is empty, a successor or a limit. -/
theorem ord_cases' {M : Type} [SetStructure M] [Nonempty M] [M↓[ℒₛₑₜ] ⊧* 𝗠] {α : M}
    (hα : MH.Ord α) : (∀ z, z ∉ α) ∨ ((∃ γ, γ ∈ α ∧ SuccR α γ) ∨ LimR α) := by
  by_cases h1 : ∃ z, z ∈ α
  · by_cases h2 : ∀ γ, γ ∈ α → ∃ γ', γ' ∈ α ∧ SuccR γ' γ
    · exact Or.inr (Or.inr ⟨h1, h2⟩)
    · push_neg at h2
      obtain ⟨γ, hγ, hno⟩ := h2
      rcases ord_sc_le (ord_mem hα hγ) hα hγ with e | e
      · exact Or.inr (Or.inl ⟨γ, hγ, succR_iff_sc.mpr e.symm⟩)
      · exact absurd (succR_iff_sc.mpr rfl) (hno (sc γ) e)
  · exact Or.inl fun z hz => h1 ⟨z, hz⟩

section zmodel

variable {K : Type} [SetStructure K] [Nonempty K] [hZ : K↓[ℒₛₑₜ] ⊧* 𝗭]

/-! ### Separation and foundation in a model of `𝗭` -/

theorem z_sep_raw (ψ : SetTheorySemiproposition 1) (ε : ℕ → K) (a : K) :
    ∃ y : K, ∀ z, z ∈ y ↔ z ∈ a ∧ Eval (M := K) ![z] ε ψ := by
  have := by
    simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema,
      Matrix.constant_eq_singleton] using
      Theory.models K 𝗭 (Or.inr (Separation.separation ψ))
  exact this ε a

/-- **Separation** for a relation with a definition, bounded or not. -/
theorem z_sep {k : ℕ} {R : MRel (k + 1)} (d : FDef R) (a : K) (p : Fin k → K) :
    ∃ y : K, ∀ z, z ∈ y ↔ z ∈ a ∧ R K (z :> p) := by
  classical
  let rw0 : Rew ℒₛₑₜ Empty (k + 1) ℕ 1 :=
    Rew.bind ((#0 : Semiterm ℒₛₑₜ ℕ 1) :> fun i : Fin k ↦ &(i : ℕ)) Empty.elim
  let x₀ : K := Classical.arbitrary K
  obtain ⟨y, hy⟩ := z_sep_raw (rw0 ▹ d.φ) (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) a
  refine ⟨y, fun z => (hy z).trans (and_congr Iff.rfl ?_)⟩
  have e : (Semiterm.val ![z] (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) ∘ rw0 ∘
      Semiterm.bvar) = (z :> p) := by
    funext i
    cases i using Fin.cases with
    | zero => simp [rw0]
    | succ i => simp [rw0]
  have e2 : (Semiterm.val ![z] (fun n ↦ if h : n < k then p ⟨n, h⟩ else x₀) ∘ rw0 ∘
      Semiterm.fvar) = (Empty.elim : Empty → K) := funext fun z => z.elim
  rw [eval_rew, e, e2]
  exact d.eval K _

theorem z_found (x : K) (h : ∃ y, y ∈ x) : ∃ y ∈ x, ∀ z ∈ x, z ∉ y := by
  have := by
    simpa [models_iff, isNonempty_def] using
      Theory.models K 𝗭 (Or.inl BasicSetTheory.foundation)
  obtain ⟨y, hy⟩ := h
  exact this x y hy

/-! ### The pairs of `AlephTheory.lean` in a model of `𝗭` -/

theorem z_hin_isOp {p a b : K} : Hin.IsOp p a b ↔ IsOp p a b := by
  have s1 : ∀ {u a : K}, Hin.IsSing u a ↔ IsSing u a := fun {u a} =>
    ⟨fun h => ⟨(h a).mpr rfl, fun c hc => (h c).mp hc⟩,
      fun h c => ⟨h.2 c, fun e => by rw [e]; exact h.1⟩⟩
  have s2 : ∀ {u a b : K}, Hin.IsUp u a b ↔ IsUp u a b := fun {u a b} =>
    ⟨fun h => ⟨(h a).mpr (Or.inl rfl), (h b).mpr (Or.inr rfl), fun c hc => (h c).mp hc⟩,
      fun h c => ⟨h.2.2 c, fun e => by
        rcases e with e | e
        · rw [e]; exact h.1
        · rw [e]; exact h.2.1⟩⟩
  constructor
  · intro H
    obtain ⟨sa, hsa⟩ : ∃ s : K, ∀ c, c ∈ s ↔ c = a := ⟨{a}, fun c => by simp⟩
    obtain ⟨da, hda⟩ : ∃ s : K, ∀ c, c ∈ s ↔ c = a ∨ c = b := ⟨{a, b}, fun c => by simp⟩
    have hs : Hin.IsSing sa a := hsa
    have hd : Hin.IsUp da a b := hda
    exact ⟨⟨sa, (H sa).mpr (Or.inl hs), s1.mp hs⟩, ⟨da, (H da).mpr (Or.inr hd), s2.mp hd⟩,
      fun z hz => ((H z).mp hz).imp s1.mp s2.mp⟩
  · rintro ⟨⟨s, hs, hsa⟩, ⟨d, hd, hdab⟩, hall⟩ z
    constructor
    · intro hz
      exact (hall z hz).imp s1.mpr s2.mpr
    · rintro (h | h)
      · have e : z = s := mem_ext fun c => (h c).trans ((s1.mpr hsa) c).symm
        rw [e]
        exact hs
      · have e : z = d := mem_ext fun c => (h c).trans ((s2.mpr hdab) c).symm
        rw [e]
        exact hd

theorem z_hin_rl {f a b : K} : Hin.Rl f a b ↔ Pr f a b :=
  ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, z_hin_isOp.mp h⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, z_hin_isOp.mpr h⟩⟩

/-! ### The sets included in a transitive set form a model of `𝗠` -/

theorem isMacBase_wt : IsMacBase (WT K) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- extensionality
    intro x y h
    refine Subtype.ext (mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · exact (h ⟨z, inTr_mem x.2 hz⟩).mp hz
    · exact (h ⟨z, inTr_mem y.2 hz⟩).mpr hz
  · -- foundation
    rintro x ⟨y, hy⟩
    obtain ⟨m, hm, hmin⟩ := z_found x.1 ⟨y.1, hy⟩
    exact ⟨⟨m, inTr_mem x.2 hm⟩, hm, fun z hz => hmin z.1 hz⟩
  · -- pairs
    intro x y
    obtain ⟨tx, htx, hx⟩ := x.2
    obtain ⟨ty, hty, hy⟩ := y.2
    obtain ⟨p, hp⟩ : ∃ p : K, ∀ u, u ∈ p ↔ u = x.1 ∨ u = y.1 := ⟨{x.1, y.1}, fun u => by simp⟩
    obtain ⟨t, ht⟩ : ∃ t : K, ∀ u, u ∈ t ↔ u ∈ tx ∨ (u ∈ ty ∨ u ∈ p) :=
      ⟨tx ∪ (ty ∪ p), fun u => by simp only [mem_union_iff]⟩
    have hpW : InTr p := by
      refine ⟨t, fun u hu z hz => ?_, fun z hz => (ht z).mpr (Or.inr (Or.inr hz))⟩
      rcases (ht u).mp hu with h1 | h1 | h1
      · exact (ht z).mpr (Or.inl (htx u h1 z hz))
      · exact (ht z).mpr (Or.inr (Or.inl (hty u h1 z hz)))
      · rcases (hp u).mp h1 with e | e
        · rw [e] at hz
          exact (ht z).mpr (Or.inl (hx z hz))
        · rw [e] at hz
          exact (ht z).mpr (Or.inr (Or.inl (hy z hz)))
    exact ⟨⟨p, hpW⟩, (hp x.1).mpr (Or.inl rfl), (hp y.1).mpr (Or.inr rfl)⟩
  · -- power sets
    intro x
    obtain ⟨t, ht, hx⟩ := x.2
    obtain ⟨q, hq⟩ : ∃ q : K, ∀ u, u ∈ q ↔ ∀ w, w ∈ u → w ∈ x.1 :=
      ⟨℘ x.1, fun u => mem_power_iff.trans ⟨fun h w hw => h w hw, fun h w hw => h w hw⟩⟩
    obtain ⟨t', ht'⟩ : ∃ t' : K, ∀ u, u ∈ t' ↔ u ∈ t ∨ u ∈ q :=
      ⟨t ∪ q, fun u => mem_union_iff⟩
    have hqW : InTr q := by
      refine ⟨t', fun u hu z hz => ?_, fun z hz => (ht' z).mpr (Or.inr hz)⟩
      rcases (ht' u).mp hu with h1 | h1
      · exact (ht' z).mpr (Or.inl (ht u h1 z hz))
      · exact (ht' z).mpr (Or.inl (hx z ((hq u).mp h1 z hz)))
    exact ⟨⟨q, hqW⟩, fun z hz => (hq z.1).mpr fun w hw => hz ⟨w, inTr_mem z.2 hw⟩ hw⟩
  · -- transitive containment
    intro x
    obtain ⟨t, ht, hx⟩ := x.2
    exact ⟨⟨t, inTr_of_tr ht⟩, fun z hz => hx z.1 hz, fun y hy z hz => ht y.1 hy z.1 hz⟩
  · -- infinity
    have hω : Tr (ω : K) := fun y hy z hz =>
      (inferInstance : IsTransitive (ω : K)).transitive y hy z hz
    have hωW : InTr (ω : K) := inTr_of_tr hω
    have h0 : (∅ : K) ∈ (ω : K) := empty_mem_ω
    refine ⟨⟨ω, hωW⟩, ⟨⟨∅, inTr_mem hωW h0⟩, h0, fun z hz => ?_⟩, fun x hx => ?_⟩
    · exact absurd (show z.1 ∈ (∅ : K) from hz) (by simp)
    · have hs : succ x.1 ∈ (ω : K) := ω_succ_closed hx
      refine ⟨⟨succ x.1, inTr_mem hωW hs⟩, hs, fun z => ?_⟩
      have h1 : z.1 ∈ succ x.1 ↔ z.1 = x.1 ∨ z.1 ∈ x.1 := mem_succ_iff
      exact h1.trans (or_congr_left Subtype.ext_iff.symm)
  · -- separation in the structure of the members of a set
    intro t ψ ε
    obtain ⟨tt, htt, htsub⟩ := t.2
    let t₀ : K := t.1
    let π : extSet t₀ → extSet t := fun a =>
      ⟨⟨a.1, inTr_mem t.2 a.2⟩, show (⟨a.1, inTr_mem t.2 a.2⟩ : WT K) ∈ t from a.2⟩
    have hsur : Function.Surjective π := fun u =>
      ⟨⟨u.1.1, u.2⟩, Subtype.ext (Subtype.ext rfl)⟩
    have hmem : ∀ a a' : extSet t₀, π a ∈ π a' ↔ a ∈ a' := fun _ _ => Iff.rfl
    have heq : ∀ a a' : extSet t₀, π a = π a' ↔ a = a' := fun a a' =>
      ⟨fun h => Subtype.ext (congrArg (fun u : extSet t => (u.1.1 : K)) h), fun h => by rw [h]⟩
    let ε₀ : ℕ → extSet t₀ := fun k => ⟨(ε k).1.1, (ε k).2⟩
    have hε : (fun k ↦ π (ε₀ k)) = ε := funext fun k => Subtype.ext (Subtype.ext rfl)
    obtain ⟨y₀, hy₀⟩ := z_sep_raw (rlv ψ) (rhoT t₀ ε₀) t₀
    have hyW : InTr y₀ := ⟨tt, htt, fun z hz => htsub z ((hy₀ z).mp hz).1⟩
    refine ⟨⟨y₀, hyW⟩, fun z => ?_⟩
    have key : ∀ hz : z.1 ∈ t₀, Eval (M := K) ![z.1] (rhoT t₀ ε₀) (rlv ψ) ↔
        Eval (M := extSet t) ![(⟨z, hz⟩ : extSet t)] ε ψ := by
      intro hz
      let a : extSet t₀ := ⟨z.1, hz⟩
      have h1 := rlv_eval t₀ ε₀ ψ ![a]
      have h2 := eval_isoG π hsur hmem heq ψ ![a] ε₀
      have e1 : (fun i ↦ ((![a] i : extSet t₀) : K)) = ![z.1] := by
        funext i; fin_cases i; rfl
      have e2 : (fun i ↦ π (![a] i)) = ![(⟨z, hz⟩ : extSet t)] := by
        funext i; fin_cases i; rfl
      rw [e1] at h1
      rw [e2, hε] at h2
      exact h1.trans h2.symm
    have h3 : z ∈ (⟨y₀, hyW⟩ : WT K) ↔ z.1 ∈ t₀ ∧ Eval (M := K) ![z.1] (rhoT t₀ ε₀) (rlv ψ) :=
      hy₀ z.1
    exact h3.trans ⟨fun k => ⟨k.1, (key k.1).mp k.2⟩, fun ⟨hz, k⟩ => ⟨hz, (key hz).mpr k⟩⟩

instance wtNonempty : Nonempty (WT K) := isMacBase_wt.nonempty

/-- **The sets included in a transitive set, in a model of `𝗭`, are a model of `𝗠`.** -/
instance wtModelsM : (WT K)↓[ℒₛₑₜ] ⊧* 𝗠 := isMacBase_wt.models

/-! ### Ordinals and the hierarchy -/

/-- In a model of `𝗭`, an ordinal is empty, a successor or a limit. -/
theorem z_ord_cases {α : K} (hα : MH.Ord α) :
    (∀ z, z ∉ α) ∨ ((∃ γ, γ ∈ α ∧ SuccR α γ) ∨ LimR α) := by
  have hαW : InTr α := inTr_of_tr hα.1
  let α' : WT K := ⟨α, hαW⟩
  have hO : MH.Ord α' := (bdef_sub wt_tr ordB ![α']).mpr hα
  rcases ord_cases' hO with h | ⟨γ, hγ, hs⟩ | ⟨⟨z, hz⟩, hl⟩
  · exact Or.inl fun z hz => h ⟨z, inTr_mem hαW hz⟩ hz
  · exact Or.inr (Or.inl ⟨γ.1, hγ, (bdef_sub wt_tr succB ![α', γ]).mp hs⟩)
  · refine Or.inr (Or.inr ⟨⟨z.1, hz⟩, fun a ha => ?_⟩)
    obtain ⟨a', ha', hs⟩ := hl ⟨a, inTr_mem hαW ha⟩ ha
    exact ⟨a'.1, ha', (bdef_sub wt_tr succB ![a', ⟨a, inTr_mem hαW ha⟩]).mp hs⟩

/-- **The values of the hierarchy are transitive.** -/
theorem val_tr {h θ : K} (hθ : MH.Ord θ) (H : PowH h θ) :
    ∀ α, (α ∈ θ ∨ α = θ) → ∀ x, Pr h α x → Tr x := by
  obtain ⟨-, htot, hzero, hsucc, hlim⟩ := H
  by_contra hcon
  push_neg at hcon
  obtain ⟨α₀, hα₀, x₀, hp₀, hx₀⟩ := hcon
  obtain ⟨D, hD⟩ := z_sep badVF (succ θ) ![h]
  have hD' : ∀ α, α ∈ D ↔ (α = θ ∨ α ∈ θ) ∧ ∃ x, Pr h α x ∧ ¬Tr x := fun α =>
    (hD α).trans (and_congr mem_succ_iff Iff.rfl)
  obtain ⟨α, hαD, hmin⟩ := z_found D ⟨α₀, (hD' α₀).mpr ⟨hα₀.symm, x₀, hp₀, hx₀⟩⟩
  obtain ⟨hαθ, x, hp, hx⟩ := (hD' α).mp hαD
  have hOα : MH.Ord α := by
    rcases hαθ with e | e
    · rw [e]
      exact hθ
    · exact ord_mem hθ e
  have hlt : ∀ γ, γ ∈ α → γ ∈ θ := by
    intro γ hγ
    rcases hαθ with e | e
    · rw [e] at hγ
      exact hγ
    · exact hθ.1 α e γ hγ
  have ih : ∀ γ, γ ∈ α → ∀ x', Pr h γ x' → Tr x' := by
    intro γ hγ x' hp'
    by_contra hx'
    exact hmin γ ((hD' γ).mpr ⟨Or.inr (hlt γ hγ), x', hp', hx'⟩) hγ
  apply hx
  rcases z_ord_cases hOα with he | ⟨γ, hγ, hs⟩ | hl
  · have hz : ∀ z, z ∈ x ↔ NumR z := hzero α x hp he
    intro y hy z hz'
    exact (hz z).mpr (numR_mem ((hz y).mp hy) hz')
  · obtain ⟨x', hp'⟩ := htot γ (Or.inl (hlt γ hγ))
    have hK : ∀ z, z ∈ x ↔ ∀ w, w ∈ z → w ∈ x' := hsucc γ α x' x (hlt γ hγ) hs hp' hp
    have htr' : Tr x' := ih γ hγ x' hp'
    intro y hy z hz
    exact (hK z).mpr fun w hw => htr' z ((hK y).mp hy z hz) w hw
  · have hK : ∀ z, z ∈ x ↔ ∃ γ, γ ∈ α ∧ ∃ x', Pr h γ x' ∧ z ∈ x' :=
      hlim α x hαθ.symm hl hp
    intro y hy z hz
    obtain ⟨γ, hγ, x', hp', hyx⟩ := (hK y).mp hy
    exact (hK z).mpr ⟨γ, hγ, x', hp', ih γ hγ x' hp' y hyx z hz⟩

/-! ### The rank axioms -/

/-- **A rank axiom that holds in a model of `𝗭` holds in its sets included in a transitive
set.** -/
theorem hasRank_wt {n : ℕ} (hR : HasRank n K) : HasRank n (WT K) := by
  obtain ⟨h, θ, hθ, H, k, hk, hkθ, w, hw, hno⟩ := hR
  have hvt := val_tr hθ H
  obtain ⟨hfn, htot, hzero, hsucc, hlim⟩ := H
  have hOle : ∀ α, (α ∈ θ ∨ α = θ) → MH.Ord α := by
    rintro α (e | e)
    · exact ord_mem hθ e
    · rw [e]
      exact hθ
  -- the hierarchy cut down to its pairs
  obtain ⟨h₁, hh₁⟩ := z_sep goodPB.toFDef h ![θ]
  have hh₁' : ∀ p, p ∈ h₁ ↔ p ∈ h ∧ GoodP p θ := hh₁
  have hpr₁ : ∀ α x, Pr h₁ α x ↔ Pr h α x ∧ (α ∈ θ ∨ α = θ) := by
    intro α x
    constructor
    · rintro ⟨p, hp, hop⟩
      obtain ⟨hph, d, -, α', -, x', -, hop', hle⟩ := (hh₁' p).mp hp
      obtain ⟨e1, -⟩ := op_inj hop hop'
      rw [← e1] at hle
      exact ⟨⟨p, hph, hop⟩, hle⟩
    · rintro ⟨⟨p, hp, hop⟩, hle⟩
      obtain ⟨d, hd, hdab⟩ := hop.2.1
      exact ⟨p, (hh₁' p).mpr ⟨hp, d, hd, α, hdab.1, x, hdab.2.1, hop, hle⟩, hop⟩
  -- it is included in a transitive set
  obtain ⟨T, hT⟩ : ∃ T : K, ∀ u, u ∈ T ↔
      u ∈ h₁ ∨ (u ∈ ⋃ˢ h₁ ∨ (u ∈ ⋃ˢ (⋃ˢ h₁) ∨ u ∈ ⋃ˢ (⋃ˢ (⋃ˢ h₁)))) :=
    ⟨h₁ ∪ (⋃ˢ h₁ ∪ (⋃ˢ (⋃ˢ h₁) ∪ ⋃ˢ (⋃ˢ (⋃ˢ h₁)))), fun u => by simp only [mem_union_iff]⟩
  have hTtr : Tr T := by
    intro u hu z hz
    rcases (hT u).mp hu with h1 | h1 | h1 | h1
    · exact (hT z).mpr (Or.inr (Or.inl (mem_sUnion_iff.mpr ⟨u, h1, hz⟩)))
    · exact (hT z).mpr (Or.inr (Or.inr (Or.inl (mem_sUnion_iff.mpr ⟨u, h1, hz⟩))))
    · exact (hT z).mpr (Or.inr (Or.inr (Or.inr (mem_sUnion_iff.mpr ⟨u, h1, hz⟩))))
    · obtain ⟨c, hc, huc⟩ := mem_sUnion_iff.mp h1
      obtain ⟨s, hs, hcs⟩ := mem_sUnion_iff.mp hc
      obtain ⟨p, hp, hsp⟩ := mem_sUnion_iff.mp hs
      obtain ⟨hph, d, -, α, -, x, -, hop, hle⟩ := (hh₁' p).mp hp
      have hc' : c = α ∨ c = x := by
        rcases hop.2.2 s hsp with hsg | hup
        · exact Or.inl (hsg.2 c hcs)
        · exact hup.2.2 c hcs
      have hzc : z ∈ c := by
        rcases hc' with e | e
        · rw [e] at huc ⊢
          exact (hOle α hle).1 u huc z hz
        · rw [e] at huc ⊢
          exact hvt α hle x ⟨p, hph, hop⟩ u huc z hz
      exact (hT z).mpr (Or.inr (Or.inr (Or.inr (mem_sUnion_iff.mpr ⟨c, hc, hzc⟩))))
  have hh₁W : InTr h₁ := ⟨T, hTtr, fun z hz => (hT z).mpr (Or.inl hz)⟩
  have hθW : InTr θ := inTr_of_tr hθ.1
  let θ' : WT K := ⟨θ, hθW⟩
  let h' : WT K := ⟨h₁, hh₁W⟩
  have hPW : ∀ a b : WT K, Pr h' a b ↔ Pr h a.1 b.1 ∧ (a.1 ∈ θ ∨ a.1 = θ) := fun a b =>
    (bdef_sub wt_tr prB ![h', a, b]).trans (hpr₁ a.1 b.1)
  have hle' : ∀ α : WT K, (α ∈ θ' ∨ α = θ') → (α.1 ∈ θ ∨ α.1 = θ) := fun α hα =>
    hα.imp (fun e => e) (fun e => congrArg Subtype.val e)
  have hvW : ∀ α x, (α ∈ θ ∨ α = θ) → Pr h α x → InTr x := fun α x hle hp =>
    inTr_of_tr (hvt α hle x hp)
  let k' : WT K := ⟨k, inTr_mem hθW hkθ⟩
  let w' : WT K := ⟨w, hvW k w (Or.inl hkθ) hw⟩
  refine ⟨h', θ', (bdef_sub wt_tr ordB ![θ']).mpr hθ, ⟨?_, ?_, ?_, ?_, ?_⟩, k',
    (bdef_sub wt_tr (isNumB n) ![k']).mpr hk, hkθ, w', (hPW k' w').mpr ⟨hw, Or.inl hkθ⟩, ?_⟩
  · intro α x x' h1 h2
    exact Subtype.ext (hfn α.1 x.1 x'.1 ((hPW _ _).mp h1).1 ((hPW _ _).mp h2).1)
  · intro α hα
    obtain ⟨x, hp⟩ := htot α.1 (hle' α hα)
    exact ⟨⟨x, hvW α.1 x (hle' α hα) hp⟩, (hPW _ _).mpr ⟨hp, hle' α hα⟩⟩
  · intro α x hp hemp z
    have hemp' : ∀ c, ¬c ∈ α.1 := fun c hc => hemp ⟨c, inTr_mem α.2 hc⟩ hc
    have h1 : z.1 ∈ x.1 ↔ NumR z.1 := hzero α.1 x.1 ((hPW _ _).mp hp).1 hemp' z.1
    exact h1.trans (bdef_sub wt_tr numB ![z]).symm
  · intro α β x y hα hsc hpx hpy z
    have hK : ∀ z₀, z₀ ∈ y.1 ↔ ∀ c, c ∈ z₀ → c ∈ x.1 :=
      hsucc α.1 β.1 x.1 y.1 hα ((bdef_sub wt_tr succB ![β, α]).mp hsc) ((hPW _ _).mp hpx).1
        ((hPW _ _).mp hpy).1
    exact ⟨fun hz c hc => (hK z.1).mp hz c.1 hc,
      fun Hz => (hK z.1).mpr fun c hc => Hz ⟨c, inTr_mem z.2 hc⟩ hc⟩
  · intro β y hβ hlimβ hpy z
    have hle : β.1 ∈ θ ∨ β.1 = θ := hle' β hβ
    have hlim₀ : LimR β.1 := by
      obtain ⟨⟨c, hc⟩, hs⟩ := hlimβ
      refine ⟨⟨c.1, hc⟩, fun a ha => ?_⟩
      obtain ⟨a', ha', hsc⟩ := hs ⟨a, inTr_mem β.2 ha⟩ ha
      exact ⟨a'.1, ha', (bdef_sub wt_tr succB ![a', ⟨a, inTr_mem β.2 ha⟩]).mp hsc⟩
    have hK : ∀ z₀, z₀ ∈ y.1 ↔ ∃ a, a ∈ β.1 ∧ ∃ x, Pr h a x ∧ z₀ ∈ x :=
      hlim β.1 y.1 hle hlim₀ ((hPW _ _).mp hpy).1
    have hlt : ∀ a, a ∈ β.1 → a ∈ θ := by
      intro a ha
      rcases hle with e | e
      · exact hθ.1 β.1 e a ha
      · rw [e] at ha
        exact ha
    constructor
    · intro hz
      obtain ⟨a, ha, x, hp, hzx⟩ := (hK z.1).mp hz
      exact ⟨⟨a, inTr_mem β.2 ha⟩, ha, ⟨x, hvW a x (Or.inl (hlt a ha)) hp⟩,
        (hPW _ _).mpr ⟨hp, Or.inl (hlt a ha)⟩, hzx⟩
    · rintro ⟨a, ha, x, hp, hzx⟩
      exact (hK z.1).mpr ⟨a.1, ha, x.1, ((hPW _ _).mp hp).1, hzx⟩
  · rintro ⟨f, hf1, hf2⟩
    apply hno
    refine ⟨f.1, fun u hu => ?_, fun u u' v hu hu' h1 h2 => ?_⟩
    · let u₁ : WT K := ⟨u, inTr_mem hθW hu⟩
      obtain ⟨v, hv, hrl⟩ := hf1 u₁ hu
      have q1 : Pr f u₁ v := pr_iff.mpr (hin_rl_iff'.mp hrl)
      have p1 : Pr f.1 u v.1 := (bdef_sub wt_tr prB ![f, u₁, v]).mp q1
      exact ⟨v.1, hv, z_hin_rl.mpr p1⟩
    · have p1 : Pr f.1 u v := z_hin_rl.mp h1
      have p2 : Pr f.1 u' v := z_hin_rl.mp h2
      have hvW' : InTr v := by
        obtain ⟨p, hp, hop⟩ := p1
        obtain ⟨d, hd, hdab⟩ := hop.2.1
        exact inTr_mem (inTr_mem (inTr_mem f.2 hp) hd) hdab.2.1
      let u₁ : WT K := ⟨u, inTr_mem hθW hu⟩
      let u₂ : WT K := ⟨u', inTr_mem hθW hu'⟩
      let v₁ : WT K := ⟨v, hvW'⟩
      have q1 : Pr f u₁ v₁ := (bdef_sub wt_tr prB ![f, u₁, v₁]).mpr p1
      have q2 : Pr f u₂ v₁ := (bdef_sub wt_tr prB ![f, u₂, v₁]).mpr p2
      have e : u₁ = u₂ := hf2 u₁ u₂ v₁ hu hu' (hin_rl_iff'.mpr (pr_iff.mp q1))
        (hin_rl_iff'.mpr (pr_iff.mp q2))
      exact congrArg Subtype.val e

end zmodel

end ZT

/-! ### The consistency statement -/

/-- **The sets included in a transitive set, in a model of `𝗭` with the rank axioms, are a
model of `𝗠` with the rank axioms.** -/
theorem wt_models_mr {M : Type} [SetStructure M] [Nonempty M] (hTR : M↓[ℒₛₑₜ] ⊧* 𝗭𝗥) :
    haveI : M↓[ℒₛₑₜ] ⊧* 𝗭 :=
      models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hTR φ (Or.inl hφ)
    (ZT.WT M)↓[ℒₛₑₜ] ⊧* 𝗠𝗥 := by
  have hZ : M↓[ℒₛₑₜ] ⊧* 𝗭 :=
    models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hTR φ (Or.inl hφ)
  have hr : ∀ n, MH.HasRank n M := fun n =>
    models_rank_iff.mp (models_theory_iff.mp hTR _ (Or.inr ⟨n, rfl⟩))
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | ⟨n, rfl⟩
  · exact models_theory_iff.mp ZT.wtModelsM φ hφ
  · exact models_rank_iff.mpr (ZT.hasRank_wt (hr n))

/-- **If Zermelo set theory with the rank axioms is consistent, so is `𝗠` with the rank
axioms.** -/
theorem consistent_mr_of_consistent_zr (h : Entailment.Consistent 𝗭𝗥) :
    Entailment.Consistent 𝗠𝗥 := by
  by_contra hU
  refine Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable ?_) h
  apply SetTheory.complete.{0}
  intro M _ _ hTR
  exfalso
  apply hU
  have hZ : M↓[ℒₛₑₜ] ⊧* 𝗭 :=
    models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hTR φ (Or.inl hφ)
  have : (ZT.WT M)↓[ℒₛₑₜ] ⊧* 𝗠𝗥 := wt_models_mr hTR
  exact consistent_of_model 𝗠𝗥 (ZT.WT M)

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.ZT.wtModelsM
#print axioms FFL.FirstOrder.SetTheory.ZT.val_tr
#print axioms FFL.FirstOrder.SetTheory.ZT.hasRank_wt
#print axioms FFL.FirstOrder.SetTheory.consistent_mr_of_consistent_zr
