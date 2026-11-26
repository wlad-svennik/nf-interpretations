module

public import MHHartogs

@[expose] public section

set_option autoImplicit false

/-!
# A rank of a model of `𝗠𝗛𝗥` is a model of Zermelo set theory with the rank axioms

`𝗭𝗧` is Zermelo set theory `𝗭` (the library's: separation for all formulas, no Choice) with
transitive containment. `𝗭𝗧𝗥` and `𝗭𝗥` are `𝗭𝗧` and `𝗭` with the rank axioms of `MHRank.lean`.

**`consistent_ztr_of_consistent_mhr : Con(𝗠𝗛𝗥) → Con(𝗭𝗧𝗥)`**, and so `Con(𝗠𝗛𝗥) → Con(𝗭𝗥)`.

In a model of `𝗠𝗛` in which the rank axiom for `n + 8` holds, with hierarchy `h` on the
ordinals up to `θ`:

* `ρ` is Hartogs' ordinal of `pw n`; `ρ + 1` maps one-to-one into `pw (n + 6)`
  (`hart_pw`, `MHHartogs.lean`).
* The lexicographic order on `(ρ + 1) × ω` has a collapse `F` onto a limit ordinal `lam`, and
  `lam ⊆ θ`, as in `supply_of_rank`. Let `θ' = F ⟨ρ, 0⟩`; `ρ` maps one-to-one into `θ'`, so
  `θ'` does not map one-to-one into `pw n`.
* `X` is the value of `h` at `lam` (`exists_rankSet`, `RankSet`): a transitive set, closed
  under subsets of members, pairs and power sets, with `ω`, `θ'` and the hierarchy on the
  ordinals up to `θ'` as members (`powH_ord_sub`, `IsPowH.restrict`).
* The structure of the members of `X` satisfies separation for all formulas
  (`fullsep_extSet`): the formula with its quantifiers bounded by `X` (`rlv`, `rlv_eval`) is a
  bounded formula of the model. So it is a model of `𝗭` and of `𝗠` (`isMacBase_rankSet`,
  `models_zermelo_of_base`).
* The rank axioms up to `n` hold in it (`hasRank_rankSet`): bounded definitions are absolute
  for it (`bdef_abs`), and a one-to-one map in the model between members of `X` is a member.

The domain depends on `n`, so the theorem is by compactness (`consistent_ztr_of_forall`) and is
not an interpretation.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

/-! ### Relativisation to a set -/

section relativise

/-- A term with its parameters moved up by one, to make room for the set. -/
def sh1 {n : ℕ} : Semiterm ℒₛₑₜ ℕ n → Semiterm ℒₛₑₜ ℕ n
  | #x => #x
  | &x => &(x + 1)
  | .func f _ => Empty.elim f

/-- A formula with every quantifier bounded by the parameter `&0`. -/
def rlv {n : ℕ} : Semiformula ℒₛₑₜ ℕ n → Semiformula ℒₛₑₜ ℕ n
  | .rel r v => .rel r (fun i ↦ sh1 (v i))
  | .nrel r v => .nrel r (fun i ↦ sh1 (v i))
  | ⊤ => ⊤
  | ⊥ => ⊥
  | φ ⋏ ψ => rlv φ ⋏ rlv ψ
  | φ ⋎ ψ => rlv φ ⋎ rlv ψ
  | ∀¹ φ => ∀¹[memOp.operator ![#0, &0]] rlv φ
  | ∃¹ φ => ∃¹[memOp.operator ![#0, &0]] rlv φ

/-- **The relativised formula is bounded.** -/
theorem rlv_bdd : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n), (Bounding.mem ℒₛₑₜ).Closure (rlv φ) := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => exact Bounding.Closure.verum _
  | hfalsum => exact Bounding.Closure.falsum _
  | hrel r v => exact Bounding.Closure.rel r _
  | hnrel r v => exact Bounding.Closure.nrel r _
  | hand φ ψ ih1 ih2 => exact Bounding.Closure.and ih1 ih2
  | hor φ ψ ih1 ih2 => exact Bounding.Closure.or ih1 ih2
  | hall φ ih =>
    exact Bounding.Closure.ball (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive]) ih
  | hexs φ ih =>
    exact Bounding.Closure.bexs (Set.mem_singleton_iff.mpr rfl) (by simp [Semiterm.Positive]) ih

variable {M : Type} [SetStructure M]

/-- The parameters: the set, and the parameters of the formula. -/
def rhoT (t : M) (ε : ℕ → extSet t) : ℕ → M
  | 0 => t
  | k + 1 => (ε k : M)

lemma sh1_val (t : M) (ε : ℕ → extSet t) {n : ℕ} (u : Semiterm ℒₛₑₜ ℕ n)
    (e : Fin n → extSet t) :
    (sh1 u).val (M := M) (fun i ↦ (e i : M)) (rhoT t ε) =
      ((u.val (M := extSet t) e ε : extSet t) : M) := by
  match u with
  | #x => rfl
  | &x => rfl
  | .func f _ => exact Empty.elim f

/-- **The meaning of the relativised formula** is that of the formula in the structure of the
members of the set. -/
theorem rlv_eval (t : M) (ε : ℕ → extSet t) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ ℕ n) (e : Fin n → extSet t),
      Eval (M := M) (fun i ↦ (e i : M)) (rhoT t ε) (rlv φ) ↔ Eval (M := extSet t) e ε φ := by
  have hcons : ∀ {n : ℕ} (u : extSet t) (e : Fin n → extSet t),
      ((u : M) :> fun i ↦ (e i : M)) = fun i ↦ (((u :> e) i : extSet t) : M) := by
    intro n u e; funext i; cases i using Fin.cases <;> rfl
  have hrel : ∀ {n k : ℕ} (r : (ℒₛₑₜ).Rel k) (v : Fin k → Semiterm ℒₛₑₜ ℕ n)
      (e : Fin n → extSet t),
      Eval (M := M) (fun i ↦ (e i : M)) (rhoT t ε) (Semiformula.rel r (fun i ↦ sh1 (v i))) ↔
        Eval (M := extSet t) e ε (Semiformula.rel r v) := by
    intro n k r v e
    cases r with
    | eq =>
      show ((sh1 (v 0)).val (M := M) (fun i ↦ (e i : M)) (rhoT t ε) =
        (sh1 (v 1)).val (M := M) (fun i ↦ (e i : M)) (rhoT t ε)) ↔
        ((v 0).val (M := extSet t) e ε = (v 1).val (M := extSet t) e ε)
      rw [sh1_val, sh1_val]
      exact Subtype.ext_iff.symm
    | mem =>
      show ((sh1 (v 0)).val (M := M) (fun i ↦ (e i : M)) (rhoT t ε) ∈
        (sh1 (v 1)).val (M := M) (fun i ↦ (e i : M)) (rhoT t ε)) ↔
        ((v 0).val (M := extSet t) e ε ∈ (v 1).val (M := extSet t) e ε)
      rw [sh1_val, sh1_val]
      exact Iff.rfl
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro e; exact Iff.rfl
  | hfalsum => intro e; exact Iff.rfl
  | hrel r v => intro e; exact hrel r v e
  | hnrel r v =>
    intro e
    show Eval (M := M) (fun i ↦ (e i : M)) (rhoT t ε) (∼Semiformula.rel r (fun i ↦ sh1 (v i))) ↔
      Eval (M := extSet t) e ε (∼Semiformula.rel r v)
    simp only [LogicalConnective.HomClass.map_neg, LogicalConnective.Prop.neg_eq]
    exact not_congr (hrel r v e)
  | hand φ ψ ih1 ih2 =>
    intro e
    show Eval (M := M) _ _ (rlv φ ⋏ rlv ψ) ↔ Eval (M := extSet t) e ε (φ ⋏ ψ)
    simp only [LogicalConnective.HomClass.map_and, LogicalConnective.Prop.and_eq]
    rw [ih1 e, ih2 e]
  | hor φ ψ ih1 ih2 =>
    intro e
    show Eval (M := M) _ _ (rlv φ ⋎ rlv ψ) ↔ Eval (M := extSet t) e ε (φ ⋎ ψ)
    simp only [LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
    rw [ih1 e, ih2 e]
  | hall φ ih =>
    intro e
    show Eval (M := M) _ _ (∀¹[memOp.operator ![#0, &0]] rlv φ) ↔ Eval (M := extSet t) e ε (∀¹ φ)
    simp only [eval_ball, eval_memOp, Matrix.cons_val_zero]
    rw [eval_all]
    constructor
    · intro H u
      have h1 := H (u : M) u.2
      rw [hcons] at h1
      exact (ih _).mp h1
    · intro H x hx
      have h1 := (ih ((⟨x, hx⟩ : extSet t) :> e)).mpr (H ⟨x, hx⟩)
      rw [← hcons] at h1
      exact h1
  | hexs φ ih =>
    intro e
    show Eval (M := M) _ _ (∃¹[memOp.operator ![#0, &0]] rlv φ) ↔ Eval (M := extSet t) e ε (∃¹ φ)
    simp only [eval_bexs, eval_memOp, Matrix.cons_val_zero]
    rw [eval_ex]
    constructor
    · rintro ⟨x, hx, h1⟩
      have h2 : Eval (M := M) (((⟨x, hx⟩ : extSet t) : M) :> fun i ↦ (e i : M)) (rhoT t ε)
          (rlv φ) := h1
      rw [hcons] at h2
      exact ⟨⟨x, hx⟩, (ih _).mp h2⟩
    · rintro ⟨u, hu⟩
      refine ⟨(u : M), u.2, ?_⟩
      have h1 := (ih (u :> e)).mpr hu
      rw [← hcons] at h1
      exact h1

end relativise

/-! ### From separation for all formulas -/

/-- Separation for all formulas gives the condition `IsMacBase.sep`. -/
theorem sep_of_fullsep {W : Type} [SetStructure W]
    (hsep : ∀ (ψ : SetTheorySemiproposition 1) (ε : ℕ → W) (t : W),
      ∃ y : W, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := W) ![z] ε ψ)
    (t : W) (ψ : SetTheorySemiproposition 1) (ε : ℕ → extSet t) :
    ∃ y : W, ∀ z, z ∈ y ↔ ∃ hz : z ∈ extSet t, Eval (M := extSet t) ![⟨z, hz⟩] ε ψ := by
  obtain ⟨y, hy⟩ := hsep (rlv ψ) (rhoT t ε) t
  have e1 : ∀ (z : W) (hz : z ∈ extSet t),
      (fun i ↦ ((![(⟨z, hz⟩ : extSet t)] i : extSet t) : W)) = ![z] := by
    intro z hz; funext i; fin_cases i; rfl
  refine ⟨y, fun z => (hy z).trans ⟨fun h => ⟨h.1, ?_⟩, fun h => ?_⟩⟩
  · have h1 := rlv_eval t ε ψ ![⟨z, h.1⟩]
    rw [e1 z h.1] at h1
    exact h1.mp h.2
  · obtain ⟨hz, h2⟩ := h
    have h1 := rlv_eval t ε ψ ![⟨z, hz⟩]
    rw [e1 z hz] at h1
    exact ⟨hz, h1.mpr h2⟩

/-- A structure that satisfies the conditions of `IsMacBase` and separation for all formulas is
a model of `𝗭`. -/
theorem models_zermelo_of_base {W : Type} [SetStructure W] [Nonempty W] (h : IsMacBase W)
    (hsep : ∀ (ψ : SetTheorySemiproposition 1) (ε : ℕ → W) (t : W),
      ∃ y : W, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := W) ![z] ε ψ) : W↓[ℒₛₑₜ] ⊧* 𝗭 := by
  have hM : W↓[ℒₛₑₜ] ⊧* 𝗠 := h.models
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · exact models_theory_iff.mp hM φ (Or.inl (Or.inl hφ))
  · cases hφ with
    | separation ψ =>
      suffices ∀ (ε : ℕ → W) (x : W), ∃ y : W, ∀ z, z ∈ y ↔ z ∈ x ∧ Eval (M := W) ![z] ε ψ by
        simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema,
          Matrix.constant_eq_singleton]
      exact fun ε x => hsep ψ ε x

/-! ### The theories -/

/-- Zermelo set theory with transitive containment. -/
abbrev ZermeloT : SetTheory := 𝗭 ∪ 𝗧𝗖𝗼

@[inherit_doc] notation "𝗭𝗧" => ZermeloT

/-- `𝗭𝗧` with the rank axioms up to `N`. -/
abbrev ZermeloTRanksUpTo (N : ℕ) : SetTheory := 𝗭𝗧 ∪ {φ | ∃ j, j ≤ N ∧ φ = Axiom.rank j}

/-- `𝗭𝗧` with the rank axioms for every `n`. -/
abbrev ZermeloTRanks : SetTheory := 𝗭𝗧 ∪ Set.range Axiom.rank

@[inherit_doc] notation "𝗭𝗧𝗥" => ZermeloTRanks

/-- Zermelo set theory with the rank axioms for every `n`. -/
abbrev ZermeloRanks : SetTheory := 𝗭 ∪ Set.range Axiom.rank

@[inherit_doc] notation "𝗭𝗥" => ZermeloRanks

instance : 𝗘𝗤 _ ⪯ 𝗭𝗧 :=
  let : 𝗘𝗤 _ ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

instance (N : ℕ) : 𝗘𝗤 _ ⪯ ZermeloTRanksUpTo N :=
  let : 𝗘𝗤 _ ⪯ 𝗭𝗧 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

instance : 𝗘𝗤 _ ⪯ 𝗭𝗧𝗥 :=
  let : 𝗘𝗤 _ ⪯ 𝗭𝗧 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

instance : 𝗘𝗤 _ ⪯ 𝗭𝗥 :=
  let : 𝗘𝗤 _ ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this (Entailment.WeakerThan.ofSubset fun _ h ↦ Or.inl h)

/-- **Compactness.** If `𝗭𝗧` with the rank axioms up to `N` is consistent for every `N`, then
`𝗭𝗧𝗥` is consistent. -/
theorem consistent_ztr_of_forall (h : ∀ N, Entailment.Consistent (ZermeloTRanksUpTo N)) :
    Entailment.Consistent 𝗭𝗧𝗥 := by
  by_contra hZ
  have hbot : 𝗭𝗧𝗥 ⊢ (⊥ : Sentence ℒₛₑₜ) := Entailment.not_consistent_iff_inconsistent.mp hZ ⊥
  obtain ⟨𝓕, h𝓕, hfin, hF⟩ := Entailment.Compact.finite_provable hbot
  have key : ∀ S : Set (Sentence ℒₛₑₜ), S.Finite → S ⊆ 𝗭𝗧𝗥 →
      ∃ N : ℕ, ∀ φ ∈ S, φ ∈ 𝗭𝗧 ∨ ∃ k, k ≤ N ∧ φ = Axiom.rank k := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => exact fun _ => ⟨0, fun φ hφ => absurd hφ (Set.notMem_empty φ)⟩
    | @insert ψ S _ _ ih =>
      intro hsub
      obtain ⟨N, hN⟩ := ih fun φ hφ => hsub (Set.mem_insert_of_mem _ hφ)
      rcases hsub (Set.mem_insert ψ S) with hψ | ⟨k, rfl⟩
      · refine ⟨N, fun φ hφ => ?_⟩
        rcases hφ with rfl | hφ
        · exact Or.inl hψ
        · exact hN φ hφ
      · refine ⟨max N k, fun φ hφ => ?_⟩
        rcases hφ with rfl | hφ
        · exact Or.inr ⟨k, le_max_right _ _, rfl⟩
        · rcases hN φ hφ with h' | ⟨j, hj, rfl⟩
          · exact Or.inl h'
          · exact Or.inr ⟨j, le_trans hj (le_max_left _ _), rfl⟩
  obtain ⟨N, hN⟩ := key 𝓕 ((Set.adjunctiveSet_finite_iff 𝓕).mp hfin) h𝓕
  have hle : 𝓕 ⪯ ZermeloTRanksUpTo N := Entailment.WeakerThan.ofAxm! fun {φ} hφ => by
    rcases hN φ hφ with h' | ⟨k, hk, rfl⟩
    · exact Entailment.by_axm (Or.inl h')
    · exact Entailment.by_axm (Or.inr ⟨k, hk, rfl⟩)
  exact Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable (hle.pbl hF)) (h N)

namespace MH

/-! ### The notions of `AlephTheory.lean` in a model of `𝗠` -/

section basic

variable {V : Type} [SetStructure V] [Nonempty V] [hV : V↓[ℒₛₑₜ] ⊧* 𝗠]

theorem hin_isOp_iff' {p a b : V} : Hin.IsOp p a b ↔ p = kp a b := by
  have s1 : ∀ {u a : V}, Hin.IsSing u a ↔ u = {a} := fun {u a} =>
    ⟨fun h => mem_ext fun c => by simpa using h c, fun h c => by simp [h]⟩
  have s2 : ∀ {u a b : V}, Hin.IsUp u a b ↔ u = {a, b} := fun {u a b} =>
    ⟨fun h => mem_ext fun c => by simpa using h c, fun h c => by simp [h]⟩
  constructor
  · intro h
    refine mem_ext fun z => ?_
    rw [h z, s1, s2]
    simp [kp]
  · rintro rfl z
    rw [s1, s2]
    simp [kp]

theorem hin_rl_iff' {F a b : V} : Hin.Rl F a b ↔ kp a b ∈ F :=
  ⟨fun ⟨_, hp, h⟩ => hin_isOp_iff'.mp h ▸ hp, fun h => ⟨kp a b, h, hin_isOp_iff'.mpr rfl⟩⟩

end basic

section defs

variable {V : Type} [SetStructure V]

/-- The ordinal `α` is included in the value of the hierarchy at `α`: bounded form. -/
def OSub (α h : V) : Prop :=
  ∀ q, q ∈ h → ∀ u, u ∈ q → ∀ x, x ∈ u → (IsOp q α x → ∀ z, z ∈ α → z ∈ x)

/-- The value of `F` at the pair of `γ` and `e` is `v`. -/
def FZ (γ v u e F : V) : Prop := ∃ a, a ∈ u ∧ (IsOp a γ e ∧ Pr F a v)

end defs

def oSubB : BDef (k := 2) (fun V _ v ↦ OSub (v 0) (v 1)) :=
  (BDef.ball 1 (BDef.ball 0 (BDef.ball 0 ((isOpB.comp ![2, 3, 0]).imp
    (BDef.ball 3 (BDef.mem 0 1)))))).congr fun _ _ _ => Iff.rfl

def fzB : BDef (k := 5) (fun V _ v ↦ FZ (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 2 ((isOpB.comp ![0, 1, 4]).and (prB.comp ![5, 0, 2]))).congr fun _ _ _ => Iff.rfl

section rankset

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **Every ordinal up to `θ` is included in the value of the hierarchy at it.** -/
theorem powH_ord_sub {h θ : V} (H : IsPowH h θ) :
    ∀ α, α ∈ sc θ → ∀ x, Pr h α x → ∀ z, z ∈ α → z ∈ x := by
  have hsO : Ord (sc θ) := ord_sc H.ord
  have key := ord_ind oSubB ![h] hsO (fun β hβ ih => by
    show OSub β h
    have ih' : ∀ α, α ∈ β → ∀ x, Pr h α x → ∀ z, z ∈ α → z ∈ x := fun α hα x hx => by
      obtain ⟨q, hq, hop⟩ := hx
      obtain ⟨u, hu, hxu⟩ := pr_snd_mem hop
      exact ih α hα q hq u hu x hxu hop
    intro q hq u _ x _ hop
    have hx : Pr h β x := ⟨q, hq, hop⟩
    rcases ord_cases (ord_mem hsO hβ) with e | ⟨η, hη, e⟩ | hl
    · intro z hz
      rw [e] at hz
      exact absurd hz (by simp)
    · have hηθ : η ∈ θ := by
        rcases mem_sc.mp hβ with e' | e'
        · rw [← e']
          exact hη
        · exact H.ord.1 β e' η hη
      obtain ⟨xη, hxη⟩ := H.tot η (mem_sc.mpr (Or.inr hηθ))
      have htr := (powH_tmon H η (mem_sc.mpr (Or.inr hηθ)) xη hxη).1
      rw [e] at hx
      rw [H.fn _ _ _ hx (H.succ η xη hηθ hxη)]
      intro z hz
      rw [e] at hz
      rcases mem_sc.mp hz with e' | hz'
      · rw [e']
        exact mem_power_iff.mpr (ih' η hη xη hxη)
      · exact mem_power_iff.mpr fun w hw => htr z (ih' η hη xη hxη z hz') w hw
    · intro z hz
      have hsz : sc z ∈ β := hl.2.2 z hz
      obtain ⟨xs, hxs⟩ := H.tot (sc z) (hsO.1 β hβ (sc z) hsz)
      exact (H.lim β x hβ hl hx z).mpr
        ⟨sc z, hsz, xs, hxs, ih' (sc z) hsz xs hxs z (self_mem_sc z)⟩)
  intro α hα x hx
  obtain ⟨q, hq, hop⟩ := hx
  obtain ⟨u, hu, hxu⟩ := pr_snd_mem hop
  exact key α hα q hq u hu x hxu hop

/-- **The hierarchy on the ordinals up to a smaller ordinal.** -/
theorem IsPowH.restrict {h θ θ' : V} (H : IsPowH h θ) (hθ' : θ' ∈ sc θ) :
    ∃ h', IsPowH h' θ' ∧ (∀ α x, Pr h' α x ↔ (α ∈ sc θ' ∧ Pr h α x)) ∧
      ∀ p, p ∈ h' → ∃ α x, p = kp α x ∧ Pr h' α x := by
  have hsO := ord_sc H.ord
  have hθ'O : Ord θ' := ord_mem hsO hθ'
  have hsub : ∀ α, α ∈ sc θ' → α ∈ sc θ := fun α hα => by
    rcases mem_sc.mp hα with e | e
    · rw [e]
      exact hθ'
    · exact hsO.1 θ' hθ' α e
  obtain ⟨xt, hxt⟩ := H.tot θ' hθ'
  let h' : V := relB (k := 1) (prB.comp ![2, 0, 1]) (sc θ') (℘ xt) ![h]
  have hh' : ∀ α x, Pr h' α x ↔ (α ∈ sc θ' ∧ Pr h α x) := by
    intro α x
    refine (pr_relB (prB.comp ![2, 0, 1]) (sc θ') (℘ xt) ![h] α x).trans
      ⟨fun k => ⟨k.1, k.2.2⟩, fun k => ⟨k.1, ?_, k.2⟩⟩
    rcases mem_sc.mp k.1 with e | e
    · have k2 := k.2
      rw [e] at k2
      rw [H.fn _ _ _ k2 hxt]
      exact mem_power_iff.mpr fun z hz => hz
    · exact mem_power_iff.mpr (powH_mono H hθ' e k.2 hxt)
  refine ⟨h', ⟨hθ'O, fun α x x' k k' => H.fn α x x' ((hh' α x).mp k).2 ((hh' α x').mp k').2,
    fun α hα => ?_, ?_, fun α x hα hx => ?_, fun β y hβ hl hy z => ?_⟩, hh', fun p hp => ?_⟩
  · obtain ⟨x, hx⟩ := H.tot α (hsub α hα)
    exact ⟨x, (hh' α x).mpr ⟨hα, hx⟩⟩
  · refine (hh' ∅ om).mpr ⟨?_, H.zero⟩
    rcases ord_tri ord_empty hθ'O with e | e | e
    · exact mem_sc.mpr (Or.inr e)
    · exact mem_sc.mpr (Or.inl e)
    · exact absurd e (by simp)
  · have hx' := ((hh' α x).mp hx).2
    have hαθ : α ∈ θ := by
      rcases mem_sc.mp hθ' with e | e
      · rw [← e]
        exact hα
      · exact H.ord.1 θ' e α hα
    refine (hh' (sc α) (℘ x)).mpr ⟨?_, H.succ α x hαθ hx'⟩
    rcases ord_sc_le (ord_mem hθ'O hα) hθ'O hα with e | e
    · exact mem_sc.mpr (Or.inl e)
    · exact mem_sc.mpr (Or.inr e)
  · have hy' := ((hh' β y).mp hy).2
    rw [H.lim β y (hsub β hβ) hl hy' z]
    constructor
    · rintro ⟨α, hα, x, hx, hz⟩
      exact ⟨α, hα, x, (hh' α x).mpr ⟨(ord_sc hθ'O).1 β hβ α hα, hx⟩, hz⟩
    · rintro ⟨α, hα, x, hx, hz⟩
      exact ⟨α, hα, x, ((hh' α x).mp hx).2, hz⟩
  · obtain ⟨α, -, x, -, e⟩ := mem_prodS.mp (relB_sub (prB.comp ![2, 0, 1]) (sc θ') (℘ xt) ![h] hp)
    exact ⟨α, x, e, pr_iff.mpr (e ▸ hp)⟩

/-- A transitive set `X` that is closed under subsets of its members, pairs and power sets,
has `ω` as a member, and has as members a hierarchy `h'` on the ordinals up to `θ'` and `θ'`,
where `θ'` does not map one-to-one into `pw n`. -/
structure RankSet (n : ℕ) (X h' θ' : V) : Prop where
  tr : Tr X
  sub : ∀ x, x ∈ X → ∀ w, (∀ z, z ∈ w → z ∈ x) → w ∈ X
  cov : ∀ x y, x ∈ X → y ∈ X → ∃ t, t ∈ X ∧ (Tr t ∧ (x ∈ t ∧ (y ∈ t ∧ ℘ t ∈ X)))
  om : (om : V) ∈ X
  pow : IsPowH h' θ'
  hmem : h' ∈ X
  tmem : θ' ∈ X
  big : ¬VInj θ' (pw n)

/-- **In a model of `𝗠𝗛`, the rank axiom for `n + 8` gives such a set for `n`**: the value of
the hierarchy at a limit ordinal. -/
theorem exists_rankSet (n : ℕ) (hR : HasRank (n + 8) V) :
    ∃ X h' θ' : V, RankSet n X h' θ' := by
  obtain ⟨h, θ, hθ, hP, k, hk, hkθ, w, hw, hno⟩ := hR
  have H : IsPowH h θ := (powH_iff hθ).mp hP
  have ek : k = nm (n + 8) := (isNum_iff _ _).mp hk
  subst ek
  have ew : w = pw (n + 8) := H.fn _ _ _ hw (powH_num H _ (mem_sc.mpr (Or.inr hkθ)))
  subst ew
  have hno' : ¬VInj θ (pw (n + 8) : V) := hno
  obtain ⟨ρ, hρ⟩ := next_exists (pw n : V)
  have hρO : Ord ρ := ord_of_ordS hρ.1
  have hSO : Ord (sc ρ) := ord_sc hρO
  have hSinj : VInj (sc ρ) (pw (n + 6) : V) := vinj_sc_pow (hart_pw hρ)
  -- the collapse of the pairs
  obtain ⟨F, lam, hlamO, hF, honto⟩ := lex_collapse hSO
  have hFfn : ∀ γ m v v', γ ∈ sc ρ → m ∈ (om : V) → Pr F (kp γ m) v → Pr F (kp γ m) v' →
      v = v' := by
    intro γ m v v' hγ hm h1 h2
    obtain ⟨v₀, -, -, hu, -⟩ := hF γ m hγ hm
    rw [hu v h1, hu v' h2]
  have key : ¬ θ ∈ lam := by
    intro hθl
    obtain ⟨α₀, k₀, hα₀, hk₀, hFθ⟩ := honto θ hθl
    obtain ⟨v, -, hv, -, hmem⟩ := hF α₀ k₀ hα₀ hk₀
    have e : θ = v := hFfn α₀ k₀ θ v hα₀ hk₀ hFθ hv
    rw [← e] at hmem
    have h1 : VInj θ (prodS (sc ρ) (om : V)) :=
      vinj_of_rel (prB.comp ![2, 1, 0]) θ (prodS (sc ρ) (om : V)) ![F]
        (fun y hy => by
          obtain ⟨γ', n', hγ', hn', -, hFy⟩ := (hmem y).mp hy
          exact ⟨kp γ' n', mem_prodS.mpr ⟨γ', hγ', n', hn', rfl⟩, hFy⟩)
        (fun y y' a _ _ ha k1 k2 => by
          obtain ⟨γ, hγ, m, hm, rfl⟩ := mem_prodS.mp ha
          exact hFfn γ m y y' hγ hm k1 k2)
    have h3 : VInj θ (prodS (pw (n + 6) : V) (om : V)) := vinj_comp h1 (vinj_prod_left hSinj)
    exact hno' (vinj_mono h3 (prod_pw_sub (n + 5)))
  have hlamθ : ∀ v, v ∈ lam → v ∈ θ := by
    intro v hv
    rcases ord_tri (ord_mem hlamO hv) hθ with e | e | e
    · exact e
    · rw [e] at hv
      exact absurd hv key
    · exact absurd (hlamO.1 v hv θ e) key
  have fsucc : ∀ α, α ∈ sc ρ → ∀ m, m ∈ (om : V) → ∀ v v', Pr F (kp α m) v →
      Pr F (kp α (sc m)) v' → v' = sc v := by
    intro α hα m hm v v' hv hv'
    obtain ⟨w, -, hw, -, hwm⟩ := hF α m hα hm
    obtain ⟨w', -, hw', -, hwm'⟩ := hF α (sc m) hα (sc_mem_om hm)
    have e := hFfn α m v w hα hm hv hw
    have e' := hFfn α (sc m) v' w' hα (sc_mem_om hm) hv' hw'
    rw [e, e']
    refine mem_ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨g, j, hg, hj, hlt, hFy⟩ := (hwm' y).mp hy
      rcases hlt with h' | ⟨rfl, h'⟩
      · exact mem_sc.mpr (Or.inr ((hwm y).mpr ⟨g, j, hg, hj, Or.inl h', hFy⟩))
      · rcases mem_sc.mp h' with rfl | h''
        · exact mem_sc.mpr (Or.inl (hFfn g j y w hg hj hFy hw))
        · exact mem_sc.mpr (Or.inr ((hwm y).mpr ⟨g, j, hg, hj, Or.inr ⟨rfl, h''⟩, hFy⟩))
    · rcases mem_sc.mp hy with rfl | hy'
      · exact (hwm' y).mpr ⟨α, m, hα, hm, Or.inr ⟨rfl, self_mem_sc m⟩, hw⟩
      · obtain ⟨g, j, hg, hj, hlt, hFy⟩ := (hwm y).mp hy'
        refine (hwm' y).mpr ⟨g, j, hg, hj, ?_, hFy⟩
        rcases hlt with h' | ⟨rfl, h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨rfl, mem_sc.mpr (Or.inr h')⟩
  -- the ordinal `θ'`, and the limit ordinal `lam`
  have hρS : ρ ∈ sc ρ := self_mem_sc ρ
  obtain ⟨θ', hθ'l, hFθ', -, hθ'm⟩ := hF ρ ∅ hρS empty_mem_om
  have hlim : Lim lam := ⟨hlamO, ⟨θ', hθ'l⟩, fun v hv => by
    obtain ⟨γ, m, hγ, hm, hFv⟩ := honto v hv
    obtain ⟨v', hv'l, hv', -⟩ := hF γ (sc m) hγ (sc_mem_om hm)
    rw [← fsucc γ hγ m hm v v' hFv hv']
    exact hv'l⟩
  have hθ'θ : θ' ∈ θ := hlamθ θ' hθ'l
  have hθ's : θ' ∈ sc θ := mem_sc.mpr (Or.inr hθ'θ)
  have hbig : ¬VInj θ' (pw n : V) := by
    intro hv
    refine hρ.2.1 (vinj_comp ?_ hv)
    refine vinj_of_rel fzB ρ θ' ![prodS (sc ρ) (om : V), (∅ : V), F] (fun γ hγ => ?_)
      (fun γ γ' v hγ hγ' _ k1 k2 => ?_)
    · have hγS : γ ∈ sc ρ := mem_sc.mpr (Or.inr hγ)
      obtain ⟨v, -, hv, -, -⟩ := hF γ ∅ hγS empty_mem_om
      refine ⟨v, (hθ'm v).mpr ⟨γ, ∅, hγS, empty_mem_om, Or.inl hγ, hv⟩, ?_⟩
      show FZ γ v (prodS (sc ρ) (om : V)) ∅ F
      exact ⟨kp γ ∅, mem_prodS.mpr ⟨γ, hγS, ∅, empty_mem_om, rfl⟩, isOp_kp γ ∅, hv⟩
    · have k1' : FZ γ v (prodS (sc ρ) (om : V)) ∅ F := k1
      have k2' : FZ γ' v (prodS (sc ρ) (om : V)) ∅ F := k2
      obtain ⟨a, -, hop, hFa⟩ := k1'
      obtain ⟨a', -, hop', hFa'⟩ := k2'
      rw [isOp_iff.mp hop] at hFa
      rw [isOp_iff.mp hop'] at hFa'
      have hγS : γ ∈ sc ρ := mem_sc.mpr (Or.inr hγ)
      have hγ'S : γ' ∈ sc ρ := mem_sc.mpr (Or.inr hγ')
      have lt : ∀ γ₁ γ₂, γ₁ ∈ sc ρ → γ₂ ∈ sc ρ → γ₁ ∈ γ₂ → Pr F (kp γ₁ ∅) v →
          Pr F (kp γ₂ ∅) v → False := by
        intro γ₁ γ₂ h1 h2 h12 f1 f2
        obtain ⟨w, -, hw, -, hwm⟩ := hF γ₂ ∅ h2 empty_mem_om
        have e := hFfn γ₂ ∅ v w h2 empty_mem_om f2 hw
        have hvw : v ∈ w := (hwm v).mpr ⟨γ₁, ∅, h1, empty_mem_om, Or.inl h12, f1⟩
        rw [e] at hvw
        exact mem_irrefl _ hvw
      rcases ord_tri (ord_mem hρO hγ) (ord_mem hρO hγ') with e | e | e
      · exact (lt γ γ' hγS hγ'S e hFa hFa').elim
      · exact e
      · exact (lt γ' γ hγ'S hγS e hFa' hFa).elim
  -- the set `X`
  have hlams : lam ∈ sc θ := by
    rcases (ord_le_iff hlamO hθ).mp hlamθ with e | e
    · exact mem_sc.mpr (Or.inl e)
    · exact mem_sc.mpr (Or.inr e)
  obtain ⟨X, hX⟩ := H.tot lam hlams
  have hXm := H.lim lam X hlams hlim hX
  have hXtr : Tr X := (powH_tmon H lam hlams X hX).1
  have valX : ∀ α, α ∈ lam → ∀ x, Pr h α x →
      Tr x ∧ (x ∈ X ∧ (℘ x ∈ X ∧ ∀ w, (∀ z, z ∈ w → z ∈ x) → w ∈ X)) := by
    intro α hα x hx
    have hαθ := hlamθ α hα
    have hs1 : sc α ∈ lam := hlim.2.2 α hα
    have hs2 : sc (sc α) ∈ lam := hlim.2.2 _ hs1
    have p1 : Pr h (sc α) (℘ x) := H.succ α x hαθ hx
    have p2 : Pr h (sc (sc α)) (℘ (℘ x)) := H.succ (sc α) (℘ x) (hlamθ _ hs1) p1
    have sub : ∀ w, (∀ z, z ∈ w → z ∈ x) → w ∈ X := fun w hw =>
      (hXm w).mpr ⟨sc α, hs1, ℘ x, p1, mem_power_iff.mpr hw⟩
    exact ⟨(powH_tmon H α (mem_sc.mpr (Or.inr hαθ)) x hx).1, sub x fun z hz => hz,
      (hXm _).mpr ⟨sc (sc α), hs2, ℘ (℘ x), p2, mem_power_iff.mpr fun z hz => hz⟩, sub⟩
  -- the hierarchy on the ordinals up to `θ'`
  obtain ⟨h', H', hh', hpairs⟩ := H.restrict hθ's
  obtain ⟨xt, hxt⟩ := H.tot θ' hθ's
  have s1 := hlim.2.2 θ' hθ'l
  have s2 := hlim.2.2 _ s1
  have s3 := hlim.2.2 _ s2
  have s4 := hlim.2.2 _ s3
  have q1 : Pr h (sc θ') (℘ xt) := H.succ θ' xt hθ'θ hxt
  have q2 := H.succ _ _ (hlamθ _ s1) q1
  have q3 := H.succ _ _ (hlamθ _ s2) q2
  have q4 := H.succ _ _ (hlamθ _ s3) q3
  have hθ'X : θ' ∈ X := (hXm θ').mpr ⟨sc θ', s1, ℘ xt, q1,
    mem_power_iff.mpr (powH_ord_sub H θ' hθ's xt hxt)⟩
  have hh'X : h' ∈ X := by
    refine (hXm h').mpr ⟨_, s4, _, q4, mem_power_iff.mpr fun p hp => ?_⟩
    obtain ⟨α, x, rfl, hpr⟩ := hpairs p hp
    obtain ⟨hα, hx⟩ := (hh' α x).mp hpr
    have hαs : α ∈ sc θ := by
      rcases mem_sc.mp hα with e | e
      · rw [e]
        exact hθ's
      · exact (ord_sc hθ).1 θ' hθ's α e
    have hxsub : ∀ z, z ∈ x → z ∈ xt := by
      rcases mem_sc.mp hα with e | e
      · rw [e] at hx
        rw [H.fn _ _ _ hx hxt]
        exact fun z hz => hz
      · exact powH_mono H hθ's e hx hxt
    have hα1 : α ∈ ℘ xt :=
      mem_power_iff.mpr fun z hz => hxsub z (powH_ord_sub H α hαs x hx z hz)
    have hx1 : x ∈ ℘ xt := mem_power_iff.mpr hxsub
    show kp α x ∈ ℘ (℘ (℘ xt))
    refine mem_power_iff.mpr fun s hs => mem_power_iff.mpr fun t ht => ?_
    rcases (by simpa [kp] using hs : s = {α} ∨ s = {α, x}) with rfl | rfl
    · rw [show t = α by simpa using ht]
      exact hα1
    · rcases (by simpa using ht : t = α ∨ t = x) with rfl | rfl
      · exact hα1
      · exact hx1
  have h0lam : (∅ : V) ∈ lam := by
    rcases ord_tri ord_empty hlamO with e | e | e
    · exact e
    · rw [← e] at hθ'l
      exact absurd hθ'l (by simp)
    · exact absurd e (by simp)
  refine ⟨X, h', θ', ⟨hXtr, fun x hx w hw => ?_, fun x y hx hy => ?_,
    (valX ∅ h0lam om H.zero).2.1, H', hh'X, hθ'X, hbig⟩⟩
  · obtain ⟨α, hα, xα, hxα, hxm⟩ := (hXm x).mp hx
    obtain ⟨htr, -, -, hsub⟩ := valX α hα xα hxα
    exact hsub w fun z hz => htr x hxm z (hw z hz)
  · obtain ⟨α, hα, xα, hxα, hxm⟩ := (hXm x).mp hx
    obtain ⟨β, hβ, xβ, hxβ, hym⟩ := (hXm y).mp hy
    rcases ord_tri (ord_mem hlamO hα) (ord_mem hlamO hβ) with e | e | e
    · obtain ⟨htr, hmem, hpw, -⟩ := valX β hβ xβ hxβ
      exact ⟨xβ, hmem, htr,
        powH_mono H (mem_sc.mpr (Or.inr (hlamθ β hβ))) e hxα hxβ x hxm, hym, hpw⟩
    · obtain ⟨htr, hmem, hpw, -⟩ := valX β hβ xβ hxβ
      rw [e] at hxα
      rw [H.fn _ _ _ hxα hxβ] at hxm
      exact ⟨xβ, hmem, htr, hxm, hym, hpw⟩
    · obtain ⟨htr, hmem, hpw, -⟩ := valX α hα xα hxα
      exact ⟨xα, hmem, htr, hxm,
        powH_mono H (mem_sc.mpr (Or.inr (hlamθ α hα))) e hxβ hxα y hym, hpw⟩

end rankset

/-! ### The structure of the members of the set -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **Separation for all formulas** in the structure of the members of a set that has the
subsets of its members as members. -/
theorem fullsep_extSet {X : V} (hsub : ∀ x, x ∈ X → ∀ w, (∀ z, z ∈ w → z ∈ x) → w ∈ X)
    (ψ : SetTheorySemiproposition 1) (ε : ℕ → extSet X) (t : extSet X) :
    ∃ y : extSet X, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := extSet X) ![z] ε ψ := by
  obtain ⟨y, hy⟩ := sep_raw (rlv ψ) (rlv_bdd ψ) (rhoT X ε) (t : V)
  have hyX : y ∈ X := hsub t t.2 y fun z hz => ((hy z).mp hz).1
  refine ⟨⟨y, hyX⟩, fun z => ?_⟩
  have e1 : (fun i ↦ ((![z] i : extSet X) : V)) = ![(z : V)] := by
    funext i; fin_cases i; rfl
  have h1 := rlv_eval X ε ψ ![z]
  rw [e1] at h1
  exact (hy z).trans (and_congr Iff.rfl h1)

/-- Bounded definitions are absolute for the structure of the members of a transitive set. -/
theorem bdef_abs {k : ℕ} {R : MRel k} (d : BDef R) {X : V} (hX : Tr X)
    (v : Fin k → extSet X) : R (extSet X) v ↔ R V (fun i ↦ (v i : V)) := by
  have h1 := eval_submodel_iff (U := extSet X) (fun y hy z hz => hX y hy z hz) d.bdd v
    (Empty.elim)
  have e : (fun x : Empty ↦ ((Empty.elim x : extSet X) : V)) = (Empty.elim : Empty → V) :=
    funext fun x => x.elim
  rw [e] at h1
  exact (d.eval (extSet X) v).symm.trans (h1.trans (d.eval V _))

variable {n : ℕ} {X h' θ' : V}

theorem isMacBase_rankSet (RS : RankSet n X h' θ') : IsMacBase (extSet X) := by
  refine ⟨fun x y h => ?_, fun x hx => ?_, fun x y => ?_, fun x => ?_, fun x => ?_, ?_,
    sep_of_fullsep (fullsep_extSet RS.sub)⟩
  · refine Subtype.ext (mem_ext fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
    · exact (h ⟨z, RS.tr x x.2 z hz⟩).mp hz
    · exact (h ⟨z, RS.tr y y.2 z hz⟩).mpr hz
  · obtain ⟨y₀, hy₀⟩ := hx
    obtain ⟨y, hy, hmin⟩ := m_found (x : V) ⟨(y₀ : V), hy₀⟩
    exact ⟨⟨y, RS.tr x x.2 y hy⟩, hy, fun z hz => hmin z hz⟩
  · obtain ⟨t, ht, -, hx, hy, -⟩ := RS.cov x y x.2 y.2
    exact ⟨⟨t, ht⟩, hx, hy⟩
  · obtain ⟨t, ht, htr, hx, -, hp⟩ := RS.cov x x x.2 x.2
    exact ⟨⟨℘ t, hp⟩, fun z hz => mem_power_iff.mpr fun w hw =>
      htr x hx w (hz ⟨w, RS.tr z z.2 w hw⟩ hw)⟩
  · obtain ⟨t, ht, htr, hx, -, -⟩ := RS.cov x x x.2 x.2
    exact ⟨⟨t, ht⟩, fun z hz => htr x hx z hz, fun y hy z hz => htr y hy z hz⟩
  · refine ⟨⟨om, RS.om⟩, ⟨⟨∅, RS.tr _ RS.om _ empty_mem_om⟩, empty_mem_om, fun z hz => ?_⟩,
      fun x hx => ?_⟩
    · exact absurd (show (z : V) ∈ (∅ : V) from hz) (by simp)
    · have hs : sc (x : V) ∈ (om : V) := sc_mem_om hx
      refine ⟨⟨sc x, RS.tr _ RS.om _ hs⟩, hs, fun z => ?_⟩
      exact (mem_sc (γ := (x : V)) (z := (z : V))).trans (or_congr Subtype.ext_iff.symm Iff.rfl)

theorem nonempty_rankSet (RS : RankSet n X h' θ') : Nonempty (extSet X) := ⟨⟨om, RS.om⟩⟩

/-- **The rank axioms up to `n` hold in the structure.** The witnesses are the hierarchy `h'`
and the ordinal `θ'`; the conditions pass to the structure because bounded definitions are
absolute for it and it has the subsets of its members. -/
theorem hasRank_rankSet (RS : RankSet n X h' θ') {j : ℕ} (hj : j ≤ n) :
    HasRank j (extSet X) := by
  haveI : Nonempty (extSet X) := nonempty_rankSet RS
  have hM : (extSet X)↓[ℒₛₑₜ] ⊧* 𝗠 := (isMacBase_rankSet RS).models
  have H := RS.pow
  obtain ⟨c1, c2, c3, c4, c5⟩ := (powH_iff H.ord).mpr H
  let hW : extSet X := ⟨h', RS.hmem⟩
  let tW : extSet X := ⟨θ', RS.tmem⟩
  have prT : ∀ a b : extSet X, Pr hW a b ↔ Pr h' (a : V) (b : V) :=
    fun a b => bdef_abs prB RS.tr ![hW, a, b]
  have valX : ∀ a x : V, Pr h' a x → x ∈ X := by
    intro a x hx
    have h1 : kp a x ∈ X := RS.tr h' RS.hmem _ (pr_iff.mp hx)
    have h2 : ({a, x} : V) ∈ X := RS.tr _ h1 _ (by simp [kp])
    exact RS.tr _ h2 _ (by simp)
  -- the numeral and the value at it
  have hnmX : (nm j : V) ∈ X := RS.tr _ RS.om _ (nm_mem_om j)
  have hnO : Ord (nm j : V) := ord_mem ord_om (nm_mem_om j)
  have hsubj : ∀ z, z ∈ (nm j : V) → z ∈ (pw n : V) :=
    fun z hz => om_sub_pw n z (om_tr _ (nm_mem_om j) z hz)
  have hjθ' : (nm j : V) ∈ θ' := by
    rcases ord_tri hnO H.ord with e | e | e
    · exact e
    · have hv : VInj (nm j : V) (pw n) := vinj_of_sub hsubj
      rw [e] at hv
      exact absurd hv RS.big
    · exact absurd (vinj_of_sub fun z hz => hsubj z (hnO.1 θ' e z hz)) RS.big
  have hpj : Pr h' (nm j) (pw j) := powH_num H j (mem_sc.mpr (Or.inr hjθ'))
  let kW : extSet X := ⟨nm j, hnmX⟩
  let wW : extSet X := ⟨pw j, valX _ _ hpj⟩
  refine ⟨hW, tW, (bdef_abs ordB RS.tr ![tW]).mpr H.ord, ⟨?_, ?_, ?_, ?_, ?_⟩, kW,
    (bdef_abs (isNumB j) RS.tr ![kW]).mpr (isNum_nm j), hjθ', wW, (prT kW wW).mpr hpj, ?_⟩
  · exact fun α x x' k k' => Subtype.ext (c1 _ _ _ ((prT α x).mp k) ((prT α x').mp k'))
  · intro α hα
    have hα' : (α : V) ∈ θ' ∨ (α : V) = θ' :=
      hα.elim Or.inl fun e => Or.inr (congrArg Subtype.val e)
    obtain ⟨x, hx⟩ := c2 α hα'
    exact ⟨⟨x, valX _ _ hx⟩, (prT α ⟨x, valX _ _ hx⟩).mpr hx⟩
  · intro α x k hα z
    have hα' : ∀ z : V, ¬ z ∈ (α : V) := fun z hz => hα ⟨z, RS.tr α α.2 z hz⟩ hz
    exact (c3 α x ((prT α x).mp k) hα' z).trans (bdef_abs numB RS.tr ![z]).symm
  · intro α β x y hα hs kx ky z
    have hs' : SuccR (β : V) (α : V) := (bdef_abs succB RS.tr ![β, α]).mp hs
    exact (c4 α β x y hα hs' ((prT α x).mp kx) ((prT β y).mp ky) z).trans
      ⟨fun h w hw => h w hw, fun h w hw => h ⟨w, RS.tr z z.2 w hw⟩ hw⟩
  · intro β y hβ hl ky z
    have hβ' : (β : V) ∈ θ' ∨ (β : V) = θ' :=
      hβ.elim Or.inl fun e => Or.inr (congrArg Subtype.val e)
    have hl' : LimR (β : V) := by
      obtain ⟨⟨z₀, hz₀⟩, hl2⟩ := hl
      refine ⟨⟨z₀, hz₀⟩, fun α hα => ?_⟩
      obtain ⟨α', hα', hs⟩ := hl2 ⟨α, RS.tr β β.2 α hα⟩ hα
      exact ⟨α', hα', (bdef_abs succB RS.tr ![α', ⟨α, RS.tr β β.2 α hα⟩]).mp hs⟩
    refine (c5 β y hβ' hl' ((prT β y).mp ky) z).trans ⟨?_, ?_⟩
    · rintro ⟨α, hα, x, hx, hz⟩
      exact ⟨⟨α, RS.tr β β.2 α hα⟩, hα, ⟨x, valX _ _ hx⟩, (prT _ _).mpr hx, hz⟩
    · rintro ⟨α, hα, x, hx, hz⟩
      exact ⟨α, hα, x, (prT α x).mp hx, hz⟩
  · rintro ⟨f, hf1, hf2⟩
    have rlW : ∀ a b : extSet X, Hin.Rl f a b ↔ Pr (f : V) (a : V) (b : V) := fun a b =>
      (hin_rl_iff'.trans pr_iff.symm).trans (bdef_abs prB RS.tr ![f, a, b])
    apply RS.big
    refine vinj_mono (vinj_of_injV (F := (f : V)) ⟨fun u hu => ?_,
      fun u hu u' hu' v hv k k' => ?_⟩) (pw_mono hj)
    · obtain ⟨v, hv, hr⟩ := hf1 ⟨u, RS.tr θ' RS.tmem u hu⟩ hu
      exact ⟨v, hv, (rlW _ _).mp hr⟩
    · have huX := RS.tr θ' RS.tmem u hu
      have hu'X := RS.tr θ' RS.tmem u' hu'
      have hvX : v ∈ X := RS.tr _ (valX _ _ hpj) v hv
      exact congrArg Subtype.val (hf2 ⟨u, huX⟩ ⟨u', hu'X⟩ ⟨v, hvX⟩ hu hu'
        ((rlW ⟨u, huX⟩ ⟨v, hvX⟩).mpr k) ((rlW ⟨u', hu'X⟩ ⟨v, hvX⟩).mpr k'))

/-- **The structure is a model of `𝗭𝗧` with the rank axioms up to `n`.** -/
theorem models_upto_rankSet (RS : RankSet n X h' θ') [Nonempty (extSet X)] :
    (extSet X)↓[ℒₛₑₜ] ⊧* ZermeloTRanksUpTo n := by
  have hB := isMacBase_rankSet RS
  have hM : (extSet X)↓[ℒₛₑₜ] ⊧* 𝗠 := hB.models
  have hZ : (extSet X)↓[ℒₛₑₜ] ⊧* 𝗭 := models_zermelo_of_base hB (fullsep_extSet RS.sub)
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with (hφ | hφ) | ⟨j, hj, rfl⟩
  · exact models_theory_iff.mp hZ φ hφ
  · exact models_theory_iff.mp hM φ (Or.inr hφ)
  · exact models_rank_iff.mpr (hasRank_rankSet RS hj)

end model

end MH

/-! ### The consistency implications -/

/-- If `𝗠𝗛` with the rank axioms is consistent, so is `𝗭𝗧` with the rank axioms up to `N`: in a
model of `𝗠𝗛𝗥`, the value of the hierarchy for `N + 8` at a limit ordinal is a model. -/
theorem consistent_upto_of_consistent_mhr (h : Entailment.Consistent 𝗠𝗛𝗥) (N : ℕ) :
    Entailment.Consistent (ZermeloTRanksUpTo N) := by
  by_contra hU
  refine Entailment.not_consistent_iff_inconsistent.mpr
    (Entailment.inconsistent_of_provable ?_) h
  apply SetTheory.complete.{0}
  intro M _ _ hTR
  exfalso
  apply hU
  have hMH : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := mhr_models_mh
  obtain ⟨X, h', θ', RS⟩ := MH.exists_rankSet (V := M) N (mhr_rank (N + 8))
  haveI : Nonempty (extSet X) := MH.nonempty_rankSet RS
  have : (extSet X)↓[ℒₛₑₜ] ⊧* ZermeloTRanksUpTo N := MH.models_upto_rankSet RS
  exact consistent_of_model (ZermeloTRanksUpTo N) (extSet X)

/-- **If `𝗠𝗛` with the rank axioms is consistent, so is Zermelo set theory with transitive
containment and the rank axioms.** -/
theorem consistent_ztr_of_consistent_mhr (h : Entailment.Consistent 𝗠𝗛𝗥) :
    Entailment.Consistent 𝗭𝗧𝗥 :=
  consistent_ztr_of_forall fun N => consistent_upto_of_consistent_mhr h N

/-- **If `𝗠𝗛` with the rank axioms is consistent, so is Zermelo set theory with the rank
axioms.** -/
theorem consistent_zr_of_consistent_mhr (h : Entailment.Consistent 𝗠𝗛𝗥) :
    Entailment.Consistent 𝗭𝗥 :=
  (consistent_ztr_of_consistent_mhr h).of_subset fun φ hφ => by
    rcases hφ with hφ | hφ
    · exact Or.inl (Or.inl hφ)
    · exact Or.inr hφ

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.exists_rankSet
#print axioms FFL.FirstOrder.SetTheory.MH.models_upto_rankSet
#print axioms FFL.FirstOrder.SetTheory.consistent_ztr_of_consistent_mhr
#print axioms FFL.FirstOrder.SetTheory.consistent_zr_of_consistent_mhr
