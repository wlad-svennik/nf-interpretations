module

public import NFUCountLev
public import NFInterpretsMac
public import NFInterpretsFnCount

@[expose] public section

set_option autoImplicit false

/-!
# NFU + Infinity + the Axiom of Counting interprets Zermelo set theory

`𝗭` is the library's Zermelo set theory: extensionality, empty set, pairing, union, power set,
infinity, foundation and the schema of separation for all formulas. It has no axiom of choice.

The interpretation: the domain is `HinU.InX`, the types of well-founded pointed graphs that
belong to a level `Pⁿ(Ω)` for a natural number `n` (`NFUCountLev.lean`); membership is `Hin.EE`;
equality is equality. With the Axiom of Counting every level is mapped onto itself by the
type-raising map, so every subset of a level is the extension of a type in the next level.
The domain is a set of the model, which gives separation for all formulas.

* `exists_definable_subsetU`: in a model of `𝗡𝗙𝗨𝗜`, every subset of a set structure that is
  definable in the structure, with parameters, is a set (as in `NFInterpretsMac.lean`).
* `isMacBase_of_levels`, `sep_of_levels`: a structure of types that is the union of a directed
  family of transitive sets, each of whose subsets is the extension of an element and each of
  which has its power set included in another, satisfies the conditions of `IsMacBase` and
  separation for all formulas.
* `models_z_of_base`: such a structure is a model of `𝗭`.
* **`nfuicInterpretsZ : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭`**, and by composition `fncInterpretsZ : 𝗙𝗡𝗙𝗖 ⊳ 𝗭`,
  `fnkInterpretsZ : 𝗙𝗡𝗙𝗞 ⊳ 𝗭`, `nfcInterpretsZ : 𝗡𝗙𝗖 ⊳ 𝗭`.

This is Proposition 17.6 of the draft *Choice and Consistency Strength in NF and NFU* (v15), in
the form of an interpretation: bare NFU with Infinity and Counting, with no Choice and no
type-level pair, interprets Zermelo set theory without Choice.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace HinU

open Hin (IsSing IsUp IsOp Rl WF IsBis Bis IsSing3 IsPG IsType InZ EE IsEg IsTheta
  isSingD isUpD isOpD rlD wfD isBisD bisD isSing3D isPGD isTypeD inZD eeD isEgD isThetaD
  Stable Trans IsZero Succ Ind InOm FinS HasFin isZeroD succD indD inOmD finSD hasFinD
  tr tr_eval tr_strat σr rho eval_and')

/-! ### Definable subsets of a set structure -/

section relativise

variable {M : Type} [SetStructure M] {U : Type} [SetStructure U] [Nonempty M]
  [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

/-- **Definable subsets of a set structure are sets**, in a model of `𝗡𝗙𝗨𝗜`. `U` is a structure
whose universe is, through the one-to-one map `j`, the set `A` of the model, and whose
membership relation is the graph `R`. -/
theorem exists_definable_subsetU (j : U → M) (A R : M) (hA : ∀ v, v ∈ A ↔ ∃ u, j u = v)
    (hj : Function.Injective j) (hR : ∀ u u' : U, u ∈ u' ↔ Rl R (j u) (j u'))
    (ψ : SetTheorySemiproposition 1) (ε : ℕ → U) :
    ∃ S : M, ∀ v, v ∈ S ↔ ∃ u : U, j u = v ∧ Eval (M := U) ![u] ε ψ := by
  have h0 : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨 := models_nfu_of_nfui
  let χ : SetTheorySemiproposition 1 := Semiformula.rel Language.Set.Rel.mem ![#0, &0] ⋏ tr ψ
  have hχ : χ.IsStratified := ⟨σr, ![0], stratified_and.mpr
    ⟨stratified_rel.mpr ⟨0, fun i => by fin_cases i <;> rfl⟩,
      tr_strat ψ ![0] (fun i => by fin_cases i; rfl)⟩⟩
  have := by
    simpa [models_iff, Axiom.comprehensionSchema] using
      Theory.models M 𝗡𝗙𝗨 (NewFoundationsWithUrelements.comprehension χ hχ)
  obtain ⟨S, hS⟩ := this (rho A R j ε)
  refine ⟨S, fun v => (hS v).trans ?_⟩
  rw [eval_and']
  have e1 : ∀ u : U, (![j u] : Fin 1 → M) = fun i ↦ j (![u] i) := by
    intro u; funext i; fin_cases i; rfl
  constructor
  · rintro ⟨hv, H⟩
    obtain ⟨u, rfl⟩ := (hA v).mp hv
    rw [e1] at H
    exact ⟨u, rfl, (tr_eval A R j hA hj hR ε ψ _).mp H⟩
  · rintro ⟨u, rfl, H⟩
    refine ⟨(hA (j u)).mpr ⟨u, rfl⟩, ?_⟩
    rw [e1]
    exact (tr_eval A R j hA hj hR ε ψ _).mpr H

end relativise

/-! ### A structure built from levels -/

section base

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜]

/-- **The conditions of `IsMacBase`** for a structure `W` of types, with membership `EE`, that
is the union of a directed family `Lev` of transitive sets of types such that every subset of a
member of the family is the extension of an element of `W`, the power set of a member is
included in a member, and the set of the finite ordinals is a member. -/
theorem isMacBase_of_levels {W : Type} [SetStructure W] (i : W → M) (hi : Function.Injective i)
    {g : M} (hg : IsEg g) (hmem : ∀ a b : W, a ∈ b ↔ EE (i a) (i b))
    (hZ : ∀ w, InZ (i w)) (hdown : ∀ w v, EE v (i w) → ∃ w', i w' = v)
    (Lev : M → Prop) (lev_mem : ∀ w, ∃ L, Lev L ∧ i w ∈ L)
    (lev_dir : ∀ L₁ L₂, Lev L₁ → Lev L₂ →
      ∃ L, Lev L ∧ (∀ x, x ∈ L₁ → x ∈ L) ∧ ∀ x, x ∈ L₂ → x ∈ L)
    (lev_tr : ∀ L, Lev L → ∀ x, x ∈ L → ∀ v, EE v x → v ∈ L)
    (lev_key : ∀ L, Lev L → ∀ S : M, (∀ s, s ∈ S → s ∈ L) → ∃ w : W, ∀ v, EE v (i w) ↔ v ∈ S)
    (lev_pow : ∀ L, Lev L → ∃ L', Lev L' ∧ ∀ y, InZ y → (∀ u, EE u y → u ∈ L) → y ∈ L')
    {Ω : M} (hΩ : ∀ x, x ∈ Ω ↔ InOm x) (hΩL : Lev Ω) : IsMacBase W := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- extensionality
    intro x y h
    refine hi (ee_ext (hZ x) (hZ y) fun v => ⟨fun hv => ?_, fun hv => ?_⟩)
    · obtain ⟨z, rfl⟩ := hdown x v hv
      exact (hmem z y).mp ((h z).mp ((hmem z x).mpr hv))
    · obtain ⟨z, rfl⟩ := hdown y v hv
      exact (hmem z x).mp ((h z).mpr ((hmem z y).mpr hv))
  · -- foundation
    rintro x ⟨y, hy⟩
    obtain ⟨S, hS⟩ := (eeD.comp (τ' := ![6, 6]) ![0, 1] 0).comprehensionU ![i x]
    have hS' : ∀ v, v ∈ S ↔ EE v (i x) := hS
    obtain ⟨v, hvS, -, hmin⟩ := ee_wf S ⟨i y, (hS' _).mpr ((hmem y x).mp hy), hZ y⟩
    obtain ⟨z, rfl⟩ := hdown x v ((hS' v).mp hvS)
    exact ⟨z, (hmem z x).mpr ((hS' _).mp hvS), fun z' hz' hz'z =>
      hmin (i z') ((hS' _).mpr ((hmem z' x).mp hz')) ((hmem z' z).mp hz'z)⟩
  · -- pairing
    intro x y
    obtain ⟨L₁, hL₁, hx⟩ := lev_mem x
    obtain ⟨L₂, hL₂, hy⟩ := lev_mem y
    obtain ⟨L, hL, h1, h2⟩ := lev_dir L₁ L₂ hL₁ hL₂
    obtain ⟨p, hp⟩ := lev_key L hL L fun s hs => hs
    exact ⟨p, (hmem x p).mpr ((hp _).mpr (h1 _ hx)), (hmem y p).mpr ((hp _).mpr (h2 _ hy))⟩
  · -- power set
    intro x
    obtain ⟨L, hL, hx⟩ := lev_mem x
    obtain ⟨L', hL', hpow⟩ := lev_pow L hL
    obtain ⟨p, hp⟩ := lev_key L' hL' L' fun s hs => hs
    refine ⟨p, fun z hz => (hmem z p).mpr ((hp _).mpr (hpow _ (hZ z) fun u hu => ?_))⟩
    obtain ⟨w', rfl⟩ := hdown z u hu
    exact lev_tr L hL _ hx _ ((hmem w' x).mp (hz w' ((hmem w' z).mpr hu)))
  · -- transitive containment
    intro x
    obtain ⟨L, hL, hx⟩ := lev_mem x
    obtain ⟨t, ht⟩ := lev_key L hL L fun s hs => hs
    refine ⟨t, fun z hz => (hmem z t).mpr ((ht _).mpr (lev_tr L hL _ hx _ ((hmem z x).mp hz))),
      fun y hy z hz => ?_⟩
    exact (hmem z t).mpr ((ht _).mpr
      (lev_tr L hL _ ((ht _).mp ((hmem y t).mp hy)) _ ((hmem z y).mp hz)))
  · -- infinity
    obtain ⟨I, hI⟩ := lev_key Ω hΩL Ω fun s hs => hs
    have hΩdom : ∀ v, v ∈ Ω → ∃ w, i w = v := fun v hv => hdown I v ((hI v).mpr hv)
    refine ⟨I, ?_, fun x hx => ?_⟩
    · obtain ⟨z₀, hz₀⟩ := exists_zero (V := M)
      obtain ⟨e, he⟩ := hΩdom z₀ ((hΩ _).mpr (om_zero hz₀))
      refine ⟨e, (hmem e I).mpr ((hI _).mpr ?_), fun z hz => hz₀.2 (i z) ?_⟩
      · rw [he]; exact (hΩ _).mpr (om_zero hz₀)
      · rw [← he]; exact (hmem z e).mp hz
    · have hxΩ : InOm (i x) := (hΩ _).mp ((hI _).mp ((hmem x I).mp hx))
      obtain ⟨w', hw', hw'om⟩ := om_succ_exists hxΩ
      obtain ⟨x', rfl⟩ := hΩdom w' ((hΩ _).mpr hw'om)
      refine ⟨x', (hmem x' I).mpr ((hI _).mpr ((hΩ _).mpr hw'om)), fun z => ?_⟩
      rw [hmem z x', hw'.2.2 (i z), hmem z x]
      constructor
      · rintro (h | h)
        · exact Or.inr h
        · exact Or.inl (hi h)
      · rintro (rfl | h)
        · exact Or.inr rfl
        · exact Or.inl h
  · -- definable subsets of the members of an element
    intro t ψ ε
    obtain ⟨L, hL, ht⟩ := lev_mem t
    obtain ⟨A, hA⟩ := (eeD.comp (τ' := ![6, 6]) ![0, 1] 0).comprehensionU ![i t]
    have hA' : ∀ v, v ∈ A ↔ EE v (i t) := hA
    let j : extSet t → M := fun u ↦ i u.1
    have hjA : ∀ v, v ∈ A ↔ ∃ u : extSet t, j u = v := fun v =>
      ⟨fun hv => by
        obtain ⟨z, rfl⟩ := hdown t v ((hA' v).mp hv)
        exact ⟨⟨z, (hmem z t).mpr ((hA' _).mp hv)⟩, rfl⟩,
      fun ⟨u, hu⟩ => hu ▸ (hA' _).mpr ((hmem u.1 t).mp u.2)⟩
    obtain ⟨S, hS⟩ := exists_definable_subsetU j A g hjA
      (fun u u' h => Subtype.ext (hi h))
      (fun u u' => (hmem u.1 u'.1).trans (rl_eg hg _ _).symm) ψ ε
    obtain ⟨y, hy⟩ := lev_key L hL S fun s hs => by
      obtain ⟨u, rfl, -⟩ := (hS s).mp hs
      exact lev_tr L hL _ ht _ ((hmem u.1 t).mp u.2)
    refine ⟨y, fun z => (hmem z y).trans ((hy _).trans ((hS _).trans ⟨?_, ?_⟩))⟩
    · rintro ⟨u, hu, H⟩
      have e : u.1 = z := hi hu
      subst e
      exact ⟨u.2, H⟩
    · rintro ⟨hz, H⟩
      exact ⟨⟨z, hz⟩, rfl, H⟩

/-- **Separation for all formulas** in such a structure, when its universe is a set `A` of the
model. -/
theorem sep_of_levels {W : Type} [SetStructure W] (i : W → M) (hi : Function.Injective i)
    {g : M} (hg : IsEg g) (hmem : ∀ a b : W, a ∈ b ↔ EE (i a) (i b))
    {A : M} (hA : ∀ v, v ∈ A ↔ ∃ w, i w = v)
    (Lev : M → Prop) (lev_mem : ∀ w, ∃ L, Lev L ∧ i w ∈ L)
    (lev_tr : ∀ L, Lev L → ∀ x, x ∈ L → ∀ v, EE v x → v ∈ L)
    (lev_key : ∀ L, Lev L → ∀ S : M, (∀ s, s ∈ S → s ∈ L) → ∃ w : W, ∀ v, EE v (i w) ↔ v ∈ S)
    (ψ : SetTheorySemiproposition 1) (ε : ℕ → W) (t : W) :
    ∃ y : W, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := W) ![z] ε ψ := by
  obtain ⟨L, hL, ht⟩ := lev_mem t
  obtain ⟨S, hS⟩ := exists_definable_subsetU i A g hA hi
    (fun u u' => (hmem u u').trans (rl_eg hg _ _).symm) ψ ε
  obtain ⟨S', hS'⟩ := ((SDef.mem (τ := ![6, 7, 6]) 0 1).and
    (eeD.comp ![0, 2] 0)).comprehensionU ![S, i t]
  have hS'' : ∀ v, v ∈ S' ↔ v ∈ S ∧ EE v (i t) := hS'
  obtain ⟨y, hy⟩ := lev_key L hL S' fun s hs => lev_tr L hL _ ht _ ((hS'' s).mp hs).2
  refine ⟨y, fun z => (hmem z y).trans ((hy _).trans ((hS'' _).trans ⟨?_, ?_⟩))⟩
  · rintro ⟨hzS, hzt⟩
    obtain ⟨u, hu, H⟩ := (hS _).mp hzS
    have e : u = z := hi hu
    subst e
    exact ⟨(hmem u t).mpr hzt, H⟩
  · rintro ⟨hzt, H⟩
    exact ⟨(hS _).mpr ⟨z, rfl, H⟩, (hmem z t).mp hzt⟩

/-- **The types that belong to a level form a model of the conditions**, when the model
satisfies the Axiom of Counting. -/
theorem base_of_embed (hC : JensenNFU.Counting (fun a b : M => a ∈ b)) {W : Type}
    [SetStructure W] (i : W → M) (hi : Function.Injective i)
    (hdom : ∀ x : M, InX x ↔ ∃ w, i w = x) (hmem : ∀ a b : W, a ∈ b ↔ EE (i a) (i b)) :
    IsMacBase W ∧ ∀ (ψ : SetTheorySemiproposition 1) (ε : ℕ → W) (t : W),
      ∃ y : W, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := W) ![z] ε ψ := by
  obtain ⟨g, hg⟩ := exists_eg (V := M)
  obtain ⟨W₀, hW⟩ := exists_W (V := M)
  obtain ⟨A, hA⟩ := inXD.comprehensionU (![] : Fin 0 → M)
  have hA' : ∀ v, v ∈ A ↔ ∃ w, i w = v := fun v => (hA v).trans (hdom v)
  have hlev : ∀ w, ∃ n, NatN n ∧ InLev W₀ n (i w) := fun w =>
    (inX_iff hW).mp ((hdom _).mpr ⟨w, rfl⟩)
  have hZ : ∀ w, InZ (i w) := fun w => let ⟨_, _, h⟩ := hlev w; lev_inZ hW h
  have hdown : ∀ w v, EE v (i w) → ∃ w', i w' = v := fun w v hv => by
    obtain ⟨n, hn, h⟩ := hlev w
    exact (hdom v).mp ((inX_iff hW).mpr ⟨n, hn, lev_trans hW n hn _ _ h hv⟩)
  let Lev : M → Prop := fun L => ∃ n, NatN n ∧ ∀ x, x ∈ L ↔ InLev W₀ n x
  have lev_mem : ∀ w, ∃ L, Lev L ∧ i w ∈ L := fun w => by
    obtain ⟨n, hn, h⟩ := hlev w
    obtain ⟨L, hL⟩ := exists_slice W₀ n
    exact ⟨L, ⟨n, hn, hL⟩, (hL _).mpr h⟩
  have lev_dir : ∀ L₁ L₂, Lev L₁ → Lev L₂ →
      ∃ L, Lev L ∧ (∀ x, x ∈ L₁ → x ∈ L) ∧ ∀ x, x ∈ L₂ → x ∈ L := by
    rintro L₁ L₂ ⟨n, hn, h1⟩ ⟨m, hm, h2⟩
    rcases lev_total hW n hn m hm with h | h
    · exact ⟨L₂, ⟨m, hm, h2⟩, fun x hx => (h2 x).mpr (h x ((h1 x).mp hx)), fun x hx => hx⟩
    · exact ⟨L₁, ⟨n, hn, h1⟩, fun x hx => hx, fun x hx => (h1 x).mpr (h x ((h2 x).mp hx))⟩
  have lev_tr : ∀ L, Lev L → ∀ x, x ∈ L → ∀ v, EE v x → v ∈ L := by
    rintro L ⟨n, hn, hL⟩ x hx v hv
    exact (hL v).mpr (lev_trans hW n hn x v ((hL x).mp hx) hv)
  have lev_key : ∀ L, Lev L → ∀ S : M, (∀ s, s ∈ S → s ∈ L) →
      ∃ w : W, ∀ v, EE v (i w) ↔ v ∈ S := by
    rintro L ⟨n, hn, hL⟩ S hS
    obtain ⟨y, hyZ, hy⟩ := stable_full hg (lev_stable hC hW hg hn hL) S hS
    obtain ⟨n', hs⟩ := exists_succN n
    have hyl : InLev W₀ n' y := lev_succ hW hn hs hyZ fun u hu => (hL u).mp (hS u ((hy u).mp hu))
    obtain ⟨w, rfl⟩ := (hdom y).mp ((inX_iff hW).mpr ⟨n', natN_succ hn hs, hyl⟩)
    exact ⟨w, hy⟩
  have lev_pow : ∀ L, Lev L → ∃ L', Lev L' ∧ ∀ y, InZ y → (∀ u, EE u y → u ∈ L) → y ∈ L' := by
    rintro L ⟨n, hn, hL⟩
    obtain ⟨n', hs⟩ := exists_succN n
    obtain ⟨L', hL'⟩ := exists_slice W₀ n'
    exact ⟨L', ⟨n', natN_succ hn hs, hL'⟩, fun y hyZ hyu =>
      (hL' y).mpr (lev_succ hW hn hs hyZ fun u hu => (hL u).mp (hyu u hu))⟩
  obtain ⟨z, hz⟩ := exists_zeroN (V := M)
  obtain ⟨Ω, hΩ⟩ := exists_slice W₀ z
  have hΩ' : ∀ x, x ∈ Ω ↔ InOm x := fun x => (hΩ x).trans (lev_zero_iff hW hz)
  exact ⟨isMacBase_of_levels i hi hg hmem hZ hdown Lev lev_mem lev_dir lev_tr lev_key lev_pow hΩ'
      ⟨z, natN_zero hz, hΩ⟩,
    sep_of_levels i hi hg hmem hA' Lev lev_mem lev_tr lev_key⟩

end base

end HinU

/-! ### Models of `𝗭` -/

/-- **A structure that satisfies the conditions of `IsMacBase` and separation for all formulas
is a model of `𝗭`.** The structure is given with its relation symbols; the hypotheses are about
its membership relation. -/
theorem models_z_of_base {W : Type} [SetStructure W] [Nonempty W] (h : IsMacBase W)
    (hsep : ∀ (ψ : SetTheorySemiproposition 1) (ε : ℕ → W) (t : W),
      ∃ y : W, ∀ z, z ∈ y ↔ z ∈ t ∧ Eval (M := W) ![z] ε ψ)
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W] :
    W↓[ℒₛₑₜ] ⊧* 𝗭 := by
  rcases standardStructure_unique W s
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

end FFL.FirstOrder.SetTheory
