module

public import ClassZ
public import HkSound
public import MHLRank

@[expose] public section

/-!
# The classes over a constructible model of `𝗭𝗖`, and the standard numbers of the cut

Inside a model `V` of `𝗠𝗛`. Let `T` be a set as in `MHLRank.lean` (`LimFull T`: a union of
levels of the constructible sets at full heights; its members are a model of `𝗭𝗖`), and let
`μ` be a full height with `T` in the level at `μ`. The *classes* are the members of that level
that are included in `T` (`clsOf T μ`).

* `compAx_cls`: comprehension by a bounded condition holds for the classes: the class is cut
  out of `T` by bounded separation, it is constructible, and a constructible subset of a member
  of the level at a full height is in the level.
* **`thetaZ_cls`**: the classes satisfy the sentence `thetaZ` of `ClassZ.lean`. Their sets are
  the members of `T`.
* `chi_cls`: the instance of the family at a numeral `j` holds if the members of `T` satisfy
  the rank axiom for `j`.
* **`nm_mem_kset`**: in a model of `𝗠𝗛` with all the rank axioms, every numeral is in the set
  `Kset` of `HkCut.lean` for the sentence `sigmaZ` and the formula `chiU.φ`: by
  `exists_zc_ranks` there is a `T` with the rank axioms up to `n`, the classes over it are a
  set with a well-order (the order of the constructible sets), and `sound_kset` applies.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-- **The sentence of the Henkin construction**: the axioms of equality and the theory of
classes. -/
def sigmaZ : Semiformula ℒₛₑₜ Empty 0 := eqAx ⋏ thetaZ

theorem bstL_sub {φ : Sentence ℒₛₑₜ} (h : φ ∈ bstL) : φ ∈ (𝗭𝗖 : SetTheory) := by
  simp only [bstL, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl BasicSetTheory.empty_set)
  · exact Or.inl (Or.inl BasicSetTheory.extensionality)
  · exact Or.inl (Or.inl BasicSetTheory.pairing)
  · exact Or.inl (Or.inl BasicSetTheory.union)
  · exact Or.inl (Or.inl BasicSetTheory.power_set)
  · exact Or.inl (Or.inl BasicSetTheory.infinity)
  · exact Or.inl (Or.inl BasicSetTheory.foundation)
  · exact Or.inr (Set.mem_singleton_iff.mpr rfl)

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **The classes over `T`**: the members of the level at `μ` that are included in `T`. -/
noncomputable def clsOf (T μ : V) : V :=
  sepB (k := 1) (BDef.ball 0 (BDef.mem 0 2)) (Lev μ) ![T]

theorem mem_clsOf {T μ Y : V} : Y ∈ clsOf T μ ↔ Y ∈ Lev μ ∧ ∀ z, z ∈ Y → z ∈ T :=
  mem_sepB _ _ _ Y

variable {T μ : V} (hT : LimFull T) (hμ : Full μ) (hTμ : T ∈ Lev μ)

include hT hμ hTμ

theorem t_sub_cls {z : V} (hz : z ∈ T) : z ∈ clsOf T μ :=
  mem_clsOf.mpr ⟨lev_tr hμ.lim.1 T hTμ z hz, fun w hw => hT.tr z hz w hw⟩

omit hT hμ in
theorem t_mem_cls : T ∈ clsOf T μ := mem_clsOf.mpr ⟨hTμ, fun _ h => h⟩

theorem cls_tr : ∀ y ∈ extSet (clsOf T μ), ∀ z ∈ y, z ∈ extSet (clsOf T μ) :=
  fun y hy z hz => t_sub_cls hT hμ hTμ ((mem_clsOf.mp hy).2 z hz)

omit hT hTμ in
theorem cls_con {Y : V} (hY : Y ∈ clsOf T μ) : Con Y := ⟨μ, hμ.lim.1, (mem_clsOf.mp hY).1⟩

omit hT in
/-- A subset of `T` cut out by a bounded condition with classes as parameters is a class. -/
theorem sep_mem_cls {k : ℕ} {R : MRel (k + 1)} (d : BDef R) (p : Fin k → V)
    (hp : ∀ i, p i ∈ clsOf T μ) : sepB d T p ∈ clsOf T μ := by
  have hsub : ∀ z, z ∈ sepB d T p → z ∈ T := fun z hz => ((mem_sepB d T p z).mp hz).1
  have hc : Con (sepB d T p) :=
    con_sepB d ⟨μ, hμ.lim.1, hTμ⟩ p (fun i => cls_con hμ (hp i))
  exact mem_clsOf.mpr ⟨hμ.sub T _ hTμ hc hsub, hsub⟩

theorem isSet_cls (x : extSet (clsOf T μ)) : IsSet x ↔ (x : V) ∈ T :=
  ⟨fun ⟨Y, hY⟩ => (mem_clsOf.mp Y.2).2 _ hY, fun h => ⟨⟨T, t_mem_cls hTμ⟩, h⟩⟩

/-- **Comprehension by a bounded condition holds for the classes.** -/
theorem compAx_cls {Φ : Rel5}
    (d : BDef (k := 5) (fun V _ v ↦ Φ V (v 0) (v 1) (v 2) (v 3) (v 4))) :
    CompAx Φ (extSet (clsOf T μ)) := by
  intro U hU C D a
  have hUT : (U : V) = T := mem_ext fun z =>
    ⟨fun hz => (isSet_cls hT hμ hTμ ⟨z, cls_tr hT hμ hTμ U U.2 z hz⟩).mp
        ((hU ⟨z, cls_tr hT hμ hTμ U U.2 z hz⟩).mp hz),
      fun hz => (hU ⟨z, t_sub_cls hT hμ hTμ hz⟩).mpr
        ((isSet_cls hT hμ hTμ ⟨z, t_sub_cls hT hμ hTμ hz⟩).mpr hz)⟩
  let E : V := sepB d T ![T, (C : V), (D : V), (a : V)]
  have hE : ∀ z, z ∈ E ↔ z ∈ T ∧ Φ V z T (C : V) (D : V) (a : V) :=
    fun z => mem_sepB d T _ z
  have hEc : E ∈ clsOf T μ := sep_mem_cls hμ hTμ d _ (fun i => by
    fin_cases i
    · exact t_mem_cls hTμ
    · exact C.2
    · exact D.2
    · exact a.2)
  refine ⟨⟨E, hEc⟩, fun x => ?_⟩
  have h1 : x ∈ (⟨E, hEc⟩ : extSet (clsOf T μ)) ↔ (x : V) ∈ E := Iff.rfl
  have h2 : Φ (extSet (clsOf T μ)) x U C D a ↔ Φ V (x : V) (U : V) (C : V) (D : V) (a : V) :=
    bdef_subS (cls_tr hT hμ hTμ) d ![x, U, C, D, a]
  have h3 : x ∈ U ↔ (x : V) ∈ T := by
    have h4 : x ∈ U ↔ (x : V) ∈ (U : V) := Iff.rfl
    rw [h4, hUT]
  rw [h1, hE, h3, h2, hUT]

/-- The axioms about the classes hold. -/
theorem clsAx_cls : ClsAx (extSet (clsOf T μ)) := by
  refine ⟨⟨⟨om, t_sub_cls hT hμ hTμ hT.om⟩, (isSet_cls hT hμ hTμ _).mpr hT.om⟩,
    ⟨⟨T, t_mem_cls hTμ⟩, fun x => (isSet_cls hT hμ hTμ x).symm⟩, ?_,
    compAx_cls hT hμ hTμ phiComplB, compAx_cls hT hμ hTμ phiInterB,
    compAx_cls hT hμ hTμ phiUnionB, compAx_cls hT hμ hTμ phiDomB,
    compAx_cls hT hμ hTμ phiAllB, compAx_cls hT hμ hTμ phiWB, compAx_cls hT hμ hTμ phiW1B,
    compAx_cls hT hμ hTμ phiE01B, compAx_cls hT hμ hTμ phiE10B,
    compAx_cls hT hμ hTμ phiE00B, compAx_cls hT hμ hTμ phiI01B,
    compAx_cls hT hμ hTμ phiSecB⟩
  intro D a ha hsub
  refine (isSet_cls hT hμ hTμ D).mpr ?_
  exact hT.sub ((isSet_cls hT hμ hTμ a).mp ha) (cls_con hμ D.2)
    fun z hz => hsub ⟨z, cls_tr hT hμ hTμ D D.2 z hz⟩ hz

/-- The members of `T`, as the sets of the structure of the classes. -/
noncomputable def toSets (x : extSet T) : SetsOf (extSet (clsOf T μ)) :=
  ⟨⟨x.1, t_sub_cls hT hμ hTμ x.2⟩, (isSet_cls hT hμ hTμ _).mpr x.2⟩

/-- **Truth among the sets of the classes is truth among the members of `T`.** -/
theorem sets_eval_iff {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (e : Fin n → extSet T) :
    Eval (M := SetsOf (extSet (clsOf T μ))) (fun i ↦ toSets hT hμ hTμ (e i)) Empty.elim φ ↔
      Eval (M := extSet T) e Empty.elim φ := by
  have h := eval_isoG (toSets hT hμ hTμ)
    (fun y => ⟨⟨y.1.1, (isSet_cls hT hμ hTμ y.1).mp y.2⟩, Subtype.ext (Subtype.ext rfl)⟩)
    (fun a a' => Iff.rfl)
    (fun a a' => ⟨fun h => Subtype.ext (congrArg (fun y : SetsOf (extSet (clsOf T μ)) =>
      ((y : extSet (clsOf T μ)) : V)) h), fun h => by rw [h]⟩) φ e Empty.elim
  have e1 : (fun x : Empty ↦ toSets hT hμ hTμ (Empty.elim x)) =
      (Empty.elim : Empty → SetsOf (extSet (clsOf T μ))) := funext fun x => x.elim
  rw [e1] at h
  exact h

/-- **The classes satisfy the theory of classes.** -/
theorem thetaZ_cls : Eval (M := extSet (clsOf T μ)) ![] Empty.elim thetaZ := by
  refine eval_thetaZ.mpr ⟨clsAx_cls hT hμ hTμ, fun φ hφ => ?_⟩
  haveI := limFull_nonempty hT
  have hZC : (extSet T)↓[ℒₛₑₜ] ⊧* 𝗭𝗖 := limFull_models_zc hT
  have h1 : Eval (M := extSet T) ![] Empty.elim φ := models_theory_iff.mp hZC φ (bstL_sub hφ)
  have h2 := (sets_eval_iff hT hμ hTμ φ ![]).mpr h1
  have e1 : (fun i ↦ toSets hT hμ hTμ ((![] : Fin 0 → extSet T) i)) = ![] :=
    funext fun i => i.elim0
  rw [e1] at h2
  exact h2

theorem sigmaZ_cls : Eval (M := extSet (clsOf T μ)) ![] Empty.elim sigmaZ :=
  ⟨eval_eqAx _, thetaZ_cls hT hμ hTμ⟩

/-- **The instance of the family at the numeral `j₀`** holds for the classes, if the members of
`T` satisfy the rank axiom for `j₀`. -/
theorem chi_cls (j₀ : ℕ) (hr : HasRank j₀ (extSet T)) (v : Fin 3 → extSet (clsOf T μ))
    (h0 : (v 0 : V) = sc (nm j₀)) (h1 : (v 1 : V) = nm j₀) (h2 : (v 2 : V) = ∅) :
    ChiR (extSet (clsOf T μ)) (v 0) (v 1) (v 2) := by
  have hom : ∀ n, n ∈ (om : V) → n ∈ T := fun n hn => hT.tr om hT.om n hn
  have hd : IsSet (v 1) := (isSet_cls hT hμ hTμ _).mpr (h1 ▸ hom _ (nm_mem_om j₀))
  refine ⟨fun w hw => ?_, ?_, ?_, ?_, hd, ?_⟩
  · have : (w : V) ∈ (v 2 : V) := hw
    rw [h2] at this
    exact absurd this (by simp)
  · refine (bdef_subS (cls_tr hT hμ hTμ) succB ![v 0, v 1]).mpr ?_
    show SuccR (v 0 : V) (v 1 : V)
    rw [h0, h1]
    exact succR_iff_sc.mpr rfl
  · exact (isSet_cls hT hμ hTμ _).mpr (h0 ▸ hom _ (nm_mem_om (j₀ + 1)))
  · exact (isSet_cls hT hμ hTμ _).mpr (h2 ▸ hom _ empty_mem_om)
  · obtain ⟨k, hk, hex⟩ := hasRank_iff.mp hr
    have hkv : (k : V) = nm j₀ :=
      (isNum_iff j₀ _).mp ((bdef_subS (U := extSet T) hT.tr (isNumB j₀) ![k]).mp hk)
    have e1 : Eval (M := extSet T) ![k] Empty.elim rankKU.φ :=
      (rankKU.eval (extSet T) ![k]).mpr hex
    have e2 := (sets_eval_iff hT hμ hTμ rankKU.φ ![k]).mpr e1
    obtain ⟨h, θ, hr'⟩ := (rankKU.eval (SetsOf (extSet (clsOf T μ)))
      (fun i ↦ toSets hT hμ hTμ ((![k] : Fin 1 → extSet T) i))).mp e2
    have e3 : (⟨v 1, hd⟩ : SetsOf (extSet (clsOf T μ))) = toSets hT hμ hTμ k :=
      Subtype.ext (Subtype.ext (h1.trans hkv.symm))
    rw [e3]
    exact ⟨h, θ, hr'⟩

end model

/-- **In a model of `𝗠𝗛` with all the rank axioms, every numeral is in the cut.** -/
theorem nm_mem_kset {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]
    (hR : ∀ n : ℕ, HasRank n V) {P : V} (hP : CanP P) (n : ℕ) :
    (nm n : V) ∈ Kset sigmaZ chiU.φ P := by
  obtain ⟨T, hT, hrk⟩ := exists_zc_ranks n (hR (4 * (n + 3) + 15))
  obtain ⟨γ, hγ, hTγ⟩ := hT.con
  obtain ⟨μ, hμ, hγμ⟩ := exists_full_above hγ
  have hμO : MH.Ord μ := hμ.lim.1
  have hTμ : T ∈ Lev μ := lev_mono hμO hγμ T hTγ
  have hsubL : ∀ z, z ∈ clsOf T μ → z ∈ Lev μ := fun z hz => (mem_clsOf.mp hz).1
  have hW := wol hμO
  have hom : ∀ m, m ∈ (om : V) → m ∈ T := fun m hm => hT.tr om hT.om m hm
  refine sound_kset (A := clsOf T μ) (W := LtS μ) hP
    (fun x hx y hy => wol_tot hμO hW x (hsubL x hx) y (hsubL y hy))
    (fun Z hZ hne => wol_least hμO hW Z (fun z hz => hsubL z (hZ z hz)) hne)
    (fun m hm => t_sub_cls hT hμ hTμ (hom m hm)) sigmaZ chiU.φ
    (sigmaZ_cls hT hμ hTμ) (nm_mem_om n) ?_
  intro j hj v h0 h1 h2
  obtain ⟨j₀, hj₀, rfl⟩ := mem_nm.mp hj
  exact (chiU.eval (extSet (clsOf T μ)) v).mpr
    (chi_cls hT hμ hTμ j₀ (hrk j₀ (Nat.le_of_lt hj₀)) v h0 h1 h2)

end MH

end FFL.FirstOrder.SetTheory
