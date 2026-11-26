module

public import NFInterpretsFn
public import NFUJensen
public import FnCountTransfer
public import TranslationCongr

@[expose] public section

set_option autoImplicit false

/-!
# NF with the Axiom of Counting interprets FunctionNF with count

The translation is that of `NFInterpretsFn.lean`: application is `AppR`, read through the
bijection between the universe and the set of functions.

Let `M` be a model of `𝗡𝗙` that satisfies the Axiom of Counting, and `N` the model of `𝗙𝗡𝗙`
built in it.

* `exists_setLabel`, `exists_setObj`: some object `s₀` of `N` sends every `y` to the object
  that labels the characteristic function of `y`. So `s₀ · y` is a set of `N`, with the members
  that `y` has in `M`.
* `fnModel_counting`: the sets of `N` satisfy the Axiom of Counting, by `counting_of_transfer`.
* `fnModel_count`: `N` satisfies count, because over FunctionNF count is the Axiom of Counting
  for the sets (`countChurch_iff_counting`).
* **Results**: `nfcInterpretsFNC : 𝗡𝗙𝗖 ⊳ 𝗙𝗡𝗙𝗖`, and `nfcInterpretsNFUIC : 𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖` by the
  identity.
-/

namespace FFL.FirstOrder.SetTheory

/-! ### NF with Counting proves NFU + Infinity with Counting -/

/-- **Every theorem of `𝗡𝗙𝗨𝗜𝗖` is a theorem of `𝗡𝗙𝗖`.** -/
instance nfuic_weakerThan_nfc : 𝗡𝗙𝗨𝗜𝗖 ⪯ 𝗡𝗙𝗖 :=
  Entailment.weakerThan_iff.mpr fun {φ} h => by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    have hNF : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙 :=
      models_theory_iff.mpr fun ψ hψ => models_theory_iff.mp hT ψ (Or.inl hψ)
    have hU := models_nfui_of_models_nf hNF
    have : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖 := models_theory_iff.mpr fun ψ hψ => by
      rcases hψ with hψ | hψ
      · exact models_theory_iff.mp hU ψ hψ
      · exact models_theory_iff.mp hT ψ (Or.inr hψ)
    exact models_of_provable this h

/-- **`𝗡𝗙𝗖` interprets `𝗡𝗙𝗨𝗜𝗖`**, by the identity. -/
instance nfcInterpretsNFUIC : 𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖 := DirectInterpretation.ofWeakerThan 𝗡𝗙𝗖 𝗡𝗙𝗨𝗜𝗖

namespace NFFn

open DirectTranslation

/-! ### The object that turns a set into the label of its characteristic function -/

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙]

/-- Some `s₀` has `AppR s₀ y f` exactly when `f` labels the characteristic function of `y`. -/
theorem exists_setLabel : ∃ s₀ : M, ∀ y f, AppR s₀ y f ↔ ∃ F, Chi y F ∧ J f F := by
  obtain ⟨F, hF⟩ := (SDef.ex (τ := ![9]) 9 (SDef.ex 9 ((prD.comp ![2, 1, 0] 1).and
    (SDef.ex 9 ((chiD.comp ![2, 0] 0).and (jD.comp ![1, 0] 0)))))).comprehension
      (![] : Fin 0 → M)
  refine app_of_graph (G := fun y f => ∃ F', Chi y F' ∧ J f F') (F := F) (fun p => hF p) ?_ ?_
  · intro y
    obtain ⟨F', hF'⟩ := exists_chi y
    obtain ⟨f, hf⟩ := j_surj (chi_spec hF').1
    exact ⟨f, F', hF', hf⟩
  · rintro y f f' ⟨F', h1, h2⟩ ⟨F'', h1', h2'⟩
    rw [chi_unique h1 h1'] at h2
    exact j_inj h2 h2'

local notation "N" => fnTranslation.Model M

/-- **Some object `s₀` of the model of FunctionNF sends every `y` to a set whose members are
the members of `y`.** -/
theorem exists_setObj : ∃ s₀ : N, ∀ y : N, FNF.IsSet (FNF.App s₀ y) ∧
    ∀ x : N, FNF.Mem x (FNF.App s₀ y) ↔ (x : M) ∈ (y : M) := by
  obtain ⟨s, hs⟩ := exists_setLabel (M := M)
  have htt : IsTT ((FNF.TT : N) : M) := (tt_iff _).mp rfl
  have hff : IsFF ((FNF.FF : N) : M) := (ff_iff _).mp rfl
  refine ⟨toModel s, fun y => ?_⟩
  obtain ⟨F, hχ, hJ⟩ :=
    (hs (y : M) _).mp ((app_iff (toModel s) y (FNF.App (toModel s) y)).mp rfl)
  have hrow : ∀ a b : N, b = FNF.App (FNF.App (toModel s) y) a ↔
      ((a : M) ∈ (y : M) ∧ IsTT (b : M)) ∨ ((a : M) ∉ (y : M) ∧ IsFF (b : M)) := by
    intro a b
    rw [app_iff]
    constructor
    · rintro ⟨F', hJ', h⟩
      rw [← j_fun hJ hJ'] at h
      exact ((chi_spec hχ).2 _ _).mp h
    · intro h
      exact ⟨F, hJ, ((chi_spec hχ).2 _ _).mpr h⟩
  have hset : FNF.IsSet (FNF.App (toModel s) y) := by
    intro a
    rcases (hrow a _).mp rfl with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl ((tt_iff _).mpr h)
    · exact Or.inr ((ff_iff _).mpr h)
  refine ⟨hset, fun x => ⟨fun h => ?_, fun h => ⟨hset, ?_⟩⟩⟩
  · rcases (hrow x _).mp h.2.symm with ⟨hx, -⟩ | ⟨-, hf⟩
    · exact hx
    · exact absurd rfl (tt_ne_ff htt hf)
  · exact ((hrow x _).mpr (Or.inl ⟨h, htt⟩)).symm

/-- **If the model of `𝗡𝗙` satisfies the Axiom of Counting, so do the sets of the model of
FunctionNF built in it.** -/
theorem fnModel_counting (hC : JensenNFU.Counting (fun a b : M => a ∈ b)) :
    JensenNFU.Counting (FNF.Mem (M := N)) := by
  have hNFUI : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 := models_nfui_of_models_nf hT
  have hU : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨 :=
    models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hNFUI φ (Or.inl hφ)
  obtain ⟨e₀, he₀⟩ := Hin.exists_empty (V := M)
  have hI : (modelOfJensenNFU hU e₀ he₀).Infinity :=
    modelOfJensenNFU_infinity hU e₀ he₀ (models_theory_iff.mp hNFUI _ (Or.inr rfl))
  have : Fact (modelOfJensenNFU hU e₀ he₀).Infinity := ⟨hI⟩
  have hTn : ∀ n : (modelOfJensenNFU hU e₀ he₀).Num, (modelOfJensenNFU hU e₀ he₀).T n = n :=
    (modelOfJensenNFU hU e₀ he₀).counting_iff_T.mp hC
  obtain ⟨s₀, hs₀⟩ := exists_setObj (M := M)
  have : (fnTranslation.Model M)↓[ℒλ] ⊧* 𝗙𝗡𝗙 := fnModel_models
  exact FNF.counting_of_transfer (modelOfJensenNFU hU e₀ he₀) hTn (fun a : N => (a : M)) toModel
    (fun _ => rfl) (fun _ => coe_inj rfl) s₀ (fun x y => (hs₀ y).2 x)

/-- **If the model of `𝗡𝗙` satisfies the Axiom of Counting, the model of FunctionNF built in it
satisfies count.** -/
theorem fnModel_count (hC : JensenNFU.Counting (fun a b : M => a ∈ b)) :
    (fnTranslation.Model M)↓[ℒλ] ⊧ FNF.Axiom.count := by
  have : (fnTranslation.Model M)↓[ℒλ] ⊧* 𝗙𝗡𝗙 := fnModel_models
  exact FNF.models_count_iff.mpr (FNF.countChurch_of_counting (fnModel_counting hC))

end model

/-! ### The interpretation -/

/-- A model of `𝗡𝗙𝗖` is a model of `𝗡𝗙` and satisfies the Axiom of Counting. -/
lemma nfc_models {M : Type} [SetStructure M] [Nonempty M] (hT : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗖) :
    M↓[ℒₛₑₜ] ⊧* 𝗡𝗙 ∧ JensenNFU.Counting (fun a b : M => a ∈ b) :=
  ⟨models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hT φ (Or.inl hφ),
    models_counting_iff.mp (models_theory_iff.mp hT _ (Or.inr rfl))⟩

/-- **The translation of the language of FunctionNF into `𝗡𝗙𝗖`**: the formulas are those of
`fnTranslation`. -/
def fnTranslationC : DirectTranslation 𝗡𝗙𝗖 ℒλ where
  domain := ⟨⊤⟩
  rel := fnRel
  func := fnFunc
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    simp [models_iff, Semiformula.Operator.val]
  func_defined {k} f := by
    apply SetTheory.complete.{0}
    intro M _ _ hTC
    have : M↓[ℒₛₑₜ] ⊧* 𝗡𝗙 := (nfc_models hTC).1
    have h : ∀ v : Fin k → M, (∀ i, (⟨⊤⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![v i]) →
        ∃! y, (⟨⊤⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![y] ∧ (fnFunc f).val (y :> v) := by
      intro v _
      obtain ⟨y, hy, huniq⟩ := graph_existsUnique f v
      exact ⟨y, ⟨by simp [Semiformula.Operator.val], (fnFunc_val f y v).mpr hy⟩,
        fun y' hy' => huniq y' ((fnFunc_val f y' v).mp hy'.2)⟩
    simpa [models_iff, Function.comp_def, Matrix.constant_eq_singleton] using h
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : fnRel (Language.Eq.eq : (ℒλ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

/-- The two translations translate every formula in the same way. -/
lemma fnTranslationC_translate (σ : Sentence ℒλ) :
    fnTranslationC.translate σ = fnTranslation.translate σ :=
  DirectTranslation.translate_congr fnTranslationC fnTranslation rfl (fun _ => rfl)
    (fun _ => rfl) σ

/-- **`𝗡𝗙` with the Axiom of Counting interprets FunctionNF with count.** -/
instance nfcInterpretsFNC : 𝗡𝗙𝗖 ⊳ 𝗙𝗡𝗙𝗖 where
  trln := fnTranslationC
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ hTC
    obtain ⟨hNF, hC⟩ := nfc_models hTC
    have := hNF
    rw [fnTranslationC_translate]
    refine DirectTranslation.Model.translate_iff.mpr ?_
    rcases hφ with hφ | hφ
    · exact models_theory_iff.mp fnModel_models φ hφ
    · have e : φ = FNF.Axiom.count := hφ
      rw [e]
      exact fnModel_count hC

end NFFn

/-- **`𝗡𝗙𝗖` interprets `𝗡𝗙𝗨𝗜𝗖` through FunctionNF with count.** -/
@[instance_reducible] def nfcInterpretsNFUICviaFn : 𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖 :=
  DirectInterpretation.comp FNF.fncInterpretsNFUIC NFFn.nfcInterpretsFNC

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.NFFn.fnModel_counting
#print axioms FFL.FirstOrder.SetTheory.NFFn.nfcInterpretsFNC
#print axioms FFL.FirstOrder.SetTheory.nfcInterpretsNFUIC
