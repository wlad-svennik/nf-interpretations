module

public import FnInterpretsNFU
public import CountWitness
public import CountBridge

@[expose] public section

set_option autoImplicit false

/-!
# FunctionNF with a Counting axiom

Two axioms in the language of FunctionNF. Both say that some part of the passage from `x` to
the constant function `K x = λy.x`, which raises the level by one, exists as an object.

* `Axiom.countChain` (**count′**): there are `κ`, `X` and `a` with `X · a = ⊤` such that every `x`
  with `X · x = ⊤` has `X · (κ · x) = ⊤`, `κ · x ≠ a` and `(κ · x) · y = x` for all `y`.
  So `κ` is `K` on the members of `X`, which `K` maps into `X` without reaching `a`.
* `Axiom.count` (**count**): for every Church numeral `n`, `n S 0 = n`. Here `0 = λf.λx.x` and
  `S = λn.λf.λx.f (n f x)` are given by their equations, and `n` is a Church numeral when
  `P · n = ⊤` for every `P` with `P · 0 = ⊤` and `P · m = ⊤ → P · (S · m) = ⊤`.

The theories: `𝗙𝗡𝗙𝗞 = 𝗙𝗡𝗙 ∪ {countChain}` and `𝗙𝗡𝗙𝗖 = 𝗙𝗡𝗙 ∪ {count}`.

This file states the axioms, says what they mean in a structure, and proves the first
interpretation:

* `fnkInterpretsNFUIC : 𝗙𝗡𝗙𝗞 ⊳ 𝗡𝗙𝗨𝗜𝗖`, FunctionNF with count′ interprets NFU + Infinity + the
  Axiom of Counting, by the translation of `FnInterpretsNFU.lean`.
-/

namespace FFL.FirstOrder

namespace FNF

open JensenNFU (TFm IsNFU UnivInfinite Counting IsNatN IsSuccN IsZeroN)
open DirectTranslation

/-! ### The axioms -/

namespace Axiom

/-- **count′.** `∃κ X a. X·a = ⊤ ∧ ∀x. X·x = ⊤ → X·(κ·x) = ⊤ ∧ κ·x ≠ a ∧ ∀y. (κ·x)·y = x`. -/
def countChain : Sentence ℒλ :=
  ∃¹ ∃¹ ∃¹ (eqF (appT #1 #0) ttT ⋏
    (∀¹ (eqF (appT #2 #0) ttT 🡒
      (eqF (appT #2 (appT #3 #0)) ttT ⋏ ((∼(eqF (appT #3 #0) #1)) ⋏
        (∀¹ (eqF (appT (appT #4 #1) #0) #1)))))))

/-- **count.** For all `z` and `s`: if `z·f·x = x` for all `f`, `x`, and
`s·n·f·x = f·(n·f·x)` for all `n`, `f`, `x`, then every Church numeral `n` for this zero and
successor has `n·s·z = n`. -/
def count : Sentence ℒλ :=
  ∀¹ ∀¹ ((∀¹ ∀¹ (eqF (appT (appT #3 #1) #0) #0)) 🡒
    ((∀¹ ∀¹ ∀¹ (eqF (appT (appT (appT #3 #2) #1) #0) (appT #1 (appT (appT #2 #1) #0)))) 🡒
      (∀¹ ((∀¹ (eqF (appT #0 #3) ttT 🡒
            ((∀¹ (eqF (appT #1 #0) ttT 🡒 eqF (appT #1 (appT #3 #0)) ttT)) 🡒
              eqF (appT #0 #1) ttT))) 🡒
        eqF (appT (appT #0 #1) #2) #0))))

end Axiom

/-! ### What they say in a structure -/

section meaning

variable (M : Type*) [s : Tarski.Structure ℒλ M]

/-- **count′** in a structure. -/
def CountChain : Prop :=
  ∃ κ X a : M, App X a = TT ∧
    ∀ x, App X x = TT → App X (App κ x) = TT ∧ App κ x ≠ a ∧ ∀ y, App (App κ x) y = x

variable {M}

/-- `z` is the Church numeral zero: `z·f·x = x`. -/
def IsCZero (z : M) : Prop := ∀ f x, App (App z f) x = x

/-- `s` is the successor of Church numerals: `s·n·f·x = f·(n·f·x)`. -/
def IsCSucc (s' : M) : Prop := ∀ n f x, App (App (App s' n) f) x = App f (App (App n f) x)

/-- `n` is a Church numeral for the zero `z` and the successor `s`. -/
def IsChurch (z s' n : M) : Prop :=
  ∀ P, App P z = TT → (∀ m, App P m = TT → App P (App s' m) = TT) → App P n = TT

variable (M)

/-- **count** in a structure. -/
def CountChurch : Prop :=
  ∀ z s' : M, IsCZero z → IsCSucc s' → ∀ n, IsChurch z s' n → App (App n s') z = n

variable {M} [Tarski.Structure.Eq ℒλ M] [Nonempty M]

lemma models_countChain_iff : M↓[ℒλ] ⊧ Axiom.countChain ↔ CountChain M := by
  simp [models_iff, Axiom.countChain, CountChain, eval_eqF, val_appT, val_ttT]

lemma models_count_iff : M↓[ℒλ] ⊧ Axiom.count ↔ CountChurch M := by
  simp [models_iff, Axiom.count, CountChurch, IsCZero, IsCSucc, IsChurch, eval_eqF, val_appT,
    val_ttT]

end meaning

end FNF

/-! ### The theories -/

/-- FunctionNF with count′. -/
abbrev FunctionNFChain : Theory ℒλ := 𝗙𝗡𝗙 ∪ {FNF.Axiom.countChain}

notation "𝗙𝗡𝗙𝗞" => FunctionNFChain

/-- FunctionNF with count. -/
abbrev FunctionNFCount : Theory ℒλ := 𝗙𝗡𝗙 ∪ {FNF.Axiom.count}

notation "𝗙𝗡𝗙𝗖" => FunctionNFCount

instance : 𝗙𝗡𝗙 ⪯ 𝗙𝗡𝗙𝗞 := inferInstance

instance : 𝗙𝗡𝗙 ⪯ 𝗙𝗡𝗙𝗖 := inferInstance

instance : 𝗘𝗤 _ ⪯ 𝗙𝗡𝗙𝗞 :=
  let : 𝗘𝗤 _ ⪯ 𝗙𝗡𝗙 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

instance : 𝗘𝗤 _ ⪯ 𝗙𝗡𝗙𝗖 :=
  let : 𝗘𝗤 _ ⪯ 𝗙𝗡𝗙 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

namespace FNF

open JensenNFU (TFm IsNFU UnivInfinite Counting IsNatN IsSuccN IsZeroN)
open DirectTranslation

/-! ### Transport of the Axiom of Counting along a bijection -/

section transport

variable {N M : Type} {memN : N → N → Prop} {memM : M → M → Prop} (e : N → M)

theorem isZeroN_map (hsurj : Function.Surjective e) (hmem : ∀ a b, memN a b ↔ memM (e a) (e b))
    (z : N) : IsZeroN memN z ↔ IsZeroN memM (e z) := by
  constructor
  · intro h x
    obtain ⟨x', rfl⟩ := hsurj x
    rw [← hmem, h x']
    constructor
    · intro h' w
      obtain ⟨w', rfl⟩ := hsurj w
      rw [← hmem]
      exact h' w'
    · intro h' w
      rw [hmem]
      exact h' (e w)
  · intro h x
    rw [hmem, h (e x)]
    constructor
    · intro h' w
      rw [hmem]
      exact h' (e w)
    · intro h' w
      obtain ⟨w', rfl⟩ := hsurj w
      rw [← hmem]
      exact h' w'

theorem isSuccN_map (hinj : Function.Injective e) (hsurj : Function.Surjective e)
    (hmem : ∀ a b, memN a b ↔ memM (e a) (e b)) (k k' : N) :
    IsSuccN memN k k' ↔ IsSuccN memM (e k) (e k') := by
  have key : ∀ y : N, (∃ x, memN x k ∧ ∃ b, ¬memN b x ∧ ∀ z, memN z y ↔ memN z x ∨ z = b) ↔
      ∃ x, memM x (e k) ∧ ∃ b, ¬memM b x ∧ ∀ z, memM z (e y) ↔ memM z x ∨ z = b := by
    intro y
    constructor
    · rintro ⟨x, hx, b, hb, h⟩
      refine ⟨e x, (hmem _ _).mp hx, e b, fun hc => hb ((hmem _ _).mpr hc), fun z => ?_⟩
      obtain ⟨z', rfl⟩ := hsurj z
      rw [← hmem, ← hmem, h z']
      exact or_congr Iff.rfl ⟨fun h' => by rw [h'], fun h' => hinj h'⟩
    · rintro ⟨x, hx, b, hb, h⟩
      obtain ⟨x', rfl⟩ := hsurj x
      obtain ⟨b', rfl⟩ := hsurj b
      refine ⟨x', (hmem _ _).mpr hx, b', fun hc => hb ((hmem _ _).mp hc), fun z => ?_⟩
      rw [hmem, hmem, h (e z)]
      exact or_congr Iff.rfl ⟨fun h' => hinj h', fun h' => by rw [h']⟩
  constructor
  · intro h y
    obtain ⟨y', rfl⟩ := hsurj y
    rw [← hmem, h y']
    exact key y'
  · intro h y
    rw [hmem, h (e y)]
    exact (key y).symm

theorem isNatN_map (hinj : Function.Injective e) (hsurj : Function.Surjective e)
    (hmem : ∀ a b, memN a b ↔ memM (e a) (e b)) (n : N) :
    IsNatN memN n ↔ IsNatN memM (e n) := by
  constructor
  · intro h F
    obtain ⟨F', rfl⟩ := hsurj F
    rintro ⟨h0, hs⟩
    rw [← hmem]
    refine h F' ⟨fun z hz => ?_, fun k hk k' hk' => ?_⟩
    · rw [hmem]
      exact h0 (e z) ((isZeroN_map e hsurj hmem z).mp hz)
    · rw [hmem]
      exact hs (e k) ((hmem _ _).mp hk) (e k') ((isSuccN_map e hinj hsurj hmem k k').mp hk')
  · intro h F
    rintro ⟨h0, hs⟩
    rw [hmem]
    refine h (e F) ⟨fun z hz => ?_, fun k hk k' hk' => ?_⟩
    · obtain ⟨z', rfl⟩ := hsurj z
      rw [← hmem]
      exact h0 z' ((isZeroN_map e hsurj hmem z').mpr hz)
    · obtain ⟨k₁, rfl⟩ := hsurj k
      obtain ⟨k₂, rfl⟩ := hsurj k'
      rw [← hmem]
      exact hs k₁ ((hmem _ _).mpr hk) k₂ ((isSuccN_map e hinj hsurj hmem k₁ k₂).mpr hk')

/-- The Axiom of Counting passes from a structure to an isomorphic one. -/
theorem counting_of_equiv (hinj : Function.Injective e) (hsurj : Function.Surjective e)
    (hmem : ∀ a b, memN a b ↔ memM (e a) (e b)) (h : Counting memM) : Counting memN := by
  intro n hn x hx
  obtain ⟨y, hy, hys⟩ := h (e n) ((isNatN_map e hinj hsurj hmem n).mp hn) (e x) ((hmem _ _).mp hx)
  obtain ⟨y', rfl⟩ := hsurj y
  refine ⟨y', (hmem _ _).mpr hy, fun s' => ?_⟩
  rw [hmem, hys (e s')]
  constructor
  · rintro ⟨a, ha, h'⟩
    obtain ⟨a', rfl⟩ := hsurj a
    refine ⟨a', (hmem _ _).mpr ha, fun z => ?_⟩
    rw [hmem, h' (e z)]
    exact ⟨fun h'' => hinj h'', fun h'' => by rw [h'']⟩
  · rintro ⟨a, ha, h'⟩
    refine ⟨e a, (hmem _ _).mp ha, fun z => ?_⟩
    obtain ⟨z', rfl⟩ := hsurj z
    rw [← hmem, h' z']
    exact ⟨fun h'' => by rw [h''], fun h'' => hinj h''⟩

/-- A structure, given with its relation symbols, that has the Axiom of Counting satisfies the
sentence. -/
theorem models_counting' {W : Type} [SetStructure W] [Nonempty W] [s : Tarski.Structure ℒₛₑₜ W]
    [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (h : Counting (fun a b : W => a ∈ b)) : W↓[ℒₛₑₜ] ⊧ SetTheory.Axiom.counting := by
  rcases SetTheory.standardStructure_unique W s
  exact SetTheory.models_counting_iff.mpr h

end transport

/-! ### The translation, for an extension of FunctionNF -/

/-- **The translation of the language of set theory into a theory in the language of
FunctionNF**: the formulas are those of `nfuTranslation`. -/
def nfuTranslationOf (T : Theory ℒλ) [𝗘𝗤 _ ⪯ T] : DirectTranslation T ℒₛₑₜ where
  domain := ⟨⊤⟩
  rel := nfuRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    simp [models_iff, Semiformula.Operator.val]
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : nfuRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {T : Theory ℒλ} [𝗘𝗤 _ ⪯ T]
variable {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [hT : M↓[ℒλ] ⊧* T] [hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

/-- The membership relation of the interpreted structure. -/
instance nfuModelOf_setStructure : SetStructure ((nfuTranslationOf T).Model M) :=
  ⟨fun y x ↦ Mem (x : M) (y : M)⟩

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hT hM in
lemma nfuModelOf_mem_iff (a b : (nfuTranslationOf T).Model M) : a ∈ b ↔ Mem (a : M) (b : M) :=
  Iff.rfl

omit hM in
instance nfuModelOf_mem : Tarski.Structure.Mem ℒₛₑₜ ((nfuTranslationOf T).Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, Semiformula.eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : (nfuTranslationOf T).Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact memφ_val _ _

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hT hM in
/-- An object of the model, as an object of the interpreted structure. -/
def toModelOf (a : M) : (nfuTranslationOf T).Model M :=
  ⟨a, by simp [DirectTranslation.Dom, nfuTranslationOf, Semiformula.Operator.val]⟩

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hT hM in
lemma coe_injective :
    Function.Injective (fun a : (nfuTranslationOf T).Model M => (a : M)) :=
  fun a b h => by cases a; cases b; cases h; rfl

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hT hM in
lemma coe_surjective :
    Function.Surjective (fun a : (nfuTranslationOf T).Model M => (a : M)) :=
  fun a => ⟨toModelOf a, rfl⟩

/-- In a model of an extension of `𝗙𝗡𝗙`, the interpreted structure is a model of `𝗡𝗙𝗨𝗜`. -/
theorem nfuModelOf_models : ((nfuTranslationOf T).Model M)↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜 :=
  models_nfui' (isNFU_of_equiv _ coe_injective coe_surjective (fun a b => nfuModelOf_mem_iff a b)
      isNFU)
    (univInfinite_of_equiv _ coe_injective coe_surjective (fun a b => nfuModelOf_mem_iff a b)
      univInfinite)

omit hM in
/-- If the sets of the model satisfy the Axiom of Counting, the interpreted structure satisfies
the sentence. -/
theorem nfuModelOf_models_counting (h : Counting (Mem (M := M))) :
    ((nfuTranslationOf T).Model M)↓[ℒₛₑₜ] ⊧ SetTheory.Axiom.counting :=
  models_counting' (counting_of_equiv _ coe_injective coe_surjective
    (fun a b => nfuModelOf_mem_iff a b) h)

/-- In a model of an extension of `𝗙𝗡𝗙` whose sets satisfy the Axiom of Counting, the
interpreted structure is a model of `𝗡𝗙𝗨𝗜𝗖`. -/
theorem nfuModelOf_models_nfuic (h : Counting (Mem (M := M))) :
    ((nfuTranslationOf T).Model M)↓[ℒₛₑₜ] ⊧* 𝗡𝗙𝗨𝗜𝗖 := by
  refine models_theory_iff.mpr fun φ hφ => ?_
  rcases hφ with hφ | hφ
  · exact models_theory_iff.mp nfuModelOf_models φ hφ
  · have e : φ = SetTheory.Axiom.counting := hφ
    rw [e]
    exact nfuModelOf_models_counting h

end model

/-! ### The sets of a model of FunctionNF as a model of NFU + Infinity -/

section cut

variable {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

local infixl:70 " ⬝ " => App

instance functionCut_infinity : Fact (FunctionCut.model (M := M)).Infinity :=
  ⟨FunctionCut.infinity⟩

/-- The Axiom of Counting for the sets of the model, from the statement with `T`. -/
theorem counting_of_T (h : ∀ n : (FunctionCut.model (M := M)).Num,
    (FunctionCut.model (M := M)).T n = n) : Counting (Mem (M := M)) :=
  (FunctionCut.model (M := M)).counting_iff_T.mpr h

/-- The statement with `T`, from the Axiom of Counting for the sets of the model. -/
theorem T_of_counting (h : Counting (Mem (M := M))) (n : (FunctionCut.model (M := M)).Num) :
    (FunctionCut.model (M := M)).T n = n :=
  (FunctionCut.model (M := M)).counting_iff_T.mp h n

/-- **A strongly cantorian set with a proper injection into itself gives the Axiom of
Counting.** The statement of `CountSet.model_with_strong_dedekind`, for the model
`FunctionCut.model` itself. -/
theorem T_eq_of_strong_dedekind (d : M) (strong : CountSet.Strong d)
    (ded : CountSet.Dedekind d) (n : (FunctionCut.model (M := M)).Num) :
    (FunctionCut.model (M := M)).T n = n := by
  classical
  let Mo := FunctionCut.model (M := M)
  have mm (a b : M) : Mo.mem a b ↔ Mem a b := Iff.rfl
  have isSet {x : M} (hx : IsSet x) : Mo.isSet x := hx
  have one (a : M) : Mo.sing a = sing a := Mo.ext (Mo.sing_isSet a) (isSet isSet_sing)
    (fun z => Mo.mem_sing.trans mem_sing.symm)
  have pair (a b : M) : Mo.up a b = upr a b := Mo.ext (Mo.up_isSet a b) (isSet isSet_upr)
    (fun z => Mo.mem_up.trans mem_upr.symm)
  have op (a b : M) : Mo.op a b = kp a b := by
    simp only [NFUCut.Model.op, kp, one, pair]
  obtain ⟨g, _, hg⟩ := strong
  have sc : Mo.SC d := by
    refine ⟨g, fun p => ?_⟩
    simpa only [mm, op, one] using hg p
  obtain ⟨f, t, _, inj, ht, miss⟩ := ded
  let F : M → M := fun x => if h : Mem x d then (inj.tot x h).choose else x
  have spec (x : M) (h : Mem x d) : Ap f x (F x) := by
    simpa only [F, dite_eq_left h] using (inj.tot x h).choose_spec
  exact NFUCut.Model.OrbitCounting.counting Mo d f t F sc ht
    (fun x hx => (inj.dom _ _ (spec x hx)).2)
    (fun x y hx hy eq => inj.inj _ _ _ (spec x hx) (eq ▸ spec y hy))
    (fun x hx eq => miss x (eq ▸ spec x hx))
    (fun x y hx => by
      rw [op]
      change Ap f x y ↔ F x = y
      exact ⟨fun h => inj.func _ _ _ (spec x hx) h, fun h => h ▸ spec x hx⟩) n

/-! ### count′ gives the Axiom of Counting -/

/-- **In a model of FunctionNF with count′, the sets satisfy the Axiom of Counting.** The
members of `X` form a strongly cantorian set, because `κ` gives the singleton map on it, and
`κ` is an injection of it into itself that does not reach `a`. -/
theorem counting_of_countChain (h : CountChain M) : Counting (Mem (M := M)) := by
  obtain ⟨κ, X, a, ha, hX⟩ := h
  -- the set of the `x` with `X · x = ⊤`
  obtain ⟨d, hd, hmem⟩ : ∃ d : M, IsSet d ∧ ∀ x, Mem x d ↔ X ⬝ x = TT :=
    (BT.appTT (Γ := [0, 1]) 1 0 0 rfl rfl).set (fun _ => X)
  have hκ : ∀ x, Mem x d → Mem (κ ⬝ x) d ∧ κ ⬝ x ≠ a ∧ ∀ y, κ ⬝ x ⬝ y = x := fun x hx => by
    obtain ⟨h1, h2, h3⟩ := hX x ((hmem x).mp hx)
    exact ⟨(hmem _).mpr h1, h2, h3⟩
  -- the graph of the singleton map on `d`
  obtain ⟨g, hg, lift⟩ := CountSet.liftGraph d κ a
  have strong : CountSet.Strong d := by
    refine ⟨g, hg, fun p => ?_⟩
    rw [lift]
    constructor
    · rintro ⟨x, y, _, _, pair, mem, rfl, rfl, rfl⟩
      exact ⟨x, mem, by simpa only [(hκ x mem).2.2 a] using pair⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, sing x, κ ⬝ x, x, rfl, hx, rfl, (hκ x hx).2.2 a, rfl⟩
  -- the graph of `κ` on `d`
  obtain ⟨f, hf, graph⟩ := CountSet.graph d κ
  have appgraph (u v : M) : Ap f u v ↔ Mem u d ∧ κ ⬝ u = v := by
    change Mem (kp u v) f ↔ _
    rw [graph]
    constructor
    · rintro ⟨x, y, p, mem, val⟩
      obtain ⟨rfl, rfl⟩ := kp_inj p
      exact ⟨mem, val⟩
    · rintro ⟨mem, val⟩
      exact ⟨u, v, rfl, mem, val⟩
  have inj : Inj f d d := by
    constructor
    · intro x y hxy
      obtain ⟨mem, rfl⟩ := (appgraph _ _).mp hxy
      exact ⟨mem, (hκ x mem).1⟩
    · exact fun x hx => ⟨_, (appgraph _ _).mpr ⟨hx, rfl⟩⟩
    · intro x y z hy hz
      exact ((appgraph _ _).mp hy).2.symm.trans ((appgraph _ _).mp hz).2
    · intro x y z hx hy
      obtain ⟨mx, ex⟩ := (appgraph _ _).mp hx
      obtain ⟨my, ey⟩ := (appgraph _ _).mp hy
      have := congrArg (fun w => w ⬝ a) (ex.trans ey.symm)
      simpa only [(hκ x mx).2.2 a, (hκ y my).2.2 a] using this
  have ded : CountSet.Dedekind d :=
    ⟨f, a, hf, inj, (hmem a).mpr ha, fun x hx => by
      obtain ⟨mx, ex⟩ := (appgraph _ _).mp hx
      exact (hκ x mx).2.1 ex⟩
  exact counting_of_T (T_eq_of_strong_dedekind d strong ded)

end cut

/-! ### The interpretation -/

section

variable {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]

/-- A model of `𝗙𝗡𝗙𝗞` is a model of `𝗙𝗡𝗙` and satisfies count′. -/
lemma fnk_models (hT : M↓[ℒλ] ⊧* 𝗙𝗡𝗙𝗞) : M↓[ℒλ] ⊧* 𝗙𝗡𝗙 ∧ CountChain M :=
  ⟨models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hT φ (Or.inl hφ),
    models_countChain_iff.mp (models_theory_iff.mp hT _ (Or.inr rfl))⟩

/-- A model of `𝗙𝗡𝗙𝗖` is a model of `𝗙𝗡𝗙` and satisfies count. -/
lemma fnc_models (hT : M↓[ℒλ] ⊧* 𝗙𝗡𝗙𝗖) : M↓[ℒλ] ⊧* 𝗙𝗡𝗙 ∧ CountChurch M :=
  ⟨models_theory_iff.mpr fun φ hφ => models_theory_iff.mp hT φ (Or.inl hφ),
    models_count_iff.mp (models_theory_iff.mp hT _ (Or.inr rfl))⟩

end

/-- **FunctionNF with count′ interprets NFU + Infinity + the Axiom of Counting.** -/
instance fnkInterpretsNFUIC : 𝗙𝗡𝗙𝗞 ⊳ 𝗡𝗙𝗨𝗜𝗖 where
  trln := nfuTranslationOf 𝗙𝗡𝗙𝗞
  interpret_theory φ hφ := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    obtain ⟨hM, hc⟩ := fnk_models hT
    have := hM
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp (nfuModelOf_models_nfuic (counting_of_countChain hc)) φ hφ)

end FNF

end FFL.FirstOrder

#print axioms FFL.FirstOrder.FNF.counting_of_countChain
#print axioms FFL.FirstOrder.FNF.fnkInterpretsNFUIC
