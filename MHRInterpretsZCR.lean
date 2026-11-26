module

public import ClassZSound
public import NFURank

@[expose] public section

/-!
# `𝗠𝗛𝗥 ⊳ 𝗭𝗖𝗥` and `𝗡𝗙𝗖 ⊳ 𝗭𝗖𝗥`

`𝗠𝗛𝗥` is `𝗠𝗛` with the rank axioms, and `𝗭𝗖𝗥` is `𝗭𝗖` with the rank axioms (`MHLRank.lean`).

In a model `V` of `𝗠𝗛𝗥` there need not be a set that is a model of `𝗭𝗖𝗥`: the sets of
`MHLRank.lean` satisfy the rank axioms up to a standard number only. The interpretation is a
Henkin model built inside `V`:

* the sentence is `sigmaZ` (equality and the finite theory of classes of `ClassZ.lean`), and the
  family is `chiU.φ` at the terms for the numbers of `V`, cut off at the set `Jset` of the
  numbers for which the instances are consistent with the sentence in the sense of `HkCut.lean`;
* every standard number is in the cut (`nm_mem_kset`, from the sets of `MHLRank.lean`);
* the leftmost assignment `S` (`HkTree.lean`) makes the sentence and the instances in the cut
  true, so its structure `Dom S` satisfies them (`holds_eval`), and the sets of `Dom S` satisfy
  `𝗭𝗖` and every rank axiom (`sets_models_zc`, `hasRank_sets`): **`henkin_models_zcr`**.

The domain and the membership of that structure are given by formulas of `ℒₛₑₜ` without
parameters (`domZU`, `memZU`): all the sets that enter the construction are determined by
conditions that are formulas (`Pack`).

* **`mhrInterpretsZCR : 𝗠𝗛𝗥 ⊳ 𝗭𝗖𝗥`**.
* **`nfcInterpretsZCR : 𝗡𝗙𝗖 ⊳ 𝗭𝗖𝗥`**, **`nfuicInterpretsZCR : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭𝗖𝗥`**, by composition
  with `nfcInterpretsMHR`, `nfuicInterpretsMHR` (`NFURank.lean`).
* `nfcInterpretsZC : 𝗡𝗙𝗖 ⊳ 𝗭𝗖` and `nfcInterpretsZR : 𝗡𝗙𝗖 ⊳ 𝗭𝗥`: parts of `𝗭𝗖𝗥`.
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula DirectTranslation

namespace MH

/-! ### The model of `𝗭𝗖𝗥` inside a model of `𝗠𝗛` with the rank axioms -/

section core

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- **The sets of the structure of the leftmost assignment are a model of `𝗭𝗖𝗥`.** -/
theorem henkin_models_zcr (hR : ∀ n : ℕ, HasRank n V) {P S : V} (hP : CanP P)
    (hS : IsS sigmaZ chiU.φ S P) :
    ∃ _ : EqOK S, ∃ _ : Nonempty (SetsOf (Dom S)), (SetsOf (Dom S))↓[ℒₛₑₜ] ⊧* 𝗭𝗖𝗥 := by
  have hK : ∀ n : ℕ, (nm n : V) ∈ Kset sigmaZ chiU.φ P := fun n => nm_mem_kset hR hP n
  have h0 : (∅ : V) ∈ Kset sigmaZ chiU.φ P := hK 0
  obtain ⟨hσ, hχ⟩ := can_holds sigmaZ chiU.φ hP h0 hS
  have hσ' : Holds S eqAx 0 ![] ∧ Holds S thetaZ (0 + cnt eqAx) ![] := hσ
  obtain ⟨h1, h2⟩ := hσ'
  have hE : EqOK S := eqOK_of_holds h1
  refine ⟨hE, ?_⟩
  have key : ∀ f : Fin 0 → Dom S, Eval (M := Dom S) f Empty.elim thetaZ →
      Eval (M := Dom S) ![] Empty.elim thetaZ := fun f h => by
    have e : f = ![] := funext fun i => i.elim0
    rw [← e]
    exact h
  have hθ : Eval (M := Dom S) ![] Empty.elim thetaZ :=
    key _ (holds_eval hE thetaZ _ ![] (fun i => i.elim0) h2)
  obtain ⟨hne, hZC⟩ := sets_models_zc hθ
  refine ⟨hne, ?_⟩
  let d : ℕ → Dom S := fun j ↦ repD hE (dn (nm j)) (dn_mem_om (nm_mem_om j))
  have hd : ∀ j, ChiR (Dom S) (d (j + 1)) (d j) (d 0) := by
    intro j
    have hj : (nm j : V) ∈ Jset sigmaZ chiU.φ P := jset_nm sigmaZ chiU.φ hK j
    have h3 := holds_eval hE chiU.φ _ (envJ (nm j)) (envJ_mem_om (nm_mem_om j)) (hχ _ hj)
    exact (chiU.eval (Dom S) _).mp h3
  exact models_theory_iff.mpr fun φ hφ => by
    rcases hφ with hφ | ⟨n, rfl⟩
    · exact models_theory_iff.mp hZC φ hφ
    · exact models_rank_iff.mpr (hasRank_sets d hd n)

end core

/-! ### The formulas -/

section fdefs

variable {V : Type} [SetStructure V]

/-- `o` is the set of the finite ordinals. -/
def IsOm (o : V) : Prop := ∀ x, x ∈ o ↔ NumR x

/-- `PO` is the power set of `o`. -/
def IsPow (PO o : V) : Prop := ∀ s, s ∈ PO ↔ ∀ z, z ∈ s → z ∈ o

/-- `K` is the set `Kset`. -/
def IsK (K o PO P : V) : Prop := ∀ n, n ∈ K ↔ (n ∈ o ∧ KDef sigmaZ chiU.φ n o PO P)

/-- `J` is the set `Jset`. -/
def IsJ (J o K : V) : Prop := ∀ j, j ∈ J ↔ (j ∈ o ∧ JDef j K)

/-- **The sets of the construction**: `ω`, its power set, the triples of the pairing function,
the two sets of the cut, and the leftmost assignment. -/
def Pack (o PO P K J S : V) : Prop :=
  IsOm o ∧ (IsPow PO o ∧ (CanP P ∧ (IsK K o PO P ∧ (IsJ J o K ∧
    Can (SatR sigmaZ chiU.φ) o PO S P o J))))

/-- `t` is the least number of its class of the equality of `S`. -/
def IsRepR (P o S t : V) : Prop := t ∈ o ∧ ∀ t', t' ∈ t → ∀ α, α ∈ S → ¬AtomR P o 1 t' t α

/-- The membership of `S`. -/
def MemR (P o S x y : V) : Prop := ∃ α, α ∈ S ∧ AtomR P o 0 x y α

/-- **The domain of the interpretation**: the sets of the structure of the leftmost
assignment. -/
def DomZ (V : Type) [SetStructure V] (x : V) : Prop :=
  ∃ o PO P K J S : V, Pack o PO P K J S ∧
    (IsRepR P o S x ∧ ∃ y, IsRepR P o S y ∧ MemR P o S x y)

/-- **The membership of the interpretation.** -/
def MemZ (V : Type) [SetStructure V] (x y : V) : Prop :=
  ∃ o PO P K J S : V, Pack o PO P K J S ∧ MemR P o S x y

end fdefs

/-- A formula that defines a relation in every structure. -/
def udefOfF {k : ℕ} {R : MRel k} (d : FDef R) : UDef R := ⟨d.φ, d.eval⟩

def isOmU : UDef (k := 1) (fun V _ v ↦ IsOm (v 0)) :=
  (UDef.all ((UDef.mem 0 1).iff ((UDef.ofB numB).comp ![0]))).congr fun _ _ _ => Iff.rfl

def isPowU : UDef (k := 2) (fun V _ v ↦ IsPow (v 0) (v 1)) :=
  (UDef.all ((UDef.mem 0 1).iff (UDef.all ((UDef.mem 0 1).imp (UDef.mem 0 3))))).congr
    fun _ _ _ => Iff.rfl

def isKU : UDef (k := 4) (fun V _ v ↦ IsK (v 0) (v 1) (v 2) (v 3)) :=
  (UDef.all ((UDef.mem 0 1).iff ((UDef.mem 0 2).and
    ((UDef.ofB (kdefB sigmaZ chiU.φ)).comp ![0, 2, 3, 4])))).congr fun _ _ _ => Iff.rfl

def isJU : UDef (k := 3) (fun V _ v ↦ IsJ (v 0) (v 1) (v 2)) :=
  (UDef.all ((UDef.mem 0 1).iff ((UDef.mem 0 2).and
    ((UDef.ofB jdefB).comp ![0, 3])))).congr fun _ _ _ => Iff.rfl

def packU : UDef (k := 6) (fun V _ v ↦ Pack (v 0) (v 1) (v 2) (v 3) (v 4) (v 5)) :=
  ((isOmU.comp ![0]).and ((isPowU.comp ![1, 0]).and (((udefOfF canPF).comp ![2]).and
    ((isKU.comp ![3, 0, 1, 2]).and ((isJU.comp ![4, 0, 3]).and
      ((UDef.ofB (canB (satB sigmaZ chiU.φ))).comp ![0, 1, 5, 2, 0, 4])))))).congr
    fun _ _ _ => Iff.rfl

def isRepB : BDef (k := 4) (fun V _ v ↦ IsRepR (v 0) (v 1) (v 2) (v 3)) :=
  ((BDef.mem 3 1).and (BDef.ball 3 (BDef.ball 3
    ((atomB 1).comp ![2, 3, 1, 5, 0]).not))).congr fun _ _ _ => Iff.rfl

def memRB : BDef (k := 5) (fun V _ v ↦ MemR (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 2 ((atomB 0).comp ![1, 2, 4, 5, 0])).congr fun _ _ _ => Iff.rfl

def domZU : UDef (k := 1) (fun V _ v ↦ DomZ V (v 0)) :=
  (UDef.ex (UDef.ex (UDef.ex (UDef.ex (UDef.ex (UDef.ex
    ((packU.comp ![5, 4, 3, 2, 1, 0]).and (((UDef.ofB isRepB).comp ![3, 5, 0, 6]).and
      (UDef.ex (((UDef.ofB isRepB).comp ![4, 6, 1, 0]).and
        ((UDef.ofB memRB).comp ![4, 6, 1, 7, 0]))))))))))).congr fun _ _ _ => Iff.rfl

def memZU : UDef (k := 2) (fun V _ v ↦ MemZ V (v 0) (v 1)) :=
  (UDef.ex (UDef.ex (UDef.ex (UDef.ex (UDef.ex (UDef.ex
    ((packU.comp ![5, 4, 3, 2, 1, 0]).and
      ((UDef.ofB memRB).comp ![3, 5, 0, 6, 7])))))))).congr fun _ _ _ => Iff.rfl

/-! ### The formulas in a model of `𝗠𝗛` -/

section fmodel

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

theorem isOm_iff {o : V} : IsOm o ↔ o = (om : V) :=
  ⟨fun h => mem_ext fun x => (h x).trans numR_iff, fun h x => by rw [h]; exact numR_iff.symm⟩

theorem isPow_iff {PO : V} : IsPow PO (om : V) ↔ PO = (℘ om : V) := by
  have hp : ∀ s : V, s ∈ (℘ om : V) ↔ ∀ z, z ∈ s → z ∈ (om : V) := fun s =>
    ⟨fun h z hz => subset_def.mp (mem_power_iff.mp h) z hz, fun h => mem_power_iff.mpr h⟩
  exact ⟨fun h => mem_ext fun s => (h s).trans (hp s).symm, fun h s => by rw [h]; exact hp s⟩

theorem pack_iff {o PO P K J S : V} : Pack o PO P K J S ↔
    (o = (om : V) ∧ (PO = (℘ om : V) ∧ (CanP P ∧ (K = Kset sigmaZ chiU.φ P ∧
      (J = Jset sigmaZ chiU.φ P ∧ IsS sigmaZ chiU.φ S P))))) := by
  have hk : ∀ (P n : V), n ∈ Kset sigmaZ chiU.φ P ↔
      (n ∈ (om : V) ∧ KDef sigmaZ chiU.φ n (om : V) (℘ om) P) :=
    fun P n => mem_sepB (kdefB sigmaZ chiU.φ) _ _ n
  have hj : ∀ (K j : V), j ∈ sepB jdefB (om : V) ![K] ↔ (j ∈ (om : V) ∧ JDef j K) :=
    fun K j => mem_sepB jdefB _ _ j
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    obtain rfl := isOm_iff.mp h1
    obtain rfl := isPow_iff.mp h2
    have eK : K = Kset sigmaZ chiU.φ P := mem_ext fun n => (h4 n).trans (hk P n).symm
    subst eK
    have eJ : J = Jset sigmaZ chiU.φ P := mem_ext fun j => (h5 j).trans (hj _ j).symm
    subst eJ
    exact ⟨rfl, rfl, h3, rfl, rfl, h6⟩
  · rintro ⟨rfl, rfl, h3, rfl, rfl, h6⟩
    exact ⟨isOm_iff.mpr rfl, isPow_iff.mpr rfl, h3, fun n => hk P n, fun j => hj _ j, h6⟩

variable {P S : V} (hP : CanP P) (hS : IsS sigmaZ chiU.φ S P)

include hP in
theorem isRepR_iff (S t : V) : IsRepR P (om : V) S t ↔ IsRep S t := by
  refine and_congr_right fun ht => ?_
  constructor
  · intro h t' ht' hin
    exact h t' ht' _ hin ((atomR_iff hP 1 ((ord_om (V := V)).1 t ht t' ht') ht).mpr
      rfl)
  · intro h t' ht' α hα hat
    have := (atomR_iff hP 1 ((ord_om (V := V)).1 t ht t' ht') ht).mp hat
    exact h t' ht' (this ▸ hα)

include hP in
theorem memR_iff (S : V) {x y : V} (hx : x ∈ (om : V)) (hy : y ∈ (om : V)) :
    MemR P (om : V) S x y ↔ atm 0 x y ∈ S :=
  ⟨fun ⟨α, hα, hat⟩ => (atomR_iff hP 0 hx hy).mp hat ▸ hα,
    fun h => ⟨_, h, (atomR_iff hP 0 hx hy).mpr rfl⟩⟩

include hP hS

theorem pack_elim {o PO P' K J S' : V} (h : Pack o PO P' K J S') :
    o = (om : V) ∧ P' = P ∧ S' = S := by
  obtain ⟨rfl, rfl, h3, rfl, rfl, h6⟩ := pack_iff.mp h
  obtain rfl := canP_unique h3 hP
  exact ⟨rfl, rfl, isS_unique sigmaZ chiU.φ h6 hS⟩

theorem pack_intro :
    Pack (om : V) (℘ om) P (Kset sigmaZ chiU.φ P) (Jset sigmaZ chiU.φ P) S :=
  pack_iff.mpr ⟨rfl, rfl, hP, rfl, rfl, hS⟩

theorem memZ_iff {x y : V} (hx : x ∈ (om : V)) (hy : y ∈ (om : V)) :
    MemZ V x y ↔ atm 0 x y ∈ S := by
  constructor
  · rintro ⟨o, PO, P', K, J, S', hpack, h⟩
    obtain ⟨rfl, rfl, rfl⟩ := pack_elim hP hS hpack
    exact (memR_iff hP _ hx hy).mp h
  · intro h
    exact ⟨_, _, _, _, _, _, pack_intro hP hS, (memR_iff hP _ hx hy).mpr h⟩

/-- **The domain is the sets of the structure of the leftmost assignment.** -/
theorem domZ_iff (x : V) : DomZ V x ↔ ∃ h : IsRep S x, IsSet (⟨x, h⟩ : Dom S) := by
  constructor
  · rintro ⟨o, PO, P', K, J, S', hpack, hx, y, hy, hxy⟩
    obtain ⟨rfl, rfl, rfl⟩ := pack_elim hP hS hpack
    have hx' := (isRepR_iff hP _ x).mp hx
    have hy' := (isRepR_iff hP _ y).mp hy
    exact ⟨hx', ⟨y, hy'⟩, (memR_iff hP _ hx'.1 hy'.1).mp hxy⟩
  · rintro ⟨hx, ⟨y, hxy⟩⟩
    exact ⟨_, _, _, _, _, _, pack_intro hP hS, (isRepR_iff hP _ x).mpr hx, y.1,
      (isRepR_iff hP _ y.1).mpr y.2, (memR_iff hP _ hx.1 y.2.1).mpr hxy⟩

end fmodel

end MH

/-! ### The translation -/

/-- A structure that is isomorphic to a model of a theory, given with any structure for the
language, is a model of the theory. -/
theorem models_of_iso {A W : Type} [SetStructure A] [Nonempty A] [SetStructure W] [Nonempty W]
    [s : Tarski.Structure ℒₛₑₜ W] [Tarski.Structure.Eq ℒₛₑₜ W] [Tarski.Structure.Mem ℒₛₑₜ W]
    (π : A → W) (hsur : Function.Surjective π) (hmem : ∀ a a' : A, π a ∈ π a' ↔ a ∈ a')
    (heq : ∀ a a' : A, π a = π a' ↔ a = a') {T : SetTheory} (h : A↓[ℒₛₑₜ] ⊧* T) :
    W↓[ℒₛₑₜ] ⊧* T := by
  rcases standardStructure_unique W s
  refine models_theory_iff.mpr fun φ hφ => ?_
  have h1 : Eval (M := A) ![] Empty.elim φ := models_theory_iff.mp h φ hφ
  have h2 := (eval_isoG π hsur hmem heq φ ![] Empty.elim).mpr h1
  have e1 : (fun i ↦ π ((![] : Fin 0 → A) i)) = ![] := funext fun i => i.elim0
  have e2 : (fun x : Empty ↦ π (Empty.elim x)) = Empty.elim := funext fun x => x.elim
  rw [e1, e2] at h2
  exact h2

/-- The interpretation of the relation symbols: equality is itself, and membership is
`MH.MemZ`. -/
def zcRel : {k : ℕ} → (ℒₛₑₜ).Rel k → Semiformula.Operator ℒₛₑₜ k
  | _, Language.Set.Rel.eq => Semiformula.Operator.Eq.eq
  | _, Language.Set.Rel.mem => ⟨MH.memZU.φ⟩

lemma zcDomain_val_iff {M : Type} [SetStructure M] (x : M) :
    (⟨MH.domZU.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] ↔ MH.DomZ M x :=
  MH.domZU.eval M ![x]

lemma zcMem_val_iff {M : Type} [SetStructure M] (x y : M) :
    (⟨MH.memZU.φ⟩ : Semiformula.Operator ℒₛₑₜ 2).val ![x, y] ↔ MH.MemZ M x y :=
  MH.memZU.eval M ![x, y]

/-- In a model of `𝗠𝗛𝗥` the domain has a member. -/
theorem exists_domZ {M : Type} [SetStructure M] [Nonempty M] [hM : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗥] :
    ∃ x : M, MH.DomZ M x := by
  haveI : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := mhr_models_mh
  obtain ⟨P, hP⟩ := MH.exists_canP (V := M)
  obtain ⟨S, hS⟩ := MH.exists_isS MH.sigmaZ MH.chiU.φ (P := P)
  obtain ⟨hE, ⟨y⟩, -⟩ := MH.henkin_models_zcr (fun n => mhr_rank n) hP hS
  exact ⟨y.1.1, (MH.domZ_iff hP hS _).mpr ⟨y.1.2, y.2⟩⟩

/-- **The translation of `ℒₛₑₜ` into `𝗠𝗛𝗥`**: the domain is `MH.DomZ`, membership is `MH.MemZ`,
and equality is equality. -/
def zcTranslation : DirectTranslation 𝗠𝗛𝗥 ℒₛₑₜ where
  domain := ⟨MH.domZU.φ⟩
  rel := zcRel
  func := fun f ↦ Empty.elim f
  domain_nonempty := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    obtain ⟨x, hx⟩ := exists_domZ (M := M)
    suffices ∃ x : M, (⟨MH.domZU.φ⟩ : Semiformula.Operator ℒₛₑₜ 1).val ![x] by
      simpa [models_iff] using this
    exact ⟨x, (zcDomain_val_iff x).mpr hx⟩
  func_defined := fun f ↦ Empty.elim f
  preserve_eq := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ _
    have : zcRel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) = Semiformula.Operator.Eq.eq := rfl
    simp [models_iff, this, Semiformula.Operator.val, Semiformula.Operator.Eq.sentence_eq]

section model

variable {M : Type} [SetStructure M] [Nonempty M] [hM : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛𝗥]

/-- The membership relation of the interpreted structure. -/
instance zcModel_setStructure : SetStructure (zcTranslation.Model M) :=
  ⟨fun y x ↦ MH.MemZ M (x : M) (y : M)⟩

omit [Nonempty M] hM in
lemma zcModel_mem_iff (a b : zcTranslation.Model M) : a ∈ b ↔ MH.MemZ M (a : M) (b : M) :=
  Iff.rfl

instance zcModel_mem : Tarski.Structure.Mem ℒₛₑₜ (zcTranslation.Model M) where
  mem a b := by
    have h1 : (Semiformula.Operator.Mem.mem : Semiformula.Operator ℒₛₑₜ 2).val ![a, b] ↔
        Tarski.Structure.rel (L := ℒₛₑₜ) Language.Mem.mem ![a, b] := by
      simp [Semiformula.Operator.val, Semiformula.Operator.Mem.sentence_eq, eval_rel,
        Matrix.fun_eq_vec_two]
    rw [h1, Model.rel_iff]
    have h2 : (fun i ↦ ((![a, b] i : zcTranslation.Model M) : M)) = ![(a : M), (b : M)] := by
      funext i; fin_cases i <;> rfl
    rw [h2]
    exact zcMem_val_iff _ _

/-- **In a model of `𝗠𝗛𝗥`, the interpreted structure is a model of `𝗭𝗖𝗥`.** -/
theorem zcModel_models : (zcTranslation.Model M)↓[ℒₛₑₜ] ⊧* 𝗭𝗖𝗥 := by
  haveI : M↓[ℒₛₑₜ] ⊧* 𝗠𝗛 := mhr_models_mh
  obtain ⟨P, hP⟩ := MH.exists_canP (V := M)
  obtain ⟨S, hS⟩ := MH.exists_isS MH.sigmaZ MH.chiU.φ (P := P)
  obtain ⟨hE, hne, hZ⟩ := MH.henkin_models_zcr (fun n => mhr_rank n) hP hS
  have hi : Function.Injective (fun a : zcTranslation.Model M ↦ (a : M)) :=
    fun a b h => by cases a; cases b; cases h; rfl
  let π : MH.SetsOf (MH.Dom S) → zcTranslation.Model M := fun y =>
    ⟨y.1.1, (zcDomain_val_iff _).mpr ((MH.domZ_iff hP hS _).mpr ⟨y.1.2, y.2⟩)⟩
  refine models_of_iso π ?_ ?_ ?_ hZ
  · intro w
    obtain ⟨h, hs⟩ := (MH.domZ_iff hP hS _).mp ((zcDomain_val_iff _).mp w.dom)
    exact ⟨⟨⟨(w : M), h⟩, hs⟩, hi rfl⟩
  · intro a a'
    exact MH.memZ_iff hP hS a.1.2.1 a'.1.2.1
  · intro a a'
    constructor
    · intro h
      have h' : (a.1.1 : M) = a'.1.1 := congrArg (fun w : zcTranslation.Model M => (w : M)) h
      exact Subtype.ext (Subtype.ext h')
    · intro h
      rw [h]

end model

/-- **`𝗠𝗛` with the rank axioms interprets `𝗭𝗖` with the rank axioms**, by the translation
`zcTranslation`: the sets of a Henkin model of a finite theory of classes, built inside the
model. -/
instance mhrInterpretsZCR : 𝗠𝗛𝗥 ⊳ 𝗭𝗖𝗥 where
  trln := zcTranslation
  interpret_theory φ hφ := by
    apply SetTheory.complete.{0}
    intro M _ _ _
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp zcModel_models φ hφ)

/-- **NF with the Axiom of Counting interprets `𝗭𝗖` with the rank axioms.** -/
instance nfcInterpretsZCR : 𝗡𝗙𝗖 ⊳ 𝗭𝗖𝗥 :=
  DirectInterpretation.comp mhrInterpretsZCR nfcInterpretsMHR

/-- **NFU + Infinity + the Axiom of Counting interprets `𝗭𝗖` with the rank axioms.** -/
instance nfuicInterpretsZCR : 𝗡𝗙𝗨𝗜𝗖 ⊳ 𝗭𝗖𝗥 :=
  DirectInterpretation.comp mhrInterpretsZCR nfuicInterpretsMHR

/-- **NF with the Axiom of Counting interprets `𝗭𝗖`**: Zermelo set theory with the full
separation schema and the axiom of choice. -/
instance nfcInterpretsZC : 𝗡𝗙𝗖 ⊳ 𝗭𝗖 where
  trln := nfcInterpretsZCR.trln
  interpret_theory φ hφ := nfcInterpretsZCR.interpret_theory φ (Or.inl hφ)

/-- **NF with the Axiom of Counting interprets `𝗭𝗥`**: Zermelo set theory with the rank
axioms. -/
instance nfcInterpretsZR : 𝗡𝗙𝗖 ⊳ 𝗭𝗥 where
  trln := nfcInterpretsZCR.trln
  interpret_theory φ hφ :=
    nfcInterpretsZCR.interpret_theory φ (hφ.elim (fun h => Or.inl (Or.inl h)) Or.inr)

end FFL.FirstOrder.SetTheory

#print axioms FFL.FirstOrder.SetTheory.MH.henkin_models_zcr
#print axioms FFL.FirstOrder.SetTheory.mhrInterpretsZCR
#print axioms FFL.FirstOrder.SetTheory.nfcInterpretsZCR
#print axioms FFL.FirstOrder.SetTheory.nfuicInterpretsZCR
#print axioms FFL.FirstOrder.SetTheory.nfcInterpretsZC
#print axioms FFL.FirstOrder.SetTheory.nfcInterpretsZR
