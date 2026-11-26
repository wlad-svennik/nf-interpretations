module

public import HkRel

@[expose] public section

/-!
# Soundness: a set structure with a well-order gives an assignment

Inside a model `V` of `𝗠𝗛`. Let `A` be a set that includes `ω`, with a set `W` of pairs that is
total on `A` and for which every set of members of `A` that has a member has a least member.
Fix a sentence `σ₀` and a formula `χ` of three variables.

* The value `vl F t` of a number `t` is defined by recursion on `t` (`ord_rec`): the value of
  the witness `sk c (tup e)` of the existential quantifier number `c` of `σ₀` or `χ` is the
  least `b` in `A` such that the scope of the quantifier is true in `(A, ∈)` at `b` and the
  values of `e`, if there is one; the value of `dn j` is `j`. The clause of the recursion
  (`GR`) is bounded: truth in `(A, ∈)` is `RS` of `HkRel.lean`, and the values of an
  environment are collected in a valuation by `EV`.
* `Sg F`: the atomic sentences that are true for the values.
* **`holds_of_eval`**: a subformula of `σ₀` or `χ` that is true in `(A, ∈)` at the values of
  `e` is true under `Sg F` at `e`.
* **`sound_kset`**: if `σ₀` is true in `(A, ∈)`, and `χ` at `(j + 1, j, 0)` for every `j` below
  the number `n`, then `n` is in `Kset` (`HkCut.lean`).
-/

namespace FFL.FirstOrder.SetTheory

open Semiformula

namespace MH

/-! ### Bounded definitions -/

section rdefs

variable {V : Type} [SetStructure V]

/-- `f` has at most one value at every member of `β`. -/
def FunB (f β : V) : Prop :=
  ∀ q, q ∈ f → ∀ q', q' ∈ f → ∀ γ, γ ∈ β → ∀ u, u ∈ q → ∀ y, y ∈ u → ∀ u', u' ∈ q' →
    ∀ y', y' ∈ u' → (IsOp q γ y → (IsOp q' γ y' → y = y'))

/-- `s` codes the values under `f` of the first `n` entries of the environment `ε`. -/
def EV (P o A FS f γ : V) : ℕ → V → V → Prop
  | 0, _, s => ∀ p, p ∈ s → False
  | n + 1, ε, s => ∃ t, t ∈ γ ∧ ∃ ε', ε' ∈ o ∧ (PG P t ε' ε ∧ ∃ a, a ∈ A ∧ (Pr f t a ∧
      ∃ s', s' ∈ FS ∧ (EV P o A FS f γ n ε' s' ∧ ExtN o s s' n a)))

/-- `φ` is true in `(A, ∈)` at `b` and the valuation `s`. -/
def WitAt (o A FS : V) {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) (s b : V) : Prop :=
  ∃ s', s' ∈ FS ∧ (ExtN o s' s n b ∧ RS o A FS φ s')

/-- `b` is a witness, or there is none. -/
def DW (o A FS : V) {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) (s b : V) : Prop :=
  WitAt o A FS φ s b ∨ ¬∃ b', b' ∈ A ∧ WitAt o A FS φ s b'

/-- `y` is the least witness, or the least member of `A` if there is no witness. -/
def LeastW (o A FS W : V) {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) (s y : V) : Prop :=
  y ∈ A ∧ (DW o A FS φ s y ∧ ∀ b, b ∈ A → (DW o A FS φ s b → ¬Pr W b y))

/-- `γ` is the witness of the quantifier number `c`, with the scope `φ`, in some environment,
and `y` is its value. -/
def Here (P o A FS W f γ y : V) (c : ℕ) {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) : Prop :=
  ∃ ε, ε ∈ γ ∧ (SkR P o c ε γ ∧ ∃ s, s ∈ FS ∧
    (EV P o A FS f γ n ε s ∧ LeastW o A FS W φ s y))

/-- `γ` is a witness of an existential quantifier of the formula, and `y` is its value. -/
def StepR (P o A FS W f γ y : V) : {n : ℕ} → Semiformula ℒₛₑₜ Empty n → ℕ → Prop
  | _, .rel _ _, _ => False
  | _, .nrel _ _, _ => False
  | _, ⊤, _ => False
  | _, ⊥, _ => False
  | _, φ ⋏ ψ, c => StepR P o A FS W f γ y φ c ∨ StepR P o A FS W f γ y ψ (c + cnt φ)
  | _, φ ⋎ ψ, c => StepR P o A FS W f γ y φ c ∨ StepR P o A FS W f γ y ψ (c + cnt φ)
  | _, ∀¹ φ, c => StepR P o A FS W f γ y φ c
  | _, ∃¹ φ, c => Here P o A FS W f γ y c φ ∨ StepR P o A FS W f γ y φ (c + 1)

/-- `γ` is the term for the number `y`. -/
def DnR (P o γ y : V) : Prop := ∃ z, z ∈ o ∧ ((∀ w, w ∈ z → False) ∧ PG P z y γ)

/-- `y` is the least member of `A`. -/
def LeastA (A W y : V) : Prop := y ∈ A ∧ ∀ b, b ∈ A → ¬Pr W b y

variable (σ₀ : Semiformula ℒₛₑₜ Empty 0) (χ : Semiformula ℒₛₑₜ Empty 3)

/-- `γ` is a witness or a term for a number, and `y` is its value. -/
def MainR (P o A FS W f γ y : V) : Prop :=
  StepR P o A FS W f γ y σ₀ 0 ∨ (StepR P o A FS W f γ y χ (cnt σ₀) ∨ DnR P o γ y)

/-- **The clause of the recursion for the values.** -/
def GR (γ f y P o A FS W : V) : Prop :=
  FunB f γ ∧ (MainR σ₀ χ P o A FS W f γ y ∨
    ((¬∃ y', y' ∈ A ∧ MainR σ₀ χ P o A FS W f γ y') ∧ LeastA A W y))

/-- The atomic sentence `α` is true for the values `F`. -/
def SgDef (α P o A F : V) : Prop :=
  ∃ a, a ∈ α ∧ ∃ b, b ∈ α ∧ ∃ x, x ∈ A ∧ ∃ y, y ∈ A ∧ (Pr F a x ∧ (Pr F b y ∧
    ((AtomR P o 0 a b α ∧ x ∈ y) ∨ (AtomR P o 1 a b α ∧ x = y))))

end rdefs

def funBB : BDef (k := 2) (fun V _ v ↦ FunB (v 0) (v 1)) :=
  (BDef.ball 0 (BDef.ball 1 (BDef.ball 3 (BDef.ball 2 (BDef.ball 0 (BDef.ball 3 (BDef.ball 0
    ((isOpB.comp ![6, 4, 2]).imp ((isOpB.comp ![5, 4, 0]).imp (BDef.eq 2 0)))))))))).congr
    fun _ _ _ => Iff.rfl

def evB : (n : ℕ) → BDef (k := 8)
    (fun V _ v ↦ EV (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) n (v 6) (v 7))
  | 0 => (BDef.ball 7 BDef.fls).congr fun _ _ _ => Iff.rfl
  | n + 1 => (BDef.bex 5 (BDef.bex 2 ((pgB.comp ![2, 1, 0, 8]).and (BDef.bex 4
      ((prB.comp ![7, 2, 0]).and (BDef.bex 6 (((evB n).comp ![4, 5, 6, 7, 8, 9, 2, 0]).and
        ((extNB n).comp ![5, 11, 0, 1])))))))).congr fun _ _ _ => Iff.rfl

def witAtB {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) :
    BDef (k := 5) (fun V _ v ↦ WitAt (v 0) (v 1) (v 2) φ (v 3) (v 4)) :=
  (BDef.bex 2 (((extNB n).comp ![1, 0, 4, 5]).and ((rsB φ).comp ![1, 2, 3, 0]))).congr
    fun _ _ _ => Iff.rfl

def dwB {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) :
    BDef (k := 5) (fun V _ v ↦ DW (v 0) (v 1) (v 2) φ (v 3) (v 4)) :=
  ((witAtB φ).or (BDef.bex 1 ((witAtB φ).comp ![1, 2, 3, 4, 0])).not).congr
    fun _ _ _ => Iff.rfl

def leastWB {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) :
    BDef (k := 6) (fun V _ v ↦ LeastW (v 0) (v 1) (v 2) (v 3) φ (v 4) (v 5)) :=
  ((BDef.mem 5 1).and (((dwB φ).comp ![0, 1, 2, 4, 5]).and (BDef.ball 1
    (((dwB φ).comp ![1, 2, 3, 5, 0]).imp (prB.comp ![4, 0, 6]).not)))).congr
    fun _ _ _ => Iff.rfl

def hereB (c : ℕ) {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) : BDef (k := 8)
    (fun V _ v ↦ Here (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) c φ) :=
  (BDef.bex 6 (((skB c).comp ![1, 2, 0, 7]).and (BDef.bex 4
    (((evB n).comp ![2, 3, 4, 5, 7, 8, 1, 0]).and
      ((leastWB φ).comp ![3, 4, 5, 6, 0, 9]))))).congr fun _ _ _ => Iff.rfl

def stepB : {n : ℕ} → (φ : Semiformula ℒₛₑₜ Empty n) → (c : ℕ) → BDef (k := 8)
    (fun V _ v ↦ StepR (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7) φ c)
  | _, .rel _ _, _ => BDef.fls.congr fun _ _ _ => Iff.rfl
  | _, .nrel _ _, _ => BDef.fls.congr fun _ _ _ => Iff.rfl
  | _, ⊤, _ => BDef.fls.congr fun _ _ _ => Iff.rfl
  | _, ⊥, _ => BDef.fls.congr fun _ _ _ => Iff.rfl
  | _, φ ⋏ ψ, c => ((stepB φ c).or (stepB ψ (c + cnt φ))).congr fun _ _ _ => Iff.rfl
  | _, φ ⋎ ψ, c => ((stepB φ c).or (stepB ψ (c + cnt φ))).congr fun _ _ _ => Iff.rfl
  | _, ∀¹ φ, c => (stepB φ c).congr fun _ _ _ => Iff.rfl
  | _, ∃¹ φ, c => ((hereB c φ).or (stepB φ (c + 1))).congr fun _ _ _ => Iff.rfl

def dnB : BDef (k := 4) (fun V _ v ↦ DnR (v 0) (v 1) (v 2) (v 3)) :=
  (BDef.bex 1 ((BDef.ball 0 BDef.fls).and (pgB.comp ![1, 0, 4, 3]))).congr
    fun _ _ _ => Iff.rfl

def leastAB : BDef (k := 3) (fun V _ v ↦ LeastA (v 0) (v 1) (v 2)) :=
  ((BDef.mem 2 0).and (BDef.ball 0 (prB.comp ![2, 0, 3]).not)).congr fun _ _ _ => Iff.rfl

section gdef

variable (σ₀ : Semiformula ℒₛₑₜ Empty 0) (χ : Semiformula ℒₛₑₜ Empty 3)

def mainB : BDef (k := 8)
    (fun V _ v ↦ MainR σ₀ χ (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) :=
  ((stepB σ₀ 0).or ((stepB χ (cnt σ₀)).or (dnB.comp ![0, 1, 6, 7]))).congr
    fun _ _ _ => Iff.rfl

/-- The clause of the recursion, as a relation of the variables `γ`, `f`, `y` and the
parameters `P`, `o`, `A`, `FS`, `W`. -/
def GRel : MRel 8 :=
  fun V _ v ↦ GR σ₀ χ (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)

def grB : BDef (GRel σ₀ χ) :=
  ((funBB.comp ![1, 0]).and (((mainB σ₀ χ).comp ![3, 4, 5, 6, 7, 1, 0, 2]).or
    (((BDef.bex 5 ((mainB σ₀ χ).comp ![4, 5, 6, 7, 8, 2, 1, 0])).not).and
      (leastAB.comp ![5, 7, 2])))).congr fun _ _ _ => Iff.rfl

def sgDefB : BDef (k := 5) (fun V _ v ↦ SgDef (v 0) (v 1) (v 2) (v 3) (v 4)) :=
  (BDef.bex 0 (BDef.bex 1 (BDef.bex 5 (BDef.bex 6 ((prB.comp ![8, 3, 1]).and
    ((prB.comp ![8, 2, 0]).and ((((atomB 0).comp ![5, 6, 3, 2, 4]).and (BDef.mem 1 0)).or
      (((atomB 1).comp ![5, 6, 3, 2, 4]).and (BDef.eq 1 0))))))))).congr fun _ _ _ => Iff.rfl

end gdef

/-! ### In a model of `𝗠𝗛` -/

section model

variable {V : Type} [SetStructure V] [Nonempty V] [hH : V↓[ℒₛₑₜ] ⊧* 𝗠𝗛]

/-- The set that contains the codes of the valuations in `A`. -/
noncomputable abbrev FSof (A : V) : V := ℘ (prodS (om : V) A)

theorem funB_pr {f γ t a a' : V} (h : FunB f γ) (ht : t ∈ γ) (h1 : Pr f t a)
    (h2 : Pr f t a') : a = a' := by
  obtain ⟨q, hq, hop⟩ := h1
  obtain ⟨q', hq', hop'⟩ := h2
  obtain ⟨u, hu, hyu⟩ := pr_snd_mem hop
  obtain ⟨u', hu', hyu'⟩ := pr_snd_mem hop'
  exact h q hq q' hq' t ht u hu a hyu u' hu' a' hyu' hop hop'

theorem funB_of_pr {f γ : V} (h : ∀ t, t ∈ γ → ∀ a a', Pr f t a → Pr f t a' → a = a') :
    FunB f γ :=
  fun q hq q' hq' t ht _ _ a _ _ _ a' _ hop hop' => h t ht a a' ⟨q, hq, hop⟩ ⟨q', hq', hop'⟩

theorem funB_loc {f f' γ : V} (hag : ∀ γ', γ' ∈ γ → ∀ y', Pr f γ' y' ↔ Pr f' γ' y')
    (h : FunB f γ) : FunB f' γ :=
  funB_of_pr fun t ht a a' h1 h2 => funB_pr h ht ((hag t ht a).mpr h1) ((hag t ht a').mpr h2)

theorem ev_loc {P o A FS f f' γ : V} (hag : ∀ γ', γ' ∈ γ → ∀ y', Pr f γ' y' ↔ Pr f' γ' y') :
    ∀ (n : ℕ) (ε s : V), EV P o A FS f γ n ε s → EV P o A FS f' γ n ε s
  | 0, _, _, h => h
  | n + 1, _, _, ⟨t, ht, ε', hε', hpg, a, ha, hpr, s', hs', hev, hext⟩ =>
    ⟨t, ht, ε', hε', hpg, a, ha, (hag t ht a).mp hpr, s', hs', ev_loc hag n ε' s' hev, hext⟩

theorem step_loc {P o A FS W f f' γ y : V}
    (hag : ∀ γ', γ' ∈ γ → ∀ y', Pr f γ' y' ↔ Pr f' γ' y') :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ),
      StepR P o A FS W f γ y φ c → StepR P o A FS W f' γ y φ c := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c h; exact h
  | hfalsum => intro c h; exact h
  | hrel r v => intro c h; exact h
  | hnrel r v => intro c h; exact h
  | hand φ ψ ih1 ih2 => intro c h; exact h.imp (ih1 c) (ih2 _)
  | hor φ ψ ih1 ih2 => intro c h; exact h.imp (ih1 c) (ih2 _)
  | hall φ ih => intro c h; exact ih c h
  | hexs φ ih =>
    intro c h
    rcases h with ⟨ε, hε, hsk, s, hs, hev, hl⟩ | h
    · exact Or.inl ⟨ε, hε, hsk, s, hs, ev_loc hag _ ε s hev, hl⟩
    · exact Or.inr (ih _ h)

theorem ext_fn {s s₂ s' a : V} (n : ℕ) (h : ExtN (om : V) s s' n a)
    (h₂ : ExtN (om : V) s₂ s' n a) : s = s₂ := by
  obtain ⟨z, -, hz, h1, h2, h3⟩ := h
  obtain rfl := (isNum_iff _ z).mp hz
  obtain ⟨z', -, hz', h1', h2', h3'⟩ := h₂
  obtain rfl := (isNum_iff _ z').mp hz'
  refine mem_ext fun p => ⟨fun hp => ?_, fun hp => ?_⟩
  · rcases h1 p hp with h | h
    · exact h2' p h
    · exact isOp_iff.mp h ▸ pr_iff.mp h3'
  · rcases h1' p hp with h | h
    · exact h2 p h
    · exact isOp_iff.mp h ▸ pr_iff.mp h3

theorem mem_tup : ∀ {n : ℕ} (e : Fin n → V), (∀ i, e i ∈ (om : V)) → ∀ i, e i ∈ tup e
  | 0, _, _, i => i.elim0
  | n + 1, e, he, i => by
    have htl : tup (fun i ↦ e i.succ) ∈ (om : V) := tup_mem_om _ fun i => he i.succ
    cases i using Fin.cases with
    | zero => exact mem_pr_left (he 0) htl
    | succ j =>
      exact om_mem_tr (tup_mem_om e he) (mem_pr_right (he 0) htl)
        (mem_tup (fun i ↦ e i.succ) (fun i => he i.succ) j)

theorem sk_inj {c c' : ℕ} {ε ε' : V} (hε : ε ∈ (om : V)) (hε' : ε' ∈ (om : V))
    (h : sk c ε = sk c' ε') : c = c' ∧ ε = ε' := by
  obtain ⟨e1, e2⟩ := pr_inj (nm_mem_om _) hε (nm_mem_om _) hε' h
  exact ⟨Nat.succ.inj (nm_inj e1), e2⟩

section withP

variable {P : V} (hP : CanP P)

include hP

theorem skR_elim {c : ℕ} {ε γ : V} (h : SkR P (om : V) c ε γ) : ε ∈ (om : V) ∧ γ = sk c ε := by
  obtain ⟨z, -, hz, hpg⟩ := h
  obtain rfl := (isNum_iff _ z).mp hz
  obtain ⟨-, hε, rfl⟩ := (canP_pg hP).mp hpg
  exact ⟨hε, rfl⟩

theorem ev_fn {A f γ : V} (hf : FunB f γ) : ∀ (n : ℕ) (ε s s₂ : V),
    EV P (om : V) A (FSof A) f γ n ε s → EV P (om : V) A (FSof A) f γ n ε s₂ → s = s₂
  | 0, _, s, s₂, h, h₂ =>
    mem_ext fun p => ⟨fun hp => (h p hp).elim, fun hp => (h₂ p hp).elim⟩
  | n + 1, ε, s, s₂, ⟨t, ht, ε', _, hpg, a, _, hpr, s', _, hev, hext⟩,
      ⟨t₂, _, ε'₂, _, hpg₂, a₂, _, hpr₂, s'₂, _, hev₂, hext₂⟩ => by
    obtain ⟨ht', hε', rfl⟩ := (canP_pg hP).mp hpg
    obtain ⟨ht₂', hε₂', e⟩ := (canP_pg hP).mp hpg₂
    obtain ⟨rfl, rfl⟩ := pr_inj ht' hε' ht₂' hε₂' e
    obtain rfl := funB_pr hf ht hpr hpr₂
    obtain rfl := ev_fn hf n ε' s' s'₂ hev hev₂
    exact ext_fn n hext hext₂

theorem ev_tup {A f γ : V} : ∀ {n : ℕ} (e a : Fin n → V), (∀ i, e i ∈ (om : V)) →
    (∀ i, e i ∈ γ) → (∀ i, a i ∈ A) → (∀ i, Pr f (e i) (a i)) →
    EV P (om : V) A (FSof A) f γ n (tup e) (fnc a)
  | 0, _, _, _, _, _, _ => fun p hp => absurd hp (by simp [fnc])
  | n + 1, e, a, he, heγ, ha, hf => by
    have htl : tup (fun i ↦ e i.succ) ∈ (om : V) := tup_mem_om _ fun i => he i.succ
    refine ⟨e 0, heγ 0, _, htl, (canP_pg hP).mpr ⟨he 0, htl, rfl⟩, a 0, ha 0, hf 0,
      fnc (fun i ↦ a i.succ), fnc_mem_pow _ (fun i => ha i.succ),
      ev_tup (fun i ↦ e i.succ) (fun i ↦ a i.succ) (fun i => he i.succ) (fun i => heγ i.succ)
        (fun i => ha i.succ) (fun i => hf i.succ), ?_⟩
    exact (extN_fnc (fun i ↦ a i.succ) (a 0) _).mpr rfl

theorem step_code {A W f γ y : V} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ),
    StepR P (om : V) A (FSof A) W f γ y φ c →
      ∃ c', c ≤ c' ∧ c' < c + cnt φ ∧ ∃ ε, ε ∈ (om : V) ∧ γ = sk c' ε := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c h; exact h.elim
  | hfalsum => intro c h; exact h.elim
  | hrel r v => intro c h; exact h.elim
  | hnrel r v => intro c h; exact h.elim
  | hand φ ψ ih1 ih2 =>
    intro c h
    have e : cnt (φ ⋏ ψ) = cnt φ + cnt ψ := rfl
    rcases h with h | h
    · obtain ⟨c', h1, h2, h3⟩ := ih1 c h
      exact ⟨c', h1, by omega, h3⟩
    · obtain ⟨c', h1, h2, h3⟩ := ih2 _ h
      exact ⟨c', by omega, by omega, h3⟩
  | hor φ ψ ih1 ih2 =>
    intro c h
    have e : cnt (φ ⋎ ψ) = cnt φ + cnt ψ := rfl
    rcases h with h | h
    · obtain ⟨c', h1, h2, h3⟩ := ih1 c h
      exact ⟨c', h1, by omega, h3⟩
    · obtain ⟨c', h1, h2, h3⟩ := ih2 _ h
      exact ⟨c', by omega, by omega, h3⟩
  | hall φ ih => intro c h; exact ih c h
  | hexs φ ih =>
    intro c h
    have e : cnt (∃¹ φ) = cnt φ + 1 := rfl
    rcases h with ⟨ε, -, hsk, -⟩ | h
    · obtain ⟨hε, rfl⟩ := skR_elim hP hsk
      exact ⟨c, le_rfl, by omega, ε, hε, rfl⟩
    · obtain ⟨c', h1, h2, h3⟩ := ih _ h
      exact ⟨c', by omega, by omega, h3⟩

variable {A W : V}
variable (hTot : ∀ x, x ∈ A → ∀ y, y ∈ A → Pr W x y ∨ (x = y ∨ Pr W y x))

include hTot in
omit hP in
theorem leastW_unique {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) {s y y' : V}
    (h : LeastW (om : V) A (FSof A) W φ s y) (h' : LeastW (om : V) A (FSof A) W φ s y') :
    y = y' := by
  rcases hTot y h.1 y' h'.1 with k | k | k
  · exact absurd k (h'.2.2 y h.1 h.2.1)
  · exact k
  · exact absurd k (h.2.2 y' h'.1 h'.2.1)

include hTot in
theorem step_fn {f γ y y' : V} (hf : FunB f γ) :
    ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ),
      StepR P (om : V) A (FSof A) W f γ y φ c → StepR P (om : V) A (FSof A) W f γ y' φ c →
      y = y' := by
  have hdis : ∀ {n m : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (ψ : Semiformula ℒₛₑₜ Empty m)
      (c d : ℕ) (y y' : V), c + cnt φ ≤ d → StepR P (om : V) A (FSof A) W f γ y φ c →
      StepR P (om : V) A (FSof A) W f γ y' ψ d → False := by
    intro n m φ ψ c d y y' hcd h h'
    obtain ⟨c₁, -, h2, ε₁, hε₁, e₁⟩ := step_code hP φ c h
    obtain ⟨c₂, h1', -, ε₂, hε₂, e₂⟩ := step_code hP ψ d h'
    have := (sk_inj hε₁ hε₂ (e₁.symm.trans e₂)).1
    omega
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c h; exact h.elim
  | hfalsum => intro c h; exact h.elim
  | hrel r v => intro c h; exact h.elim
  | hnrel r v => intro c h; exact h.elim
  | hand φ ψ ih1 ih2 =>
    intro c h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact ih1 c h h'
    · exact (hdis φ ψ c _ _ _ le_rfl h h').elim
    · exact (hdis φ ψ c _ _ _ le_rfl h' h).elim
    · exact ih2 _ h h'
  | hor φ ψ ih1 ih2 =>
    intro c h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact ih1 c h h'
    · exact (hdis φ ψ c _ _ _ le_rfl h h').elim
    · exact (hdis φ ψ c _ _ _ le_rfl h' h).elim
    · exact ih2 _ h h'
  | hall φ ih => intro c h h'; exact ih c h h'
  | hexs φ ih =>
    intro c h h'
    have hhs : ∀ y y' : V, Here P (om : V) A (FSof A) W f γ y c φ →
        StepR P (om : V) A (FSof A) W f γ y' φ (c + 1) → False := by
      rintro y y' ⟨ε, -, hsk, -⟩ hst
      obtain ⟨hε, e₁⟩ := skR_elim hP hsk
      obtain ⟨c₂, h1', -, ε₂, hε₂, e₂⟩ := step_code hP φ _ hst
      have := (sk_inj hε hε₂ (e₁.symm.trans e₂)).1
      omega
    rcases h with h | h <;> rcases h' with h' | h'
    · obtain ⟨ε, -, hsk, s, -, hev, hl⟩ := h
      obtain ⟨ε', -, hsk', s', -, hev', hl'⟩ := h'
      obtain ⟨hε, e₁⟩ := skR_elim hP hsk
      obtain ⟨hε', e₂⟩ := skR_elim hP hsk'
      obtain rfl := (sk_inj hε hε' (e₁.symm.trans e₂)).2
      obtain rfl := ev_fn hP hf _ ε s s' hev hev'
      exact leastW_unique hTot φ hl hl'
    · exact (hhs _ _ h h').elim
    · exact (hhs _ _ h' h).elim
    · exact ih _ h h'

omit hP in
theorem step_mem {P f γ y : V} : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ),
    StepR P (om : V) A (FSof A) W f γ y φ c → y ∈ A := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c h; exact h.elim
  | hfalsum => intro c h; exact h.elim
  | hrel r v => intro c h; exact h.elim
  | hnrel r v => intro c h; exact h.elim
  | hand φ ψ ih1 ih2 => intro c h; exact h.elim (ih1 c) (ih2 _)
  | hor φ ψ ih1 ih2 => intro c h; exact h.elim (ih1 c) (ih2 _)
  | hall φ ih => intro c h; exact ih c h
  | hexs φ ih =>
    intro c h
    rcases h with ⟨ε, -, -, s, -, -, hl⟩ | h
    · exact hl.1
    · exact ih _ h

variable (σ₀ : Semiformula ℒₛₑₜ Empty 0) (χ : Semiformula ℒₛₑₜ Empty 3)
variable (hA0 : ∀ n, n ∈ (om : V) → n ∈ A)

include hA0 in
theorem main_mem {f γ y : V} (h : MainR σ₀ χ P (om : V) A (FSof A) W f γ y) : y ∈ A := by
  rcases h with h | h | ⟨z, -, -, hpg⟩
  · exact step_mem σ₀ 0 h
  · exact step_mem χ _ h
  · exact hA0 y ((canP_pg hP).mp hpg).2.1

include hTot in
theorem main_fn {f γ y y' : V} (hf : FunB f γ)
    (h : MainR σ₀ χ P (om : V) A (FSof A) W f γ y)
    (h' : MainR σ₀ χ P (om : V) A (FSof A) W f γ y') : y = y' := by
  have hdn : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ) (y y' : V),
      StepR P (om : V) A (FSof A) W f γ y φ c → DnR P (om : V) γ y' → False := by
    rintro n φ c y y' hst ⟨z, -, hz, hpg⟩
    obtain ⟨c', -, -, ε, hε, e⟩ := step_code hP φ c hst
    have ez : z = ∅ := mem_ext fun w => ⟨fun h => (hz w h).elim, fun h => absurd h (by simp)⟩
    subst ez
    obtain ⟨h0, hy', e'⟩ := (canP_pg hP).mp hpg
    have := (pr_inj (nm_mem_om _) hε h0 hy' (e.symm.trans e')).1
    have h1 : (nm c' : V) ∈ (nm (c' + 1) : V) := self_mem_sc _
    rw [this] at h1
    exact absurd h1 (by simp)
  have hdis : ∀ (y y' : V), StepR P (om : V) A (FSof A) W f γ y σ₀ 0 →
      StepR P (om : V) A (FSof A) W f γ y' χ (cnt σ₀) → False := by
    intro y y' h h'
    obtain ⟨c₁, -, h2, ε₁, hε₁, e₁⟩ := step_code hP σ₀ 0 h
    obtain ⟨c₂, h1', -, ε₂, hε₂, e₂⟩ := step_code hP χ _ h'
    have := (sk_inj hε₁ hε₂ (e₁.symm.trans e₂)).1
    omega
  rcases h with h | h | h <;> rcases h' with h' | h' | h'
  · exact step_fn hP hTot hf σ₀ 0 h h'
  · exact (hdis _ _ h h').elim
  · exact (hdn σ₀ 0 _ _ h h').elim
  · exact (hdis _ _ h' h).elim
  · exact step_fn hP hTot hf χ _ h h'
  · exact (hdn χ _ _ _ h h').elim
  · exact (hdn σ₀ 0 _ _ h' h).elim
  · exact (hdn χ _ _ _ h' h).elim
  · obtain ⟨z, -, hz, hpg⟩ := h
    obtain ⟨z', -, hz', hpg'⟩ := h'
    have ez : z = ∅ := mem_ext fun w => ⟨fun h => (hz w h).elim, fun h => absurd h (by simp)⟩
    have ez' : z' = ∅ := mem_ext fun w => ⟨fun h => (hz' w h).elim, fun h => absurd h (by simp)⟩
    subst ez ez'
    obtain ⟨h0, hy, e⟩ := (canP_pg hP).mp hpg
    obtain ⟨-, hy', e'⟩ := (canP_pg hP).mp hpg'
    exact (pr_inj h0 hy h0 hy' (e.symm.trans e')).2

variable (hLeast : ∀ Z : V, (∀ z, z ∈ Z → z ∈ A) → (∃ z, z ∈ Z) →
  ∃ m, m ∈ Z ∧ ∀ z, z ∈ Z → ¬Pr W z m)

include hLeast hA0 in
omit hP in
theorem leastW_exists {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty (n + 1)) (s : V) :
    ∃ y, LeastW (om : V) A (FSof A) W φ s y := by
  let Z : V := sepB ((dwB φ).comp ![1, 2, 3, 4, 0]) A ![(om : V), A, FSof A, s]
  have hZ : ∀ z, z ∈ Z ↔ z ∈ A ∧ DW (om : V) A (FSof A) φ s z := fun z => mem_sepB _ _ _ z
  have hne : ∃ z, z ∈ Z := by
    by_cases h : ∃ b', b' ∈ A ∧ WitAt (om : V) A (FSof A) φ s b'
    · obtain ⟨b', hb', hw⟩ := h
      exact ⟨b', (hZ b').mpr ⟨hb', Or.inl hw⟩⟩
    · exact ⟨∅, (hZ ∅).mpr ⟨hA0 ∅ empty_mem_om, Or.inr h⟩⟩
  obtain ⟨m, hm, hmin⟩ := hLeast Z (fun z hz => ((hZ z).mp hz).1) hne
  exact ⟨m, ((hZ m).mp hm).1, ((hZ m).mp hm).2, fun b hb hd => hmin b ((hZ b).mpr ⟨hb, hd⟩)⟩

include hLeast hA0 hTot in
/-- **The values exist.** -/
theorem exists_val :
    ∃ F : V, IsAtt (GRel σ₀ χ) ![P, (om : V), A, FSof A, W] F (sc (om : V)) := by
  refine ord_rec (grB σ₀ χ) ?_ ?_ (om : V) A ord_om ?_
  · intro γ f f' y _ hag h
    have h' : GR σ₀ χ γ f y P (om : V) A (FSof A) W := h
    show GR σ₀ χ γ f' y P (om : V) A (FSof A) W
    have hml : ∀ y, MainR σ₀ χ P (om : V) A (FSof A) W f γ y ↔
        MainR σ₀ χ P (om : V) A (FSof A) W f' γ y := fun y =>
      ⟨fun h => h.imp (step_loc hag σ₀ 0) (fun h => h.imp (step_loc hag χ _) id),
        fun h => h.imp (step_loc (fun γ' hγ' y' => (hag γ' hγ' y').symm) σ₀ 0)
          (fun h => h.imp (step_loc (fun γ' hγ' y' => (hag γ' hγ' y').symm) χ _) id)⟩
    refine ⟨funB_loc hag h'.1, ?_⟩
    rcases h'.2 with h | ⟨hno, hl⟩
    · exact Or.inl ((hml y).mp h)
    · exact Or.inr ⟨fun ⟨y', hy', hm⟩ => hno ⟨y', hy', (hml y').mpr hm⟩, hl⟩
  · intro γ f y y' h h'
    have h1 : GR σ₀ χ γ f y P (om : V) A (FSof A) W := h
    have h2 : GR σ₀ χ γ f y' P (om : V) A (FSof A) W := h'
    rcases h1.2 with k | ⟨kno, kl⟩ <;> rcases h2.2 with k' | ⟨kno', kl'⟩
    · exact main_fn hP hTot σ₀ χ h1.1 k k'
    · exact absurd ⟨y, main_mem hP σ₀ χ hA0 k, k⟩ kno'
    · exact absurd ⟨y', main_mem hP σ₀ χ hA0 k', k'⟩ kno
    · rcases hTot y kl.1 y' kl'.1 with j | j | j
      · exact absurd j (kl'.2 y kl.1)
      · exact j
      · exact absurd j (kl.2 y' kl'.1)
  · intro β _ f _ hf
    have hfb : FunB f β := hf.2.2
    by_cases h : ∃ y', y' ∈ A ∧ MainR σ₀ χ P (om : V) A (FSof A) W f β y'
    · obtain ⟨y', hy', hm⟩ := h
      exact ⟨y', hy', hfb, Or.inl hm⟩
    · obtain ⟨m, hm, hmin⟩ := hLeast A (fun z hz => hz) ⟨∅, hA0 ∅ empty_mem_om⟩
      exact ⟨m, hm, hfb, Or.inr ⟨h, hm, fun b hb => hmin b hb⟩⟩

/-! ### The values -/

omit hP in
/-- The value of `t`. -/
noncomputable def vl (F t : V) : V := by
  classical exact if h : ∃ y : V, Pr F t y then Classical.choose h else ∅

/-- The value of `t`, as an element of the structure. -/
noncomputable def vlA (hA0 : ∀ n, n ∈ (om : V) → n ∈ A) (F t : V) : extSet A := by
  classical exact if h : vl F t ∈ A then ⟨vl F t, h⟩ else ⟨∅, hA0 ∅ empty_mem_om⟩

variable {F : V} (hF : IsAtt (GRel σ₀ χ) ![P, (om : V), A, FSof A, W] F (sc (om : V)))

include hF in
omit hP in
theorem vl_spec {t : V} (ht : t ∈ (om : V)) :
    Pr F t (vl F t) ∧ GR σ₀ χ t F (vl F t) P (om : V) A (FSof A) W := by
  obtain ⟨y, hy, hG⟩ := att_total hF (mem_sc.mpr (Or.inr ht))
  have hex : ∃ y : V, Pr F t y := ⟨y, hy⟩
  have hv : Pr F t (vl F t) := by
    unfold vl
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact ⟨hv, att_G hF hv⟩

include hF hA0 in
theorem vl_mem {t : V} (ht : t ∈ (om : V)) : vl F t ∈ A := by
  rcases (vl_spec σ₀ χ hF ht).2.2 with h | ⟨-, h⟩
  · exact main_mem hP σ₀ χ hA0 h
  · exact h.1

include hF hP in
omit hP in
theorem vlA_val (hP : CanP P) {t : V} (ht : t ∈ (om : V)) : (vlA hA0 F t : V) = vl F t := by
  unfold vlA
  rw [dif_pos (vl_mem hP σ₀ χ hA0 hF ht)]

include hF hA0 hTot in
/-- A value given by the clauses is the value. -/
theorem vl_main {t y : V} (ht : t ∈ (om : V))
    (h : MainR σ₀ χ P (om : V) A (FSof A) W F t y) : vl F t = y := by
  obtain ⟨-, hfb, hG⟩ := vl_spec σ₀ χ hF ht
  rcases hG with k | ⟨kno, -⟩
  · exact main_fn hP hTot σ₀ χ hfb k h
  · exact absurd ⟨y, main_mem hP σ₀ χ hA0 h, h⟩ kno

include hF hA0 hTot in
theorem vl_dn {j : V} (hj : j ∈ (om : V)) : vl F (dn j) = j :=
  vl_main hP hTot σ₀ χ hA0 hF (dn_mem_om hj)
    (Or.inr (Or.inr ⟨∅, empty_mem_om, fun w hw => absurd hw (by simp),
      (canP_pg hP).mpr ⟨empty_mem_om, hj, rfl⟩⟩))

/-- The values of an environment. -/
noncomputable def vE (hA0 : ∀ n, n ∈ (om : V) → n ∈ A) (F : V) {n : ℕ} (e : Fin n → V) :
    Fin n → extSet A := fun i ↦ vlA hA0 F (e i)

omit hP in
theorem vE_cons (hA0 : ∀ n, n ∈ (om : V) → n ∈ A) (F : V) {n : ℕ} (t : V) (e : Fin n → V) :
    vE hA0 F (t :> e) = (vlA hA0 F t :> vE hA0 F e) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- **The witnesses of the formula have the right values.** -/
def RespV (hA0 : ∀ n, n ∈ (om : V) → n ∈ A) (F : V) :
    {n : ℕ} → Semiformula ℒₛₑₜ Empty n → ℕ → Prop
  | _, .rel _ _, _ => True
  | _, .nrel _ _, _ => True
  | _, ⊤, _ => True
  | _, ⊥, _ => True
  | _, φ ⋏ ψ, c => RespV hA0 F φ c ∧ RespV hA0 F ψ (c + cnt φ)
  | _, φ ⋎ ψ, c => RespV hA0 F φ c ∧ RespV hA0 F ψ (c + cnt φ)
  | _, ∀¹ φ, c => RespV hA0 F φ c
  | n, ∃¹ φ, c => (∀ e : Fin n → V, (∀ i, e i ∈ (om : V)) →
      (∃ b : extSet A, Eval (M := extSet A) (b :> vE hA0 F e) Empty.elim φ) →
        Eval (M := extSet A) (vlA hA0 F (sk c (tup e)) :> vE hA0 F e) Empty.elim φ) ∧
      RespV hA0 F φ (c + 1)

include hF hTot hLeast in
theorem resp_of_step : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ),
    (∀ γ y, StepR P (om : V) A (FSof A) W F γ y φ c →
      MainR σ₀ χ P (om : V) A (FSof A) W F γ y) → RespV hA0 F φ c := by
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c _; trivial
  | hfalsum => intro c _; trivial
  | hrel r v => intro c _; trivial
  | hnrel r v => intro c _; trivial
  | hand φ ψ ih1 ih2 =>
    intro c h
    exact ⟨ih1 c fun γ y hs => h γ y (Or.inl hs), ih2 _ fun γ y hs => h γ y (Or.inr hs)⟩
  | hor φ ψ ih1 ih2 =>
    intro c h
    exact ⟨ih1 c fun γ y hs => h γ y (Or.inl hs), ih2 _ fun γ y hs => h γ y (Or.inr hs)⟩
  | hall φ ih => intro c h; exact ih c h
  | @hexs n φ ih =>
    intro c h
    refine ⟨fun e he hex => ?_, ih _ fun γ y hs => h γ y (Or.inr hs)⟩
    have hε := tup_mem_om e he
    have hγ := sk_mem_om c hε
    have heγ : ∀ i, e i ∈ sk c (tup e) := fun i =>
      om_mem_tr hγ (mem_pr_right (nm_mem_om _) hε) (mem_tup e he i)
    have hfb : FunB F (sk c (tup e)) := (vl_spec σ₀ χ hF hγ).2.1
    let a : Fin n → V := fun i ↦ vl F (e i)
    have ha : ∀ i, a i ∈ A := fun i => vl_mem hP σ₀ χ hA0 hF (he i)
    have hpr : ∀ i, Pr F (e i) (a i) := fun i => (vl_spec σ₀ χ hF (he i)).1
    have hev := ev_tup hP (A := A) (f := F) (γ := sk c (tup e)) e a he heγ ha hpr
    obtain ⟨y₀, hy₀⟩ := leastW_exists hA0 hLeast φ (fnc a)
    have hhere : Here P (om : V) A (FSof A) W F (sk c (tup e)) y₀ c φ :=
      ⟨tup e, mem_pr_right (nm_mem_om _) hε, (skR_iff hP c hε).mpr rfl, fnc a,
        fnc_mem_pow a ha, hev, hy₀⟩
    have hval : vl F (sk c (tup e)) = y₀ :=
      vl_main hP hTot σ₀ χ hA0 hF hγ (h _ _ (Or.inl hhere))
    have hvE : (fun i ↦ ((vE hA0 F e i : extSet A) : V)) = a := by
      funext i
      exact vlA_val σ₀ χ hA0 hF hP (he i)
    have hwit : ∀ b : extSet A, WitAt (om : V) A (FSof A) φ (fnc a) (b : V) ↔
        Eval (M := extSet A) (b :> vE hA0 F e) Empty.elim φ := by
      intro b
      have hc : (fun i ↦ (((b :> vE hA0 F e) i : extSet A) : V)) = ((b : V) :> a) := by
        rw [← hvE]
        funext i
        cases i using Fin.cases <;> rfl
      rw [← rs_iff φ (b :> vE hA0 F e), hc]
      constructor
      · rintro ⟨s', -, hext, hrs⟩
        obtain rfl := (extN_fnc a _ _).mp hext
        exact hrs
      · intro hrs
        exact ⟨_, fnc_mem_pow _ (fun i => by
          cases i using Fin.cases with
          | zero => exact b.2
          | succ j => exact ha j), (extN_fnc a _ _).mpr rfl, hrs⟩
    obtain ⟨b, hb⟩ := hex
    have hy₀A : y₀ ∈ A := hy₀.1
    have hvy : vlA hA0 F (sk c (tup e)) = ⟨y₀, hy₀A⟩ :=
      Subtype.ext ((vlA_val σ₀ χ hA0 hF hP hγ).trans hval)
    rw [hvy]
    rcases hy₀.2.1 with hw | hno
    · exact (hwit ⟨y₀, hy₀A⟩).mp hw
    · exact absurd ⟨b.1, b.2, (hwit b).mpr hb⟩ hno

/-- **The atomic sentences that are true for the values.** -/
noncomputable def Sg (P A F : V) : V := sepB sgDefB (om : V) ![P, (om : V), A, F]

include hF hA0 in
theorem sg_iff (r : ℕ) (hr : r = 0 ∨ r = 1) {a b : V} (ha : a ∈ (om : V))
    (hb : b ∈ (om : V)) : atm r a b ∈ Sg P A F ↔
      ((r = 0 ∧ vl F a ∈ vl F b) ∨ (r = 1 ∧ vl F a = vl F b)) := by
  have hmem : ∀ α, α ∈ Sg P A F ↔ α ∈ (om : V) ∧ SgDef α P (om : V) A F :=
    fun α => mem_sepB sgDefB _ _ α
  have hα := atm_mem_om r ha hb
  have hab : pr a b ∈ (om : V) := pr_mem_om ha hb
  have hfun : ∀ {t x : V}, t ∈ (om : V) → Pr F t x → x = vl F t := fun ht hx =>
    att_fun hF hx (vl_spec σ₀ χ hF ht).1
  rw [hmem]
  constructor
  · rintro ⟨-, a', ha', b', hb', x, -, y, -, hx, hy, hor⟩
    have ha'o : a' ∈ (om : V) := (ord_om (V := V)).1 _ hα a' ha'
    have hb'o : b' ∈ (om : V) := (ord_om (V := V)).1 _ hα b' hb'
    have key : ∀ r' : ℕ, AtomR P (om : V) r' a' b' (atm r a b) → r = r' ∧ a = a' ∧ b = b' := by
      intro r' hat
      have e := (atomR_iff hP r' ha'o hb'o).mp hat
      obtain ⟨e1, e2⟩ := pr_inj (nm_mem_om r) hab (nm_mem_om r') (pr_mem_om ha'o hb'o) e
      obtain ⟨e3, e4⟩ := pr_inj ha hb ha'o hb'o e2
      exact ⟨nm_inj e1, e3, e4⟩
    rcases hor with ⟨hat, hxy⟩ | ⟨hat, hxy⟩
    · obtain ⟨rfl, rfl, rfl⟩ := key 0 hat
      rw [hfun ha hx, hfun hb hy] at hxy
      exact Or.inl ⟨rfl, hxy⟩
    · obtain ⟨rfl, rfl, rfl⟩ := key 1 hat
      rw [hfun ha hx, hfun hb hy] at hxy
      exact Or.inr ⟨rfl, hxy⟩
  · intro h
    have haα : a ∈ atm r a b :=
      om_mem_tr hα (mem_pr_right (nm_mem_om r) hab) (mem_pr_left ha hb)
    have hbα : b ∈ atm r a b :=
      om_mem_tr hα (mem_pr_right (nm_mem_om r) hab) (mem_pr_right ha hb)
    refine ⟨hα, a, haα, b, hbα, vl F a, vl_mem hP σ₀ χ hA0 hF ha, vl F b,
      vl_mem hP σ₀ χ hA0 hF hb, (vl_spec σ₀ χ hF ha).1, (vl_spec σ₀ χ hF hb).1, ?_⟩
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
    · exact Or.inl ⟨(atomR_iff hP 0 ha hb).mpr rfl, h⟩
    · exact Or.inr ⟨(atomR_iff hP 1 ha hb).mpr rfl, h⟩

include hF hA0 in
/-- **A formula that is true in `(A, ∈)` at the values of `e` is true under `Sg` at `e`**, if
its witnesses have the right values. -/
theorem holds_of_eval : ∀ {n : ℕ} (φ : Semiformula ℒₛₑₜ Empty n) (c : ℕ) (e : Fin n → V),
    (∀ i, e i ∈ (om : V)) → RespV hA0 F φ c →
    Eval (M := extSet A) (vE hA0 F e) Empty.elim φ → Holds (Sg P A F) φ c e := by
  have hval : ∀ {t : V}, t ∈ (om : V) → (vlA hA0 F t : V) = vl F t :=
    fun ht => vlA_val σ₀ χ hA0 hF hP ht
  intro n φ
  induction φ using Semiformula.rec' with
  | hverum => intro c e _ _ _; trivial
  | hfalsum => intro c e _ _ h; exact h.elim
  | hrel r v =>
    intro c e he _ h
    cases r with
    | eq =>
      have h' : (v 0).val (M := extSet A) (vE hA0 F e) Empty.elim =
          (v 1).val (M := extSet A) (vE hA0 F e) Empty.elim := h
      rw [tix_val, tix_val] at h'
      have h'' := congrArg Subtype.val h'
      refine (sg_iff hP σ₀ χ hA0 hF 1 (Or.inr rfl) (he _) (he _)).mpr (Or.inr ⟨rfl, ?_⟩)
      rw [← hval (he _), ← hval (he _)]
      exact h''
    | mem =>
      have h' : (v 0).val (M := extSet A) (vE hA0 F e) Empty.elim ∈
          (v 1).val (M := extSet A) (vE hA0 F e) Empty.elim := h
      rw [tix_val, tix_val] at h'
      refine (sg_iff hP σ₀ χ hA0 hF 0 (Or.inl rfl) (he _) (he _)).mpr (Or.inl ⟨rfl, ?_⟩)
      rw [← hval (he _), ← hval (he _)]
      exact h'
  | hnrel r v =>
    intro c e he _ h
    cases r with
    | eq =>
      have h' : ¬(v 0).val (M := extSet A) (vE hA0 F e) Empty.elim =
          (v 1).val (M := extSet A) (vE hA0 F e) Empty.elim := h
      rw [tix_val, tix_val] at h'
      intro hin
      rcases (sg_iff hP σ₀ χ hA0 hF 1 (Or.inr rfl) (he _) (he _)).mp hin with ⟨k, -⟩ | ⟨-, k⟩
      · exact absurd k (by decide)
      · rw [← hval (he _), ← hval (he _)] at k
        exact h' (Subtype.ext k)
    | mem =>
      have h' : ¬(v 0).val (M := extSet A) (vE hA0 F e) Empty.elim ∈
          (v 1).val (M := extSet A) (vE hA0 F e) Empty.elim := h
      rw [tix_val, tix_val] at h'
      intro hin
      rcases (sg_iff hP σ₀ χ hA0 hF 0 (Or.inl rfl) (he _) (he _)).mp hin with ⟨-, k⟩ | ⟨k, -⟩
      · rw [← hval (he _), ← hval (he _)] at k
        exact h' k
      · exact absurd k (by decide)
  | hand φ ψ ih1 ih2 =>
    intro c e he hr h
    exact ⟨ih1 c e he hr.1 h.1, ih2 _ e he hr.2 h.2⟩
  | hor φ ψ ih1 ih2 =>
    intro c e he hr h
    exact h.imp (ih1 c e he hr.1) (ih2 _ e he hr.2)
  | hall φ ih =>
    intro c e he hr h t ht
    have h' := h (vlA hA0 F t)
    rw [← vE_cons] at h'
    exact ih c _ (cons_mem_om ht he) hr h'
  | hexs φ ih =>
    intro c e he hr h
    have h' := hr.1 e he h
    rw [← vE_cons] at h'
    exact ih _ _ (cons_mem_om (sk_mem_om c (tup_mem_om e he)) he) hr.2 h'

omit hP in
theorem sg_mem_pow (P A F : V) : Sg P A F ∈ (℘ om : V) :=
  mem_power_iff.mpr fun α hα => ((mem_sepB sgDefB _ _ α).mp hα).1

end withP

/-- **Soundness.** If `σ₀` is true in `(A, ∈)`, and `χ` at `(j + 1, j, 0)` for every `j` below
the number `n`, then `n` is in `Kset`. -/
theorem sound_kset {P A W : V} (hP : CanP P)
    (hTot : ∀ x, x ∈ A → ∀ y, y ∈ A → Pr W x y ∨ (x = y ∨ Pr W y x))
    (hLeast : ∀ Z : V, (∀ z, z ∈ Z → z ∈ A) → (∃ z, z ∈ Z) →
      ∃ m, m ∈ Z ∧ ∀ z, z ∈ Z → ¬Pr W z m)
    (hA0 : ∀ n, n ∈ (om : V) → n ∈ A)
    (σ₀ : Semiformula ℒₛₑₜ Empty 0) (χ : Semiformula ℒₛₑₜ Empty 3)
    (hσ : Eval (M := extSet A) ![] Empty.elim σ₀) {n : V} (hn : n ∈ (om : V))
    (hχ : ∀ j, j ∈ n → ∀ v : Fin 3 → extSet A, (v 0 : V) = sc j → (v 1 : V) = j →
      (v 2 : V) = ∅ → Eval (M := extSet A) v Empty.elim χ) :
    n ∈ Kset σ₀ χ P := by
  obtain ⟨F, hF⟩ := exists_val hP hTot σ₀ χ hA0 hLeast
  have hR0 : RespV hA0 F σ₀ 0 :=
    resp_of_step hP hTot σ₀ χ hA0 hLeast hF σ₀ 0 fun γ y h => Or.inl h
  have hR1 : RespV hA0 F χ (cnt σ₀) :=
    resp_of_step hP hTot σ₀ χ hA0 hLeast hF χ _ fun γ y h => Or.inr (Or.inl h)
  have e0 : vE hA0 F (![] : Fin 0 → V) = ![] := by funext i; exact i.elim0
  have h0 : Holds (Sg P A F) σ₀ 0 ![] :=
    holds_of_eval hP σ₀ χ hA0 hF σ₀ 0 ![] (fun i => i.elim0) hR0 (by rw [e0]; exact hσ)
  refine (mem_kset σ₀ χ hP).mpr ⟨hn, fun q hq => ⟨Sg P A F, sg_mem_pow P A F, ?_, ?_⟩⟩
  · exact holdsQ_of_holds (fun α hα => (ord_om (V := V)).1 q hq α hα) σ₀ 0 _ h0
  · intro j hj _
    have hjo : j ∈ (om : V) := (ord_om (V := V)).1 n hn j hj
    have hval : ∀ {t : V}, t ∈ (om : V) → (vlA hA0 F t : V) = vl F t :=
      fun ht => vlA_val σ₀ χ hA0 hF hP ht
    have hdn : ∀ {i : V}, i ∈ (om : V) → (vlA hA0 F (dn i) : V) = i := fun hi =>
      (hval (dn_mem_om hi)).trans (vl_dn hP hTot σ₀ χ hA0 hF hi)
    have hev : Eval (M := extSet A) (vE hA0 F (envJ j)) Empty.elim χ :=
      hχ j hj _ (hdn (sc_mem_om hjo)) (hdn hjo) (hdn empty_mem_om)
    exact holdsQ_of_holds (fun α hα => (ord_om (V := V)).1 q hq α hα) χ _ _
      (holds_of_eval hP σ₀ χ hA0 hF χ _ _ (envJ_mem_om hjo) hR1 hev)

end model

end MH

end FFL.FirstOrder.SetTheory
