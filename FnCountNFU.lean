module

public import FnChurch

@[expose] public section

set_option autoImplicit false

/-!
# FunctionNF with count interprets NFU + Infinity + the Axiom of Counting

Fix a model `M` of `𝗙𝗡𝗙` in which every Church numeral `n` has `n S 0 = n`. The sets of `M` are
a model of NFU + Infinity (`FunctionCut.model`), with Frege's natural numbers and the operation
`T` of `NFUArith`.

* `BT.fn`: comprehension for functions whose values are sets.
* `exists_fsucc`: the successor `σ` of Frege's natural numbers is an object.
* For a Church numeral `n` put `ρ n = n · σ · 0`, the Frege number reached by `n` steps from
  zero. Then `ρ` takes every Frege natural number as a value, and by induction on `n`
  (`tcompB`): every member `x` of `ρ (n S 0)` has `{{{a}} : a ∈ x} ∈ ρ n`. Here `n` is six levels
  above `x` on both sides. With `n S 0 = n` this gives `T (T m) = m` for every Frege natural
  number `m`, hence `T m = m` because `T` is monotone.
* `counting_of_countChurch`, and `fncInterpretsNFUIC : 𝗙𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖`.
-/

namespace FFL.FirstOrder

namespace FNF

open JensenNFU (Counting)
open JensenNFU.TFm (scons scons_zero scons_succ)

variable {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

local infixl:70 " ⬝ " => App

/-- The sets of a model of FunctionNF, as a model of NFU + Infinity. -/
noncomputable abbrev setModel : NFUCut.Model M := FunctionCut.model (M := M)

/-! ### Functions whose values are sets -/

/-- **Comprehension for functions whose values are sets.** A relation with a truth-value term
in `x` of level `t` and `m` of level `t + 1` defines an object `g` such that `g · m` is the set
of the `x` in the relation to `m`, for all values of the parameters. -/
theorem BT.fn {t : ℕ} {Γ : List ℕ} {R : (ℕ → M) → Prop} (p : BT (t :: (t + 1) :: Γ) R)
    (q : ℕ → M) :
    ∃ g : M, ∀ m, IsSet (g ⬝ m) ∧ ∀ x, Mem x (g ⬝ m) ↔ R (scons x (scons m q)) := by
  obtain ⟨D, hD⟩ := exists_sep (M := M)
  have hadm : Adm (t :: (t + 1) :: Γ)
      (scons t (scons (t + 1) (fun j => if h : j < Γ.length then Γ[j] else j - Γ.length)))
      (fun i => i) (fun ℓ => Γ.length + ℓ + 2) 0 := by
    refine ⟨fun i hi => ?_, fun ℓ => ?_⟩
    · cases i with
      | zero => rfl
      | succ i =>
        cases i with
        | zero => rfl
        | succ i =>
          have hi' : i < Γ.length := by simpa using hi
          show (if h : i < Γ.length then Γ[i] else i - Γ.length) = Γ[i] + 0
          rw [dite_eq_left hi']; rfl
    · show (if h : Γ.length + ℓ < Γ.length then Γ[Γ.length + ℓ] else Γ.length + ℓ - Γ.length) = ℓ + 0
      rw [dite_eq_right (by omega)]; omega
  have hl2 : HasLev (scons (t + 1) (fun j => if h : j < Γ.length then Γ[j] else j - Γ.length))
      (.lam (p.tm t (fun i => i) (fun ℓ => Γ.length + ℓ + 2))) (t + 1) :=
    ⟨t, rfl, by simpa using (p.ok t).lev _ _ _ 0 hadm⟩
  have hl : HasLev (fun j => if h : j < Γ.length then Γ[j] else j - Γ.length)
      (.lam (.lam (p.tm t (fun i => i) (fun ℓ => Γ.length + ℓ + 2)))) (t + 2) :=
    ⟨t + 1, rfl, hl2⟩
  have hy : ∀ m x : M, ev (.lam (.lam (p.tm t (fun i => i) (fun ℓ => Γ.length + ℓ + 2))))
      (fun j => if j < Γ.length then q j else D) ⬝ m ⬝ x = bool (R (scons x (scons m q))) := by
    intro m x
    rw [ev_lam hl, ev_lam hl2]
    refine (p.ok t).sem _ _ _ 0 _ (scons x (scons m q)) hadm (fun i hi => ?_) (fun ℓ => ?_)
    · cases i with
      | zero => rfl
      | succ i =>
        cases i with
        | zero => rfl
        | succ i =>
          have hi' : i < Γ.length := by simpa using hi
          show (if i < Γ.length then q i else D) = q i
          rw [ite_eq_left hi']
    · show Sep (if Γ.length + ℓ < Γ.length then q (Γ.length + ℓ) else D)
      rw [ite_eq_right (by omega)]; exact hD
  refine ⟨ev (.lam (.lam (p.tm t (fun i => i) (fun ℓ => Γ.length + ℓ + 2))))
      (fun j => if j < Γ.length then q j else D), fun m => ?_⟩
  have hset : IsSet (ev (.lam (.lam (p.tm t (fun i => i) (fun ℓ => Γ.length + ℓ + 2))))
      (fun j => if j < Γ.length then q j else D) ⬝ m) := fun x => by rw [hy m x]; exact bool_or _
  exact ⟨hset, fun x => ⟨fun h => bool_eq_tt.mp ((hy m x).symm.trans h.2),
    fun h => ⟨hset, (hy m x).trans (bool_true h)⟩⟩⟩

/-! ### The operations of `NFUCut` and of `FnSets` -/

theorem model_sing (a : M) : setModel.sing a = sing a :=
  setModel.ext (setModel.sing_isSet a) (isSet_sing (M := M)) fun _ => setModel.mem_sing.trans mem_sing.symm

theorem model_simg (x : M) : setModel.simg x = simg x :=
  setModel.ext (setModel.simg_isSet x) (isSet_simg (M := M)) fun z =>
    setModel.mem_simg.trans ((exists_congr fun a => and_congr Iff.rfl (by rw [model_sing])).trans
      mem_simg.symm)

/-- **The successor of Frege's natural numbers is an object.** -/
theorem exists_fsucc : ∃ σ : M, ∀ m, σ ⬝ m = setModel.succ m := by
  obtain ⟨g, hg⟩ := BT.fn (M := M) (t := 1) (Γ := [])
    (BT.ex 1 (BT.ex 0 ((BT.mem 1 3 1 rfl rfl).and (((BT.mem 0 1 0 rfl rfl).not).and
      (BT.all 0 ((BT.mem 0 3 0 rfl rfl).iff
        ((BT.mem 0 2 0 rfl rfl).or (BT.eq 0 1 0 rfl rfl))))))))
    (fun _ => Classical.arbitrary M)
  refine ⟨g, fun m => ?_⟩
  refine setModel.ext (hg m).1 (setModel.succ_isSet m) fun y => ?_
  refine ((hg m).2 y).trans (Iff.trans ?_ setModel.mem_succ.symm)
  constructor
  · rintro ⟨x, b, hx, hb, h⟩
    exact ⟨x, b, hx, hb, setModel.eq_adj_iff.mp h⟩
  · rintro ⟨x, b, hx, hb, rfl⟩
    exact ⟨x, b, hx, hb, fun c => setModel.mem_adj⟩

/-! ### The induction -/

/-- Every member `x` of `(n · s · z) · σ · 0` has `{{{a}} : a ∈ x} ∈ n · σ · 0`. The variables are
`n`, `s`, `z`, `σ`, `0` for the hypothesis and `σ`, `0` for the conclusion; `n` is six levels
above `x` on both sides. -/
noncomputable def tcompB : BT [6, 5, 4, 3, 2, 5, 4] (fun v : ℕ → M =>
    ∀ x, Mem x (v 0 ⬝ v 1 ⬝ v 2 ⬝ v 3 ⬝ v 4) → Mem (simg (simg x)) (v 0 ⬝ v 5 ⬝ v 6)) :=
  BT.congr (BT.ex 4 (BT.ex 2 (BT.ex 4
      ((app2B.sub [3, 4, 5, 2] 4).and ((app2B.sub [2, 6, 7, 1] 2).and
        ((app2B.sub [3, 8, 9, 0] 4).and
          (BT.all 1 ((BT.mem 0 2 1 rfl rfl).imp
            (BT.ex 2 (BT.ex 3 ((simgB.sub [1, 2] 0).and
              ((simgB.sub [0, 1] 1).and (BT.mem 0 3 3 rfl rfl)))))))))))))
    fun v => ⟨fun ⟨w, m₀, r, (e1 : v 0 ⬝ v 1 ⬝ v 2 = w), (e2 : w ⬝ v 3 ⬝ v 4 = m₀),
        (e3 : v 0 ⬝ v 5 ⬝ v 6 = r), h⟩ x hx => by
        subst e1 e2 e3
        obtain ⟨s1, s2, (e4 : s1 = simg x), (e5 : s2 = simg s1), h6⟩ := h x hx
        subst e4 e5
        exact h6,
      fun h => ⟨_, _, _, rfl, rfl, rfl, fun x hx => ⟨_, _, rfl, rfl, h x hx⟩⟩⟩

section rho

variable {z s σ : M} (hz : IsCZero z) (hs : IsCSucc s) (hσ : ∀ m, σ ⬝ m = setModel.succ m)

include hz in
/-- `ρ 0 = 0`, where `ρ n = n · σ · 0` and the second `0` is Frege's. -/
theorem rho_zero : z ⬝ σ ⬝ setModel.zero = setModel.zero := hz σ setModel.zero

include hs hσ in
/-- `ρ (S n) = ρ n + 1`. -/
theorem rho_succ (n : M) : s ⬝ n ⬝ σ ⬝ setModel.zero = setModel.succ (n ⬝ σ ⬝ setModel.zero) := by
  rw [hs n σ setModel.zero, hσ]

include hz hs hσ in
/-- `ρ n` is a natural number. -/
theorem rho_mem_nat {n : M} (hn : IsChurch z s n) :
    setModel.mem (n ⬝ σ ⬝ setModel.zero) setModel.nat := by
  have hN : IsSet ((setModel (M := M)).nat) := (setModel (M := M)).zero_mem_nat.1
  refine ⟨hN, church_induction (z := z) (s := s) chainMemB
    (scons σ (scons setModel.zero (fun _ => setModel.nat)))
    (show setModel.nat ⬝ (z ⬝ σ ⬝ setModel.zero) = TT by
      rw [rho_zero hz]; exact (setModel (M := M)).zero_mem_nat.2)
    (fun k _ (ih : setModel.nat ⬝ (k ⬝ σ ⬝ setModel.zero) = TT) =>
      show setModel.nat ⬝ (s ⬝ k ⬝ σ ⬝ setModel.zero) = TT by
        rw [rho_succ hs hσ]
        exact ((setModel (M := M)).succ_mem_nat ⟨hN, ih⟩).2) hn⟩

include hz hs hσ in
/-- **`ρ` is injective on the Church numerals.** -/
theorem rho_inj {n m : M} (hn : IsChurch z s n) (hm : IsChurch z s m)
    (e : n ⬝ σ ⬝ setModel.zero = m ⬝ σ ⬝ setModel.zero) : n = m := by
  refine church_induction (z := z) (s := s) chainInjB
    (scons z (scons s (scons σ (fun _ => setModel.zero)))) ?_ ?_ hn m hm ⟨_, rfl, e.symm⟩
  · show ∀ m, IsChurch z s m →
      (∃ w, z ⬝ σ ⬝ setModel.zero = w ∧ m ⬝ σ ⬝ setModel.zero = w) → z = m
    rintro m hm ⟨w, e1, e2⟩
    rcases church_cases hm with rfl | ⟨m', -, rfl⟩
    · rfl
    · rw [rho_succ hs hσ] at e2
      rw [rho_zero hz] at e1
      exact absurd (e1.trans e2.symm) (setModel.zero_ne_succ _)
  · intro k hk ih
    show ∀ m, IsChurch z s m →
      (∃ w, s ⬝ k ⬝ σ ⬝ setModel.zero = w ∧ m ⬝ σ ⬝ setModel.zero = w) → s ⬝ k = m
    have ih' : ∀ m, IsChurch z s m →
        (∃ w, k ⬝ σ ⬝ setModel.zero = w ∧ m ⬝ σ ⬝ setModel.zero = w) → k = m := ih
    rintro m hm ⟨w, e1, e2⟩
    rcases church_cases hm with rfl | ⟨m', hm', rfl⟩
    · rw [rho_succ hs hσ] at e1
      rw [rho_zero hz] at e2
      exact absurd (e2.trans e1.symm) (setModel.zero_ne_succ _)
    · rw [rho_succ hs hσ] at e1 e2
      have e3 := setModel.succ_inj (rho_mem_nat hz hs hσ hk) (rho_mem_nat hz hs hσ hm')
        (e1.trans e2.symm)
      rw [ih' m' hm' ⟨_, rfl, e3.symm⟩]

include hz hs hσ in
/-- **Every member `x` of `ρ (n S 0)` has `{{{a}} : a ∈ x} ∈ ρ n`.** This holds in every model of
FunctionNF. -/
theorem tcomp {n : M} (hn : IsChurch z s n) :
    ∀ x, Mem x (n ⬝ s ⬝ z ⬝ σ ⬝ setModel.zero) → Mem (simg (simg x)) (n ⬝ σ ⬝ setModel.zero) :=
  church_induction (z := z) (s := s) tcompB
    (scons s (scons z (scons σ (scons setModel.zero (scons σ (fun _ => setModel.zero))))))
    (show ∀ x, Mem x (z ⬝ s ⬝ z ⬝ σ ⬝ setModel.zero) →
        Mem (simg (simg x)) (z ⬝ σ ⬝ setModel.zero) by
      intro x hx
      rw [hz s z, rho_zero hz] at hx
      have ex : x = setModel.emp := setModel.mem_zero.mp hx
      rw [rho_zero hz, ex, ← model_simg, ← model_simg, setModel.simg_emp, setModel.simg_emp]
      exact setModel.mem_zero.mpr rfl)
    (fun k _ (ih : ∀ x, Mem x (k ⬝ s ⬝ z ⬝ σ ⬝ setModel.zero) →
        Mem (simg (simg x)) (k ⬝ σ ⬝ setModel.zero)) =>
      show ∀ x, Mem x (s ⬝ k ⬝ s ⬝ z ⬝ σ ⬝ setModel.zero) →
          Mem (simg (simg x)) (s ⬝ k ⬝ σ ⬝ setModel.zero) by
        intro x hx
        rw [hs k s z, rho_succ hs hσ] at hx
        obtain ⟨x', b, hx', hb, rfl⟩ := setModel.mem_succ.mp hx
        rw [rho_succ hs hσ, ← model_simg, ← model_simg, setModel.simg_adj, setModel.simg_adj]
        refine setModel.mem_succ.mpr ⟨_, _, ?_, ?_, rfl⟩
        · have := ih x' hx'
          rwa [← model_simg, ← model_simg] at this
        · intro hc
          obtain ⟨u, hu, e⟩ := setModel.mem_simg.mp hc
          obtain ⟨a', ha', rfl⟩ := setModel.mem_simg.mp hu
          have hba : b = a' := setModel.sing_inj (setModel.sing_inj e)
          exact hb (hba ▸ ha')) hn

include hz hs hσ in
/-- Every Frege natural number is a value of `ρ`. -/
theorem rho_surj {m : M} (hm : setModel.mem m setModel.nat) :
    ∃ n, IsChurch z s n ∧ n ⬝ σ ⬝ setModel.zero = m := by
  obtain ⟨I, -, hmem⟩ : ∃ I : M, IsSet I ∧
      ∀ m, Mem m I ↔ ∃ n, IsChurch z s n ∧ n ⬝ σ ⬝ setModel.zero = m :=
    (BT.ex (Γ := [0, 2, 3, 1, 0]) 2
      ((churchB.sub [0, 2, 3] 2).and (app2B.sub [0, 4, 5, 1] 0))).set
      (scons z (scons s (scons σ (fun _ => setModel.zero))))
  exact (hmem m).mp (setModel.nat_ind (I := I)
    ((hmem _).mpr ⟨z, isChurch_zero z s, rho_zero hz⟩)
    (fun k hk => by
      obtain ⟨n, hn, rfl⟩ := (hmem k).mp hk
      exact (hmem _).mpr ⟨s ⬝ n, isChurch_succ hn, rho_succ hs hσ n⟩) hm)

end rho

/-- **In a model of FunctionNF with count, the sets satisfy the Axiom of Counting.** -/
theorem counting_of_countChurch (h : CountChurch M) : Counting (Mem (M := M)) := by
  obtain ⟨z, hz⟩ := exists_czero (M := M)
  obtain ⟨s, hs⟩ := exists_csucc (M := M)
  obtain ⟨σ, hσ⟩ := exists_fsucc (M := M)
  have hcount := h z s hz hs
  -- `T (T m) = m`
  have hTT : ∀ m : (setModel (M := M)).Num, setModel.T (setModel.T m) = m := by
    intro m
    obtain ⟨n, hn, e⟩ := rho_surj hz hs hσ m.2
    obtain ⟨x, hx⟩ := setModel.nat_nonempty m.2
    have h1 := tcomp hz hs hσ hn x (by rw [hcount n hn, e]; exact hx)
    rw [e, ← model_simg, ← model_simg] at h1
    exact setModel.T_eq_of_mem (m := setModel.T m) (n := m) (setModel.simg_mem_T hx) h1
  exact counting_of_T (setModel.T_eq_self_of_T_T hTT)

/-- **In a model of FunctionNF whose sets satisfy the Axiom of Counting, count holds.** -/
theorem countChurch_of_counting (h : Counting (Mem (M := M))) : CountChurch M := by
  intro z s hz hs n hn
  obtain ⟨σ, hσ⟩ := exists_fsucc (M := M)
  have hT := T_of_counting h
  have hn' := isChurch_iter hz hs hn
  -- `ρ (n S 0)` and `ρ n` are natural numbers with a common member
  have h1 := rho_mem_nat hz hs hσ hn'
  have h2 := rho_mem_nat hz hs hσ hn
  obtain ⟨x, hx⟩ := setModel.nat_nonempty h1
  have h3 := tcomp hz hs hσ hn x hx
  rw [← model_simg, ← model_simg] at h3
  have h4 : setModel.mem (setModel.simg x) (n ⬝ s ⬝ z ⬝ σ ⬝ setModel.zero) := by
    have := setModel.simg_mem_T (m := ⟨_, h1⟩) hx
    rwa [hT ⟨_, h1⟩] at this
  have h5 : setModel.mem (setModel.simg (setModel.simg x)) (n ⬝ s ⬝ z ⬝ σ ⬝ setModel.zero) := by
    have := setModel.simg_mem_T (m := ⟨_, h1⟩) h4
    rwa [hT ⟨_, h1⟩] at this
  exact rho_inj hz hs hσ hn' hn (setModel.nat_disjoint h1 h2 h5 h3)

/-- **Over FunctionNF, count is the Axiom of Counting for the sets of the model.** -/
theorem countChurch_iff_counting : CountChurch M ↔ Counting (Mem (M := M)) :=
  ⟨counting_of_countChurch, countChurch_of_counting⟩

/-- **FunctionNF with count interprets NFU + Infinity + the Axiom of Counting.** -/
instance fncInterpretsNFUIC : 𝗙𝗡𝗙𝗖 ⊳ 𝗡𝗙𝗨𝗜𝗖 where
  trln := nfuTranslationOf 𝗙𝗡𝗙𝗖
  interpret_theory φ hφ := by
    apply Theory.Proof.complete_on_eq_models.{_, 0}
    intro M _ _ _ hT
    obtain ⟨hM, hc⟩ := fnc_models hT
    have := hM
    exact DirectTranslation.Model.translate_iff.mpr
      (models_theory_iff.mp (nfuModelOf_models_nfuic (counting_of_countChurch hc)) φ hφ)

end FNF

end FFL.FirstOrder

#print axioms FFL.FirstOrder.FNF.countChurch_iff_counting
#print axioms FFL.FirstOrder.FNF.fncInterpretsNFUIC
