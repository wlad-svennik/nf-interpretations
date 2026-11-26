module

public import FnCount

@[expose] public section

set_option autoImplicit false

/-!
# Church numerals in a model of FunctionNF, and count′ ⟹ count

Fix a model `M` of `𝗙𝗡𝗙`.

* The Church zero `λf.λx.x` and successor `λn.λf.λx.f (n f x)` exist (`exists_czero`,
  `exists_csucc`), so the axiom count is not vacuous.
* `churchB`: "`n` is a Church numeral" has a truth-value term, so the Church numerals form a
  set, and induction along them holds for every relation with a truth-value term
  (`church_induction`). The induction step may use that the number is a Church numeral.
* **`countChurch_of_countChain`: count′ implies count.** With `c n = n · κ · a`:
  1. `c n ∈ X`, `c 0 = a` and `c (S n) = K (c n)`;
  2. `c` is injective on the Church numerals, because `K` is injective and never takes the
     value `a` on `X`;
  3. `n S 0` is a Church numeral;
  4. `c (n S 0) = c (S (S n)) · t · t`, where both sides have `n` four levels above the value, so
     this is proved by induction; and `c (S (S n)) · t · t = c n` because `κ` is `K` on `X`.
  Hence `c (n S 0) = c n` and `n S 0 = n`.
* `fnkProvesCount : 𝗙𝗡𝗙𝗞 ⊢ Axiom.count`, `𝗙𝗡𝗙𝗖 ⪯ 𝗙𝗡𝗙𝗞` and `fnkInterpretsFNC : 𝗙𝗡𝗙𝗞 ⊳ 𝗙𝗡𝗙𝗖`.
-/

namespace FFL.FirstOrder

namespace FNF

open JensenNFU.TFm (scons scons_zero scons_succ)

variable {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [hM : M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

local infixl:70 " ⬝ " => App

/-! ### Zero and successor -/

/-- `λn.λf.λx. f (n f x)`. -/
def succT : LTm :=
  .lam (.lam (.lam (.app (.var 1) (.app (.app (.var 2) (.var 1)) (.var 0)))))

theorem ev_succT (env : ℕ → M) (n f x : M) : ev succT env ⬝ n ⬝ f ⬝ x = f ⬝ (n ⬝ f ⬝ x) := by
  have h : HasLev (fun _ => 0) succT 3 := ⟨2, rfl, 1, rfl, 0, rfl, ⟨rfl, ⟨⟨rfl, rfl⟩, rfl⟩⟩⟩
  obtain ⟨k2, -, hk2⟩ := id h
  obtain ⟨k1, -, hk1⟩ := id hk2
  obtain ⟨k0, -, hk0⟩ := id hk1
  rw [succT, ev_lam h, ev_lam hk2, ev_lam hk1, ev_app hk0, ev_app hk0.2, ev_app hk0.2.1, ev_var,
    ev_var, ev_var]
  rfl

/-- The Church numeral zero exists. -/
theorem exists_czero : ∃ z : M, IsCZero z :=
  ⟨ev kiT (fun _ => Classical.arbitrary M), fun f x => ev_kiT _ f x⟩

/-- The successor of Church numerals exists. -/
theorem exists_csucc : ∃ s : M, IsCSucc s :=
  ⟨ev succT (fun _ => Classical.arbitrary M), fun n f x => ev_succT _ n f x⟩

/-! ### Church numerals -/

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hM in
theorem isChurch_zero (z s : M) : IsChurch z s z := fun _ h0 _ => h0

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hM in
theorem isChurch_succ {z s n : M} (h : IsChurch z s n) : IsChurch z s (s ⬝ n) :=
  fun P h0 hs => hs n (h P h0 hs)

omit [Tarski.Structure.Eq ℒλ M] [Nonempty M] hM in
/-- Induction along the Church numerals, for a set. -/
theorem church_ind {z s I n : M} (hI : IsSet I) (h0 : Mem z I)
    (hs : ∀ m, Mem m I → Mem (s ⬝ m) I) (hn : IsChurch z s n) : Mem n I :=
  ⟨hI, hn I h0.2 (fun m hm => (hs m ⟨hI, hm⟩).2)⟩

/-- "`v₀` is a Church numeral for the zero `v₁` and the successor `v₂`." -/
def churchB : BT [0, 0, 1] (fun v : ℕ → M => IsChurch (v 1) (v 2) (v 0)) :=
  BT.congr (BT.all 1 ((BT.appTT 0 2 0 rfl rfl).imp
      ((BT.all 0 ((BT.appTT 1 0 0 rfl rfl).imp
          (BT.ex 0 ((BT.app 5 1 0 0 rfl rfl rfl).and (BT.appTT 2 0 0 rfl rfl))))).imp
        (BT.appTT 0 1 0 rfl rfl))))
    fun v => forall_congr' fun P => imp_congr Iff.rfl (imp_congr
      (forall_congr' fun m => imp_congr Iff.rfl
        ⟨fun ⟨w, (h1 : v 2 ⬝ m = w), (h2 : P ⬝ w = TT)⟩ => by rw [h1]; exact h2,
          fun h => ⟨_, rfl, h⟩⟩) Iff.rfl)

/-- The Church numerals form a set. -/
theorem exists_churchSet (z s : M) : ∃ N : M, IsSet N ∧ ∀ n, Mem n N ↔ IsChurch z s n :=
  (churchB (M := M)).set (scons z (fun _ => s))

/-- **Induction along the Church numerals**, for a relation with a truth-value term. The
induction step may use that the number is a Church numeral. -/
theorem church_induction {t : ℕ} {Γ : List ℕ} {R : (ℕ → M) → Prop} (p : BT (t :: Γ) R)
    (q : ℕ → M) {z s : M} (h0 : R (scons z q))
    (hs : ∀ m, IsChurch z s m → R (scons m q) → R (scons (s ⬝ m) q)) {n : M}
    (hn : IsChurch z s n) : R (scons n q) := by
  obtain ⟨I, hI, hmem⟩ := p.set q
  obtain ⟨N, hN, hNmem⟩ := exists_churchSet z s
  obtain ⟨J, hJ, hJmem⟩ : ∃ J : M, IsSet J ∧ ∀ x, Mem x J ↔ Mem x N ∧ Mem x I :=
    ((BT.mem (Γ := [t, t + 1, t + 1]) 0 1 t rfl rfl).and (BT.mem 0 2 t rfl rfl)).set
      (scons N (fun _ => I))
  have key : Mem n J := church_ind hJ
    ((hJmem z).mpr ⟨(hNmem z).mpr (isChurch_zero z s), (hmem z).mpr h0⟩)
    (fun m hm => by
      obtain ⟨h1, h2⟩ := (hJmem m).mp hm
      have hc := (hNmem m).mp h1
      exact (hJmem _).mpr ⟨(hNmem _).mpr (isChurch_succ hc),
        (hmem _).mpr (hs m hc ((hmem m).mp h2))⟩) hn
  exact (hmem n).mp ((hJmem n).mp key).2

/-- `v₀ · v₁ · v₂ = v₃`. -/
def app2B : BT [2, 1, 0, 0] (fun v : ℕ → M => v 0 ⬝ v 1 ⬝ v 2 = v 3) :=
  BT.congr (BT.ex 1 ((BT.app 1 2 0 1 rfl rfl rfl).and (BT.app 0 3 4 0 rfl rfl rfl)))
    fun v => ⟨fun ⟨u, (h1 : v 0 ⬝ v 1 = u), (h2 : u ⬝ v 2 = v 3)⟩ => by rw [h1]; exact h2,
      fun h => ⟨_, rfl, h⟩⟩

/-- A Church numeral is zero or a successor of a Church numeral. -/
theorem church_cases {z s n : M} (hn : IsChurch z s n) :
    n = z ∨ ∃ m, IsChurch z s m ∧ s ⬝ m = n := by
  let p : BT [0, 0, 1] (fun v : ℕ → M => v 0 = v 1 ∨ ∃ m, IsChurch (v 1) (v 2) m ∧ v 2 ⬝ m = v 0) :=
    BT.congr ((BT.eq 0 1 0 rfl rfl).or
      (BT.ex 0 ((churchB.sub [0, 2, 3] 0).and (BT.app 3 0 1 0 rfl rfl rfl)))) fun _ => Iff.rfl
  exact church_induction (z := z) (s := s) p (scons z (fun _ => s)) (Or.inl rfl)
    (fun m hm _ => Or.inr ⟨m, hm, rfl⟩) hn

/-! ### count′ implies count -/

/-- `X · (n · κ · a) = ⊤`; the variables are `n`, `κ`, `a`, `X`. -/
def chainMemB : BT [2, 1, 0, 1] (fun v : ℕ → M => v 3 ⬝ (v 0 ⬝ v 1 ⬝ v 2) = TT) :=
  BT.congr (BT.ex 0 ((app2B.sub [1, 2, 3, 0] 0).and (BT.appTT 4 0 0 rfl rfl)))
    fun v => ⟨fun ⟨w, (h1 : v 0 ⬝ v 1 ⬝ v 2 = w), (h2 : v 3 ⬝ w = TT)⟩ => by rw [h1]; exact h2,
      fun h => ⟨_, rfl, h⟩⟩

/-- `n · κ · a = m · κ · a` implies `n = m`, for every Church numeral `m`; the variables are
`n`, the zero, the successor, `κ`, `a`. -/
def chainInjB : BT [2, 2, 3, 1, 0] (fun v : ℕ → M =>
    ∀ m, IsChurch (v 1) (v 2) m → (∃ w, v 0 ⬝ v 3 ⬝ v 4 = w ∧ m ⬝ v 3 ⬝ v 4 = w) → v 0 = m) :=
  BT.congr (BT.all 2 ((churchB.sub [0, 2, 3] 2).imp
      ((BT.ex 0 ((app2B.sub [2, 5, 6, 0] 0).and (app2B.sub [1, 5, 6, 0] 0))).imp
        (BT.eq 1 0 2 rfl rfl)))) fun _ => Iff.rfl

/-- `n · s · z` is a Church numeral; the variables are `n`, `s`, `z`. -/
def closedB : BT [2, 1, 0] (fun v : ℕ → M => IsChurch (v 2) (v 1) (v 0 ⬝ v 1 ⬝ v 2)) :=
  BT.congr (BT.ex 0 ((app2B.sub [1, 2, 3, 0] 0).and (churchB.sub [0, 3, 2] 0)))
    fun v => ⟨fun ⟨w, (h1 : v 0 ⬝ v 1 ⬝ v 2 = w), (h2 : IsChurch (v 2) (v 1) w)⟩ => by
        rw [h1]; exact h2, fun h => ⟨_, rfl, h⟩⟩

/-- **`n S 0` is a Church numeral.** -/
theorem isChurch_iter {z s : M} (hz : IsCZero z) (hs : IsCSucc s) {n : M} (hn : IsChurch z s n) :
    IsChurch z s (n ⬝ s ⬝ z) :=
  church_induction (z := z) (s := s) closedB (scons s (fun _ => z))
    (show IsChurch z s (z ⬝ s ⬝ z) by rw [hz s z]; exact isChurch_zero z s)
    (fun k _ (ih : IsChurch z s (k ⬝ s ⬝ z)) => show IsChurch z s (s ⬝ k ⬝ s ⬝ z) by
      rw [hs k s z]; exact isChurch_succ ih) hn

/-- `(n · s · z) · κ · a = (s · (s · n)) · κ · a · t · t'`. The variable `n` is four levels
above the value on both sides. The variables are `n`, `s`, `z`, `κ`, `a` for the left-hand side
and `s`, `κ`, `a`, `t`, `t'` for the right-hand side. -/
def shiftB : BT [4, 3, 2, 1, 0, 5, 3, 2, 1, 0] (fun v : ℕ → M =>
    v 0 ⬝ v 1 ⬝ v 2 ⬝ v 3 ⬝ v 4 = v 5 ⬝ (v 5 ⬝ v 0) ⬝ v 6 ⬝ v 7 ⬝ v 8 ⬝ v 9) :=
  BT.congr (BT.ex 2 (BT.ex 4 (BT.ex 4 (BT.ex 2 (BT.ex 1 (BT.ex 0
      ((app2B.sub [6, 7, 8, 5] 2).and ((app2B.sub [5, 9, 10, 0] 0).and
        ((BT.app 11 6 4 4 rfl rfl rfl).and ((BT.app 11 4 3 4 rfl rfl rfl).and
          ((app2B.sub [3, 12, 13, 2] 2).and ((BT.app 2 14 1 1 rfl rfl rfl).and
            (BT.app 1 15 0 0 rfl rfl rfl)))))))))))))
    fun v => ⟨fun ⟨p, q1, q2, r, r1, w, (e1 : v 0 ⬝ v 1 ⬝ v 2 = p), (e2 : p ⬝ v 3 ⬝ v 4 = w),
        (e3 : v 5 ⬝ v 0 = q1), (e4 : v 5 ⬝ q1 = q2), (e5 : q2 ⬝ v 6 ⬝ v 7 = r),
        (e6 : r ⬝ v 8 = r1), (e7 : r1 ⬝ v 9 = w)⟩ => by
        subst e1 e3 e4 e5 e6
        exact e2.trans e7.symm,
      fun h => ⟨_, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, h.symm⟩⟩

/-- **count′ implies count.** -/
theorem countChurch_of_countChain (h : CountChain M) : CountChurch M := by
  obtain ⟨κ, X, a, ha, hX⟩ := h
  intro z s hz hs
  -- `c m = m · κ · a`
  have c0 : z ⬝ κ ⬝ a = a := hz κ a
  have cS : ∀ m, s ⬝ m ⬝ κ ⬝ a = κ ⬝ (m ⬝ κ ⬝ a) := fun m => hs m κ a
  -- 1. `c m ∈ X`
  have h1 : ∀ m, IsChurch z s m → X ⬝ (m ⬝ κ ⬝ a) = TT := fun m hm =>
    church_induction (z := z) (s := s) chainMemB (scons κ (scons a (fun _ => X)))
      (show X ⬝ (z ⬝ κ ⬝ a) = TT by rw [c0]; exact ha)
      (fun k _ (ih : X ⬝ (k ⬝ κ ⬝ a) = TT) => show X ⬝ (s ⬝ k ⬝ κ ⬝ a) = TT by
        rw [cS]; exact (hX _ ih).1) hm
  -- `κ` is `K` on the chain
  have hK : ∀ m, IsChurch z s m → ∀ y, κ ⬝ (m ⬝ κ ⬝ a) ⬝ y = m ⬝ κ ⬝ a :=
    fun m hm => (hX _ (h1 m hm)).2.2
  have hne : ∀ m, IsChurch z s m → κ ⬝ (m ⬝ κ ⬝ a) ≠ a := fun m hm => (hX _ (h1 m hm)).2.1
  -- 2. `c` is injective
  have h2 : ∀ n, IsChurch z s n → ∀ m, IsChurch z s m → n ⬝ κ ⬝ a = m ⬝ κ ⬝ a → n = m := by
    intro n hn m hm e
    refine church_induction (z := z) (s := s) chainInjB (scons z (scons s (scons κ (fun _ => a))))
      ?_ ?_ hn m hm ⟨_, rfl, e.symm⟩
    · -- zero
      show ∀ m, IsChurch z s m → (∃ w, z ⬝ κ ⬝ a = w ∧ m ⬝ κ ⬝ a = w) → z = m
      rintro m hm ⟨w, e1, e2⟩
      rcases church_cases hm with rfl | ⟨m', hm', rfl⟩
      · rfl
      · rw [cS] at e2
        rw [c0] at e1
        exact absurd (e2.trans e1.symm) (hne m' hm')
    · -- successor
      intro k hk ih
      show ∀ m, IsChurch z s m → (∃ w, s ⬝ k ⬝ κ ⬝ a = w ∧ m ⬝ κ ⬝ a = w) → s ⬝ k = m
      have ih' : ∀ m, IsChurch z s m → (∃ w, k ⬝ κ ⬝ a = w ∧ m ⬝ κ ⬝ a = w) → k = m := ih
      rintro m hm ⟨w, e1, e2⟩
      rcases church_cases hm with rfl | ⟨m', hm', rfl⟩
      · rw [cS] at e1
        rw [c0] at e2
        exact absurd (e1.trans e2.symm) (hne k hk)
      · rw [cS] at e1 e2
        have e3 : κ ⬝ (k ⬝ κ ⬝ a) = κ ⬝ (m' ⬝ κ ⬝ a) := e1.trans e2.symm
        have e4 : k ⬝ κ ⬝ a = m' ⬝ κ ⬝ a := by
          have := congrArg (fun u => u ⬝ a) e3
          simpa only [hK k hk a, hK m' hm' a] using this
        rw [ih' m' hm' ⟨_, rfl, e4.symm⟩]
  -- 3. `n · s · z` is a Church numeral
  have h3 : ∀ n, IsChurch z s n → IsChurch z s (n ⬝ s ⬝ z) := fun n hn => isChurch_iter hz hs hn
  -- 4. the right-hand side of `shiftB` is `c n`
  have h4 : ∀ n, IsChurch z s n → s ⬝ (s ⬝ n) ⬝ κ ⬝ a ⬝ a ⬝ a = n ⬝ κ ⬝ a := fun n hn => by
    rw [cS (s ⬝ n), hK (s ⬝ n) (isChurch_succ hn) a, cS n, hK n hn a]
  have h5 : ∀ n, IsChurch z s n → n ⬝ s ⬝ z ⬝ κ ⬝ a = s ⬝ (s ⬝ n) ⬝ κ ⬝ a ⬝ a ⬝ a := fun n hn =>
    church_induction (z := z) (s := s) shiftB
      (scons s (scons z (scons κ (scons a (scons s (scons κ (scons a (scons a (fun _ => a)))))))))
      (show z ⬝ s ⬝ z ⬝ κ ⬝ a = s ⬝ (s ⬝ z) ⬝ κ ⬝ a ⬝ a ⬝ a by
        rw [h4 z (isChurch_zero z s), hz s z])
      (fun k hk (ih : k ⬝ s ⬝ z ⬝ κ ⬝ a = s ⬝ (s ⬝ k) ⬝ κ ⬝ a ⬝ a ⬝ a) =>
        show s ⬝ k ⬝ s ⬝ z ⬝ κ ⬝ a = s ⬝ (s ⬝ (s ⬝ k)) ⬝ κ ⬝ a ⬝ a ⬝ a by
          rw [h4 (s ⬝ k) (isChurch_succ hk), hs k s z, cS (k ⬝ s ⬝ z), ih, h4 k hk, cS k]) hn
  -- conclusion
  intro n hn
  exact h2 _ (h3 n hn) n hn ((h5 n hn).trans (h4 n hn))

/-! ### The theories -/

/-- **`𝗙𝗡𝗙𝗞 ⊢ count`**: FunctionNF with count′ proves count. -/
theorem fnkProvesCount : 𝗙𝗡𝗙𝗞 ⊢ Axiom.count := by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  obtain ⟨hM, hc⟩ := fnk_models hT
  have := hM
  exact models_count_iff.mpr (countChurch_of_countChain hc)

end FNF

instance : 𝗙𝗡𝗙𝗖 ⪯ 𝗙𝗡𝗙𝗞 := Entailment.weakerThan_iff.mpr fun {φ} h => by
  apply Theory.Proof.complete_on_eq_models.{_, 0}
  intro M _ _ _ hT
  obtain ⟨hM, hc⟩ := FNF.fnk_models hT
  have := hM
  have : M↓[ℒλ] ⊧* 𝗙𝗡𝗙𝗖 := models_theory_iff.mpr fun ψ hψ => by
    rcases hψ with hψ | hψ
    · exact models_theory_iff.mp hM ψ hψ
    · have e : ψ = FNF.Axiom.count := hψ
      rw [e]
      exact FNF.models_count_iff.mpr (FNF.countChurch_of_countChain hc)
  exact models_of_provable this h

/-- **FunctionNF with count′ interprets FunctionNF with count**, by the identity. -/
instance fnkInterpretsFNC : 𝗙𝗡𝗙𝗞 ⊳ 𝗙𝗡𝗙𝗖 := DirectInterpretation.ofWeakerThan 𝗙𝗡𝗙𝗞 𝗙𝗡𝗙𝗖

end FFL.FirstOrder

#print axioms FFL.FirstOrder.FNF.countChurch_of_countChain
#print axioms FFL.FirstOrder.FNF.fnkProvesCount
#print axioms FFL.FirstOrder.fnkInterpretsFNC
