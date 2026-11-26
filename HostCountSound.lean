module

public import HostDD
public import HostER

@[expose] public section

set_option autoImplicit false

/-!
# The clauses for NF and for the Axiom of Counting from the partition theorem

In a host, for a flat model with the axioms `Ax` and `CAx` whose levels include the nonzero
ordinals of the last of `n + 1` consecutive closed levels, with `n = 2R + 1`.

One colouring of the sets of `2R + 1` levels: the colour of a set is the pair of

* the set of the atoms below `q` that are true at the centre of the increasing sequence of
  the set, and
* the set of the pairs `(t, m)`, for terms `t` below `q`, such that `m` is the least number of
  the host for which the value of `t` at the centre is the set of all objects with `m` members.

There are infinitely many colours; they are members of a closed level `C` that is a member of
the first level. The partition theorem (`Host.er_seq`) gives an increasing sequence of levels
of the length needed on which the colour is constant. On it every atom below `q` is decided
(`AllT` or `AllF`), and the number that a term denotes does not depend on the position, which
is the hypothesis of the clause K (`csat_of_dec`).

**`count_sound`**: under these hypotheses there is a sequence of levels whose truth assignment
satisfies the instances below `q` of N and of the nine clauses for the Axiom of Counting.
-/

namespace FlatM

variable {H : Host} {Fm : FlatM H}
variable {N : Type} [CommSemiring N] [PartialOrder N] {E : N → N} {num : N → H.W}

/-- The value of the term `n` at the position `R` of `s` is the set of all objects with `m`
members, for the levels at the positions `R`, `R1`, `R2`. -/
def NmAt (Fm : FlatM H) (ar : H.Arith E num) (R R1 R2 s n m : H.W) : Prop :=
  ∃ a a1 a2 c, H.App s R a ∧ H.App s R1 a1 ∧ H.App s R2 a2 ∧ Fm.Val ar n R s c ∧
    Fm.IsNm a a1 a2 m c

/-- `m` is the least such number. -/
def LeastNm (Fm : FlatM H) (ar : H.Arith E num) (R R1 R2 s n m : H.W) : Prop :=
  (m ∈ H.om ∧ Fm.NmAt ar R R1 R2 s n m) ∧
    ∀ b, H.lt b m → ¬ (b ∈ H.om ∧ Fm.NmAt ar R R1 R2 s n b)

/-- `c` is the colour of the set `B` of `r` levels. -/
def ColR (Fm : FlatM H) (ar : H.Arith E num) (qn r R R1 R2 B c : H.W) : Prop :=
  ∃ a p, c = H.op a p ∧
    (∀ i, i ∈ a ↔ i ∈ qn ∧ ∃ s, H.IncSeq s r ∧ (∀ z, z ∈ B ↔ ∃ j, H.App s j z) ∧
      Fm.Tr ar i R s) ∧
    (∀ u, u ∈ p ↔ u ∈ H.prod qn H.om ∧ ∃ n m s, u = H.op n m ∧ H.IncSeq s r ∧
      (∀ z, z ∈ B ↔ ∃ j, H.App s j z) ∧ Fm.LeastNm ar R R1 R2 s n m)

/-- Locality: the property `NmAt` at the centre of a window of a sequence. -/
theorem nmAt_seg (ar : H.Arith E num) {v w : H.W} {m₀ R R2 t : N} (hR : R = R2 + 1 + 1)
    (ht : 5 * t + 5 ≤ R)
    (hseg : ∀ j : N, j + 1 ≤ R + R + 1 → ∀ b, H.App v (num (m₀ + j)) b ↔ H.App w (num j) b)
    (m : H.W) :
    Fm.NmAt ar (num (m₀ + R)) (num (m₀ + (R2 + 1))) (num (m₀ + R2)) v (num t) m ↔
      Fm.NmAt ar (num R) (num (R2 + 1)) (num R2) w (num t) m := by
  have hval := fun c => loc (Fm := Fm) ar hseg t (num (m₀ + R)) (num R) c
    ⟨R, ht, ar.nf.add_le_add_r (ar.nf.add_le_add_l ht R) 1, rfl, rfl⟩
  have h0 := hseg R ((ar.nf.le_iff _ _).mpr ⟨R, by ring⟩)
  have h1 := hseg (R2 + 1) ((ar.nf.le_iff _ _).mpr ⟨R2 + 1 + 1 + 1, by rw [hR]; ring⟩)
  have h2 := hseg R2 ((ar.nf.le_iff _ _).mpr ⟨R2 + 1 + 1 + 1 + 1, by rw [hR]; ring⟩)
  constructor
  · rintro ⟨a, a1, a2, c, g0, g1, g2, gv, gn⟩
    exact ⟨a, a1, a2, c, (h0 a).mp g0, (h1 a1).mp g1, (h2 a2).mp g2, (hval c).mp gv, gn⟩
  · rintro ⟨a, a1, a2, c, g0, g1, g2, gv, gn⟩
    exact ⟨a, a1, a2, c, (h0 a).mpr g0, (h1 a1).mpr g1, (h2 a2).mpr g2, (hval c).mpr gv, gn⟩

/-- The property `NmAt`, in terms of the levels and the value. -/
theorem nmAt_iff (ar : H.Arith E num) (ax : Fm.Ax) {v : H.W} (hv : Fm.Plc v) {k k1 k2 n m : H.W}
    (hk : ∃ b, H.App v k b) (hk1 : ∃ b, H.App v k1 b) (hk2 : ∃ b, H.App v k2 b) :
    Fm.NmAt ar k k1 k2 v n m ↔
      Fm.IsNm (H.lvl v k) (H.lvl v k1) (H.lvl v k2) m (Fm.vl ar n k v) := by
  constructor
  · rintro ⟨a, a1, a2, c, g0, g1, g2, gv, gn⟩
    rw [← H.lvl_eq hv.fn g0, ← H.lvl_eq hv.fn g1, ← H.lvl_eq hv.fn g2,
      ← Fm.val_fun ar hv.fn _ _ _ _ gv (vl_spec ar ax hv hk)]
    exact gn
  · intro h
    exact ⟨_, _, _, _, H.lvl_spec hk, H.lvl_spec hk1, H.lvl_spec hk2, vl_spec ar ax hv hk, h⟩

/-- The property `NmAt` at the centre of a window, in terms of the levels and the value of the
sequence. -/
theorem nmAt_win (ar : H.Arith E num) (ax : Fm.Ax) {v w : H.W} (hv : Fm.Plc v) {m₀ R R2 t : N}
    (hR : R = R2 + 1 + 1) (ht : 5 * t + 5 ≤ R) (hw : H.IncSeq w (num (R + R + 1)))
    (hseg : ∀ j : N, j + 1 ≤ R + R + 1 → ∀ b, H.App v (num (m₀ + j)) b ↔ H.App w (num j) b)
    (m : H.W) :
    Fm.NmAt ar (num R) (num (R2 + 1)) (num R2) w (num t) m ↔
      Fm.IsNm (H.lvl v (num (m₀ + R))) (H.lvl v (num (m₀ + (R2 + 1))))
        (H.lvl v (num (m₀ + R2))) m (Fm.vl ar (num t) (num (m₀ + R)) v) := by
  have b0 : R + 1 ≤ R + R + 1 := (ar.nf.le_iff _ _).mpr ⟨R, by ring⟩
  have b1 : R2 + 1 + 1 ≤ R + R + 1 := (ar.nf.le_iff _ _).mpr ⟨R2 + 1 + 1 + 1, by rw [hR]; ring⟩
  have b2 : R2 + 1 ≤ R + R + 1 := (ar.nf.le_iff _ _).mpr ⟨R2 + 1 + 1 + 1 + 1, by rw [hR]; ring⟩
  have pos : ∀ j : N, j + 1 ≤ R + R + 1 → ∃ b, H.App v (num (m₀ + j)) b := fun j hj => by
    obtain ⟨b, hb⟩ := hw.tot (ar.num_mem.mpr hj)
    exact ⟨b, (hseg j hj b).mpr hb⟩
  exact (nmAt_seg ar hR ht hseg m).symm.trans
    (nmAt_iff ar ax hv (pos R b0) (pos (R2 + 1) b1) (pos R2 b2))

set_option maxHeartbeats 1600000 in
/-- **The clauses for NF and for the Axiom of Counting, from the partition property** of a set
`O` of ordinals for the exponent `nn`, a number of the host: every colouring of the sets of `nn`
members of `O` with colours in `C` has homogeneous increasing sequences of every length. -/
theorem count_sound_gen (ar : H.Arith E num) (ax : Fm.Ax) (cax : Fm.CAx) {O nn C : H.W}
    (hER : ∀ col, H.ColOn col nn O C → ∀ k, k ∈ H.om →
      ∃ s, H.IncSeq s k ∧ (∀ i a, H.App s i a → a ∈ O) ∧
        ∀ B B' c c', H.Card B nn → H.Card B' nn → H.SubV B s → H.SubV B' s →
          H.App col B c → H.App col B' c' → c = c')
    (hC : H.Closed C)
    (hlvl : ∀ a, a ∈ O → a ≠ H.emp → Fm.Lv a)
    {q R R2 : N} (hR : R = R2 + 1 + 1) (hn : num (R + R + 1) = nn)
    (hrad : ∀ i : N, i + 1 ≤ q → 5 * i + 6 ≤ R) :
    ∃ e, NSat (fun i => Fm.AllT ar e (num i) (num R)) q ∧
      CSat (fun i => Fm.AllT ar e (num i) (num R)) q := by
  have hdt := Fm.def_tr ar
  have hdi := H.def_incSeq
  have hV := Fm.def_vl ar
  have hO := Fm.defOb
  have hE := Fm.defEl
  -- the colouring
  obtain ⟨A, hA⟩ := H.exists_finSubsets ar (O) (R + R + 1)
  have hfun : ∀ B ∈ A, ∀ c c',
      Fm.ColR ar (num q) (num (R + R + 1)) (num R) (num (R2 + 1)) (num R2) B c →
      Fm.ColR ar (num q) (num (R + R + 1)) (num R) (num (R2 + 1)) (num R2) B c' → c = c' := by
    rintro B - c c' ⟨a, p, rfl, ha, hp⟩ ⟨a', p', rfl, ha', hp'⟩
    rw [H.ext' fun i => (ha i).trans (ha' i).symm, H.ext' fun u => (hp u).trans (hp' u).symm]
  have hcolD : Def2 H (fun B c =>
      Fm.ColR ar (num q) (num (R + R + 1)) (num R) (num (R2 + 1)) (num R2) B c) := by hdef
  obtain ⟨col, hcoldef⟩ : ∃ col, col = H.mkFun A (fun B c =>
      Fm.ColR ar (num q) (num (R + R + 1)) (num R) (num (R2 + 1)) (num R2) B c) hcolD hfun :=
    ⟨_, rfl⟩
  have happ : ∀ B c, H.App col B c ↔ B ∈ A ∧
      Fm.ColR ar (num q) (num (R + R + 1)) (num R) (num (R2 + 1)) (num R2) B c := fun B c => by
    rw [hcoldef]
    exact H.app_mkFun
  have hcol : H.ColOn col (nn) (O) C := by
    refine ⟨by rw [hcoldef]; exact H.isFun_mkFun, fun B hB hsub => ?_⟩
    rw [← hn] at hB
    have hqC : num q ∈ C := hC.nat_mem (ar.num_om q)
    have hP1 : Def1 H (fun i => ∃ s, H.IncSeq s (num (R + R + 1)) ∧
        (∀ z, z ∈ B ↔ ∃ j, H.App s j z) ∧ Fm.Tr ar i (num R) s) := by hdef
    have hP2 : Def1 H (fun u => ∃ n m s, u = H.op n m ∧ H.IncSeq s (num (R + R + 1)) ∧
        (∀ z, z ∈ B ↔ ∃ j, H.App s j z) ∧
        Fm.LeastNm ar (num R) (num (R2 + 1)) (num R2) s n m) := by hdef
    exact ⟨H.op (H.sepS (num q) _ hP1) (H.sepS (H.prod (num q) H.om) _ hP2),
      hC.op_mem (hC.sepS_mem hqC _ hP1) (hC.sepS_mem (hC.prod_mem hqC hC.om_mem) _ hP2),
      (happ _ _).mpr ⟨hA B hB hsub, _, _, rfl, fun i => H.mem_sepS, fun u => H.mem_sepS⟩⟩
  -- the homogeneous sequence, without its first member
  obtain ⟨s0, hs0, hs0v, hhom⟩ :=
    hER col hcol (num (1 + (R + 5 + R + 1))) (ar.num_om _)
  obtain ⟨e, he, hes, hseg1⟩ := H.exists_seg ar hs0 1 (R + 5 + R + 1) (le_refl _)
  have hlv : ∀ k a, H.App e k a → Fm.Lv a := by
    intro k a hka
    obtain ⟨j, hj, rfl⟩ := ar.mem_num.mp (he.dom hka)
    have h1 := (hseg1 j hj a).mpr hka
    obtain ⟨a0, ha0⟩ := hs0.tot (i := num 0)
      (ar.num_mem.mpr ((ar.nf.le_iff _ _).mpr ⟨R + 5 + R + 1, by ring⟩))
    have hlt : a0 ∈ a := hs0.2.2.2 _ _ _ _ ha0 h1
      (ar.num_mem.mpr ((ar.nf.le_iff _ _).mpr ⟨j, by ring⟩))
    exact hlvl a (hs0v _ _ h1) (fun e0 => H.not_mem_emp a0 (e0 ▸ hlt))
  have hv : Fm.Plc e := ⟨⟨_, he⟩, hlv⟩
  -- the colour of a window of a subsequence
  have win : ∀ (w : H.W) (L m₀ : N), H.IncSeq w (num L) → H.SubSeq w e → m₀ + (R + R + 1) ≤ L →
      ∃ sg c, H.IncSeq sg (num (R + R + 1)) ∧
        (∀ j : N, j + 1 ≤ R + R + 1 → ∀ b, H.App w (num (m₀ + j)) b ↔ H.App sg (num j) b) ∧
        H.Card (H.ran sg) (nn) ∧ H.SubV (H.ran sg) s0 ∧ H.App col (H.ran sg) c := by
    intro w L m₀ hw hwe hm
    obtain ⟨sg, hsg, hsw, hseg⟩ := H.exists_seg ar hw m₀ (R + R + 1) hm
    have hsub0 : H.SubV (H.ran sg) s0 := fun b hb => by
      obtain ⟨j, hj⟩ := H.mem_ran.mp hb
      obtain ⟨j1, hj1⟩ := hsw j b hj
      obtain ⟨j2, hj2⟩ := hwe j1 b hj1
      exact hes j2 b hj2
    have hcard : H.Card (H.ran sg) (nn) := by
      rw [← hn]
      exact ⟨sg, hsg, fun z => H.mem_ran⟩
    obtain ⟨c, -, hc⟩ := hcol.2 _ hcard (fun z hz => by
      obtain ⟨j, hj⟩ := hsub0 z hz
      exact hs0v j z hj)
    exact ⟨sg, c, hsg, hseg, hcard, hsub0, hc⟩
  obtain ⟨sg1, c0, hsg1, -, hcard1, hsub1, hc1⟩ :=
    win e _ 0 he (fun i a h => ⟨i, h⟩) ((ar.nf.le_iff _ _).mpr ⟨5, by ring⟩)
  obtain ⟨-, a0, p0, rfl, -, -⟩ := (happ _ _).mp hc1
  -- two sequences with the same members agree at each position
  have same : ∀ s sg, H.IncSeq s (num (R + R + 1)) → H.IncSeq sg (num (R + R + 1)) →
      (∀ z, z ∈ H.ran sg ↔ ∃ j, H.App s j z) →
      ∀ j : N, j + 1 ≤ R + R + 1 → ∀ b, H.App s (num (0 + j)) b ↔ H.App sg (num j) b := by
    intro s sg hs hsg hran j hj b
    rw [zero_add]
    exact H.incSeq_app_eq ar hs hsg (fun z => (hran z).symm.trans H.mem_ran) j hj b
  have rad5 : ∀ t : N, aIn t ddT + 1 ≤ q → 5 * t + 5 ≤ R := fun t ht =>
    le_trans (le_trans (ar.nf.add_le_add_r (ar.nf.mul_le_mul_l (ar.nf.le_aIn_left t ddT) 5) 5)
      (ar.nf.le_add _ 1)) (by
        have h := hrad _ ht
        rwa [show 5 * aIn t ddT + 5 + 1 = 5 * aIn t ddT + 6 from by ring])
  -- what the common colour says about a window
  have wcol : ∀ (w : H.W) (L m₀ : N), H.IncSeq w (num L) → H.SubSeq w e → m₀ + (R + R + 1) ≤ L →
      ∃ sg, H.IncSeq sg (num (R + R + 1)) ∧
        (∀ j : N, j + 1 ≤ R + R + 1 → ∀ b, H.App w (num (m₀ + j)) b ↔ H.App sg (num j) b) ∧
        (∀ i : N, i + 1 ≤ q → (num i ∈ a0 ↔ Fm.Tr ar (num i) (num R) sg)) ∧
        (∀ (t : N) (m : H.W), aIn t ddT + 1 ≤ q → (H.op (num t) m ∈ p0 ↔
          Fm.LeastNm ar (num R) (num (R2 + 1)) (num R2) sg (num t) m)) := by
    intro w L m₀ hw hwe hm
    obtain ⟨sg, c, hsg, hseg, hcard, hsub, hc⟩ := win w L m₀ hw hwe hm
    have e0 := hhom _ _ _ _ hcard hcard1 hsub hsub1 hc hc1
    subst e0
    obtain ⟨-, a, p, e1, ha, hp⟩ := (happ _ _).mp hc
    obtain ⟨e2, e3⟩ := H.op_inj e1
    subst e2 e3
    refine ⟨sg, hsg, hseg, fun i hi => ?_, fun t m ht => ?_⟩
    · rw [ha]
      constructor
      · rintro ⟨-, s, hs, hran, htr⟩
        exact (tr_loc ar (same s sg hs hsg hran) i ⟨R, hrad i hi,
          ar.nf.add_le_add_r (ar.nf.add_le_add_l (hrad i hi) R) 1, by rw [zero_add], rfl⟩).mp htr
      · intro htr
        exact ⟨ar.num_mem.mpr hi, sg, hsg, fun z => H.mem_ran, htr⟩
    · have tq : t + 1 ≤ q := le_trans (ar.nf.add_le_add_r (ar.nf.le_aIn_left t ddT) 1) ht
      rw [hp]
      constructor
      · rintro ⟨-, n', m', s, e4, hs, hran, hle⟩
        obtain ⟨e5, e6⟩ := H.op_inj e4
        subst e5 e6
        have K : ∀ x, Fm.NmAt ar (num R) (num (R2 + 1)) (num R2) s (num t) x ↔
            Fm.NmAt ar (num R) (num (R2 + 1)) (num R2) sg (num t) x := fun x => by
          have h := nmAt_seg (Fm := Fm) ar hR (rad5 t ht) (same s sg hs hsg hran) x
          simpa only [zero_add] using h
        exact ⟨⟨hle.1.1, (K _).mp hle.1.2⟩, fun b hb hP => hle.2 b hb ⟨hP.1, (K b).mpr hP.2⟩⟩
      · intro hle
        exact ⟨H.op_mem_prod.mpr ⟨ar.num_mem.mpr tq, hle.1.1⟩, num t, m, sg, rfl, hsg,
          fun z => H.mem_ran, hle⟩
  -- every atom below `q` is decided
  have hdec : ∀ i : N, i + 1 ≤ q →
      Fm.AllT ar e (num i) (num R) ∨ Fm.AllF ar e (num i) (num R) := by
    intro i hi
    have key : ∀ (w : H.W) (L p : N), H.IncSeq w (num L) → H.SubSeq w e → R ≤ p →
        p + R + 1 ≤ L → (Fm.Tr ar (num i) (num p) w ↔ num i ∈ a0) := by
      intro w L p hw hwe h1 h2
      obtain ⟨m, rfl⟩ := (ar.nf.le_iff _ _).mp h1
      obtain ⟨sg, hsg, hseg, htr, -⟩ := wcol w L m hw hwe (by
        rw [show m + (R + R + 1) = R + m + R + 1 from by ring]; exact h2)
      rw [htr i hi, show R + m = m + R from add_comm R m]
      exact tr_loc ar hseg i ⟨R, hrad i hi,
        ar.nf.add_le_add_r (ar.nf.add_le_add_l (hrad i hi) R) 1, rfl, rfl⟩
    by_cases h : num i ∈ a0
    · exact Or.inl ((allT_iff ar).mpr fun w L p hw hwe h1 h2 => (key w L p hw hwe h1 h2).mpr h)
    · exact Or.inr ((allF_iff ar).mpr fun w L p hw hwe h1 h2 htr =>
        h ((key w L p hw hwe h1 h2).mp htr))
  -- the number that a term denotes is the same at the positions `R + 2` and `R + 3`
  have hnum : ∀ t : N, aIn t ddT + 1 ≤ q → ∀ m m', m ∈ H.om → m' ∈ H.om →
      Fm.IsNm (H.lvl e (H.suc (H.suc (num R)))) (H.lvl e (H.suc (num R))) (H.lvl e (num R)) m
        (Fm.vl ar (num t) (H.suc (H.suc (num R))) e) →
      Fm.IsNm (H.lvl e (H.suc (H.suc (H.suc (num R))))) (H.lvl e (H.suc (H.suc (num R))))
        (H.lvl e (H.suc (num R))) m' (Fm.vl ar (num t) (H.suc (H.suc (H.suc (num R)))) e) →
      ∃ m₀, Fm.IsNm (H.lvl e (H.suc (H.suc (num R)))) (H.lvl e (H.suc (num R)))
          (H.lvl e (num R)) m₀ (Fm.vl ar (num t) (H.suc (H.suc (num R))) e) ∧
        Fm.IsNm (H.lvl e (H.suc (H.suc (H.suc (num R))))) (H.lvl e (H.suc (H.suc (num R))))
          (H.lvl e (H.suc (num R))) m₀ (Fm.vl ar (num t) (H.suc (H.suc (H.suc (num R)))) e) := by
    intro t ht m m' hm _ g2 _
    obtain ⟨sgA, hsgA, hsegA, -, hpA⟩ := wcol e _ 2 he (fun i a h => ⟨i, h⟩)
      ((ar.nf.le_iff _ _).mpr ⟨3, by ring⟩)
    obtain ⟨sgB, hsgB, hsegB, -, hpB⟩ := wcol e _ 3 he (fun i a h => ⟨i, h⟩)
      ((ar.nf.le_iff _ _).mpr ⟨2, by ring⟩)
    have posA := fun x => nmAt_win ar ax hv hR (rad5 t ht) hsgA hsegA x
    have posB := fun x => nmAt_win ar ax hv hR (rad5 t ht) hsgB hsegB x
    have eA0 : num (2 + R) = H.suc (H.suc (num R)) := by
      rw [show (2 : N) + R = R + 1 + 1 from by ring, ar.iso.succ, ar.iso.succ]
    have eA1 : num (2 + (R2 + 1)) = H.suc (num R) := by
      rw [show (2 : N) + (R2 + 1) = R + 1 from by rw [hR]; ring, ar.iso.succ]
    have eA2 : num (2 + R2) = num R := by
      rw [show (2 : N) + R2 = R from by rw [hR]; ring]
    have eB0 : num (3 + R) = H.suc (H.suc (H.suc (num R))) := by
      rw [show (3 : N) + R = R + 1 + 1 + 1 from by ring, ar.iso.succ, ar.iso.succ, ar.iso.succ]
    have eB1 : num (3 + (R2 + 1)) = H.suc (H.suc (num R)) := by
      rw [show (3 : N) + (R2 + 1) = R + 1 + 1 from by rw [hR]; ring, ar.iso.succ, ar.iso.succ]
    have eB2 : num (3 + R2) = H.suc (num R) := by
      rw [show (3 : N) + R2 = R + 1 from by rw [hR]; ring, ar.iso.succ]
    rw [eA0, eA1, eA2] at posA
    rw [eB0, eB1, eB2] at posB
    have hP : Def1 H (fun b => b ∈ H.om ∧
        Fm.NmAt ar (num R) (num (R2 + 1)) (num R2) sgA (num t) b) := by hdef
    obtain ⟨m₁, hm₁, hmin⟩ := H.least' _ hP ⟨hm, (posA m).mpr g2⟩
    have hleB := (hpB t m₁ ht).mp ((hpA t m₁ ht).mpr ⟨hm₁, hmin⟩)
    exact ⟨m₁, (posA m₁).mp hm₁.2, (posB m₁).mp hleB.1.2⟩
  have hl' : R + 5 + R + 1 ≤ R + 5 + R + 1 := le_refl _
  exact ⟨e, nsat_of_dec ar ax he hlv hl' hdec, csat_of_dec ar ax cax he hlv hl' hdec hnum⟩


/-- **The clauses for NF and for the Axiom of Counting, from the partition theorem** for a
standard exponent. -/
theorem count_sound (ar : H.Arith E num) (ax : Fm.Ax) (cax : Fm.CAx) {Ms : ℕ → H.W} {C : H.W}
    {n : ℕ} (hl : H.LevSeq Ms C n) (hC : H.Closed C)
    (hlvl : ∀ a, a ∈ H.ords (Ms n) → a ≠ H.emp → Fm.Lv a)
    {q R R2 : N} (hR : R = R2 + 1 + 1) (hn : num (R + R + 1) = H.nmr n)
    (hrad : ∀ i : N, i + 1 ≤ q → 5 * i + 6 ≤ R) :
    ∃ e, NSat (fun i => Fm.AllT ar e (num i) (num R)) q ∧
      CSat (fun i => Fm.AllT ar e (num i) (num R)) q :=
  count_sound_gen ar ax cax (fun _ hcol _ hk => H.er_seq hl hcol hk) hC hlvl hR hn hrad

end FlatM
