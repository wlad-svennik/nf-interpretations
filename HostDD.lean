module

public import HostCount

@[expose] public section

set_option autoImplicit false

/-!
# The flat model of a tower satisfies the existence axioms for `US`, `SC` and `DD`

In a tower (`Host.Tower`).

* `pred_inv`: comprehension for a definable property of the objects of a lower level that is
  preserved by the automorphisms. (`Tower.pred` is the case of a property given by a typed
  formula.)
* `sz_low`: "the object has `m` members", for a number `m` of the host, is preserved by the
  automorphisms: they act one-to-one on the objects of each lower level and respect membership.
* `us_ex`, `sc_ex`: the set of the singletons of the members of an object, and the successor of
  an object, by `Tower.pred`.
* `nm_ex`: the set of all objects with `m` members is an object. `dd_ex`: so is the set of these
  sets, for `m` ranging over the numbers of the host.
* **`flat_cax : T.flat.CAx`**.
-/

namespace Host

variable {H : Host}

namespace Tower

variable (T : Tower H)

/-- **Comprehension for invariant properties.** A definable property of the objects of the
level `b` that is preserved by the automorphisms of the level `a` is the extension of an object
of the level `a`. -/
theorem pred_inv {a b : H.W} (ha : T.Proper a) (hba : b ∈ a) (hb0 : b ≠ H.emp)
    (P : H.W → Prop) (hP : Def1 H P)
    (hinv : ∀ π, H.IsAut T.M T.d T.F a π → ∀ z z', z ∈ T.Tp b → P z →
      H.ActLow T.F a π b z z' → P z') :
    ∃ y, y ∈ T.Tp a ∧ ∀ z, z ∈ T.Tp b → (H.Mem T.M T.d T.F a b z y ↔ P z) := by
  obtain ⟨X, hX⟩ := H.sep' (T.Tp b) P hP
  have hXT : ∀ z, z ∈ X → z ∈ T.Ts b := fun z hz => by
    rw [T.Ts_of_ne hb0]
    exact ((hX z).mp hz).1
  obtain ⟨y, hy, -, hcase⟩ := T.symm_comp ha (T.hI a) hba hXT H.fin_emp
    (fun v hv => (H.not_mem_emp v hv).elim)
    (fun π hπ _ z z' hz hact => by
      obtain ⟨hzT, hPz⟩ := (hX z).mp hz
      have hz'T : z' ∈ T.Tp b := by
        have h := T.low_mem ha (T.hI a) hπ hba (hXT z hz) hact
        rwa [T.Ts_of_ne hb0] at h
      exact (hX z').mpr ⟨hz'T, hinv π hπ z z' hzT hPz hact⟩)
  have hExt : T.Ext a y b X := by
    rcases hcase with ⟨hX0, e⟩ | e | ⟨β', X', e, hinv'⟩
    · refine ⟨H.emp, H.emp, e, Or.inr ⟨fun h => hb0 h.symm, fun l => ?_⟩⟩
      rw [hX0]
      exact ⟨fun h => (H.not_mem_emp l h).elim,
        fun ⟨c, S, X', η, x, _, _, hx, _⟩ => (H.not_mem_emp x hx).elim⟩
    · exact ⟨b, X, e, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨β', X', e, Or.inr ⟨hinv'.2.2.2.1, hinv'.2.2.2.2.2.2⟩⟩
  refine ⟨y, hy, fun z hz => ?_⟩
  rw [T.mem_of_ext hExt, hX z]
  exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩

/-- Every object of a lower level is the image of an object under the action. -/
theorem low_pre {a b π z' : H.W} (ha : T.Proper a) (hπ : H.IsAut T.M T.d T.F a π) (hba : b ∈ a)
    (hz' : z' ∈ T.Ts b) :
    ∃ z, z ∈ T.Ts b ∧ H.ActLow T.F a π b z z' ∧ H.ActLow T.F a (H.inv π) b z' z := by
  obtain ⟨z, hz, hact⟩ := T.low_tot ha (T.hI a) (isAut_inv hπ) hba hz'
  have h3 := T.low_inv ha (T.hI a) (isAut_inv hπ) hba hz' hact
  rw [inv_inv hπ.1.1.1] at h3
  exact ⟨z, hz, h3, hact⟩

/-- The number of the members of an object is preserved by the automorphisms of its level. -/
theorem sz_act {a2 a3 ρ x x' m : H.W} (ha2 : T.Proper a2) (hρ : H.IsAut T.M T.d T.F a2 ρ)
    (h32 : a3 ∈ a2) (h30 : a3 ≠ H.emp) (hx : x ∈ T.Tp a2) (hact : H.ActRaw T.F a2 ρ x x')
    (h : T.flat.Sz a2 a3 x m) : T.flat.Sz a2 a3 x' m := by
  have ha3 := T.lower_proper ha2 h32 h30
  obtain ⟨f, hf, g1, g2, g3⟩ := h
  have ts : ∀ z, z ∈ T.Ts a3 ↔ z ∈ T.Tp a3 := fun z => by rw [T.Ts_of_ne h30]
  have hfun : ∀ u ∈ m, ∀ s s', (∃ w, H.App f u w ∧ H.ActLow T.F a2 ρ a3 w s) →
      (∃ w, H.App f u w ∧ H.ActLow T.F a2 ρ a3 w s') → s = s' := by
    rintro u - s s' ⟨w, hw, hs⟩ ⟨w', hw', hs'⟩
    rw [← hf.1.2 _ _ _ hw hw'] at hs'
    exact T.low_fun hρ.1.1 hs hs'
  have key : ∀ z z', z ∈ T.Tp a3 → H.ActLow T.F a2 ρ a3 z z' →
      (T.flat.El z x (H.op a2 a3) ↔ T.flat.El z' x' (H.op a2 a3)) := fun z z' hz hzz => by
    rw [T.flat_el, T.flat_el]
    exact T.mem_equi ha2 hρ hx hact h32 h30 hz hzz
  refine ⟨H.mkFun m (fun u s => ∃ w, H.App f u w ∧ H.ActLow T.F a2 ρ a3 w s) (by hdef) hfun,
    ⟨H.isFun_mkFun, fun i => ⟨fun hi => ?_, fun ⟨s, hs⟩ => (H.app_mkFun.mp hs).1⟩⟩,
    fun i s hi => ?_, fun s hs hel => ?_, fun i j s hi hj => ?_⟩
  · obtain ⟨w, hw⟩ := (hf.2 i).mp hi
    have hwT := (T.flat_ob' ha3).mp (g1 i w hw).1
    obtain ⟨s, -, hs⟩ := T.low_tot ha2 (T.hI a2) hρ h32 ((ts w).mpr hwT)
    exact ⟨s, H.app_mkFun.mpr ⟨hi, w, hw, hs⟩⟩
  · obtain ⟨-, w, hw, hs⟩ := H.app_mkFun.mp hi
    have hwT := (T.flat_ob' ha3).mp (g1 i w hw).1
    have hsT := (ts s).mp (T.low_mem ha2 (T.hI a2) hρ h32 ((ts w).mpr hwT) hs)
    exact ⟨(T.flat_ob' ha3).mpr hsT, (key w s hwT hs).mp (g1 i w hw).2⟩
  · have hsT := (T.flat_ob' ha3).mp hs
    obtain ⟨w, hw, hws, -⟩ := T.low_pre ha2 hρ h32 ((ts s).mpr hsT)
    have hwT := (ts w).mp hw
    obtain ⟨i, hi⟩ := g2 w ((T.flat_ob' ha3).mpr hwT) ((key w s hwT hws).mpr hel)
    exact ⟨i, H.app_mkFun.mpr ⟨(hf.2 i).mpr ⟨w, hi⟩, w, hi, hws⟩⟩
  · obtain ⟨-, w, hw, hs⟩ := H.app_mkFun.mp hi
    obtain ⟨-, w', hw', hs'⟩ := H.app_mkFun.mp hj
    have hwT := (T.flat_ob' ha3).mp (g1 i w hw).1
    have hw'T := (T.flat_ob' ha3).mp (g1 j w' hw').1
    have e1 := T.low_inv ha2 (T.hI a2) hρ h32 ((ts w).mpr hwT) hs
    have e2 := T.low_inv ha2 (T.hI a2) hρ h32 ((ts w').mpr hw'T) hs'
    have e : w = w' := T.low_fun (isAut_inv hρ).1.1 e1 e2
    rw [← e] at hw'
    exact g3 i j w hw hw'

/-- The same, for the action of an automorphism of a higher level. -/
theorem sz_low {a1 a2 a3 π x x' m : H.W} (ha1 : T.Proper a1) (hπ : H.IsAut T.M T.d T.F a1 π)
    (h21 : a2 ∈ a1) (h20 : a2 ≠ H.emp) (h32 : a3 ∈ a2) (h30 : a3 ≠ H.emp)
    (hact : H.ActLow T.F a1 π a2 x x') (h : T.flat.Sz a2 a3 x m) : T.flat.Sz a2 a3 x' m := by
  have ha2 := T.lower_proper ha1 h21 h20
  rcases hact with ⟨e, -⟩ | ⟨-, ρ, hρ, hA⟩
  · exact (h20 e).elim
  · have hρa := der_aut (T.proper_om ha1) ha1.1 h21 h20 hπ hρ
    obtain ⟨hx, hraw⟩ := (T.low_proper ha1 (T.invT_all _ ha2) h21 h20 hπ hρ).mp
      (Or.inr ⟨h20, ρ, hρ, hA⟩)
    exact T.sz_act ha2 hρa h32 h30 hx hraw h

/-- **The set of all objects with `m` members is an object.** -/
theorem nm_ex {a1 a2 a3 : H.W} (m : H.W) (ha1 : T.Proper a1) (h21 : a2 ∈ a1) (h20 : a2 ≠ H.emp)
    (h32 : a3 ∈ a2) (h30 : a3 ≠ H.emp) : ∃ n, T.flat.IsNm a1 a2 a3 m n := by
  have ha2 := T.lower_proper ha1 h21 h20
  have hdO := T.flat.defOb
  have hdE := T.flat.defEl
  obtain ⟨n, hn, h⟩ := T.pred_inv ha1 h21 h20 (fun x => T.flat.Sz a2 a3 x m) (by hdef)
    (fun π hπ z z' _ hz hact => T.sz_low ha1 hπ h21 h20 h32 h30 hact hz)
  exact ⟨n, (T.flat_ob' ha1).mpr hn, fun x hx => by
    rw [T.flat_el]
    exact h x ((T.flat_ob' ha2).mp hx)⟩

/-- **The set of the sets of all objects with `m` members, for the numbers `m` of the host, is
an object.** -/
theorem dd_ex {a a1 a2 a3 : H.W} (ha : T.Proper a) (h1 : a1 ∈ a) (h10 : a1 ≠ H.emp)
    (h21 : a2 ∈ a1) (h20 : a2 ≠ H.emp) (h32 : a3 ∈ a2) (h30 : a3 ≠ H.emp) :
    ∃ y, T.flat.Ob y a ∧ ∀ n, T.flat.Ob n a1 →
      (T.flat.El n y (H.op a a1) ↔ ∃ m, m ∈ H.om ∧ T.flat.IsNm a1 a2 a3 m n) := by
  have ha1 := T.lower_proper ha h1 h10
  have ha2 := T.lower_proper ha1 h21 h20
  have hdO := T.flat.defOb
  have hdE := T.flat.defEl
  have ts : ∀ z, z ∈ T.Ts a2 ↔ z ∈ T.Tp a2 := fun z => by rw [T.Ts_of_ne h20]
  obtain ⟨y, hy, h⟩ := T.pred_inv ha h1 h10
    (fun n => ∃ m, m ∈ H.om ∧ T.flat.IsNm a1 a2 a3 m n) (by hdef)
    (fun π hπ n n' hn ⟨m, hm, hnm⟩ hact => by
      rcases hact with ⟨e, -⟩ | ⟨-, ρ, hρ, hA⟩
      · exact (h10 e).elim
      · have hρa := der_aut (T.proper_om ha) ha.1 h1 h10 hπ hρ
        obtain ⟨-, hraw⟩ := (T.low_proper ha (T.invT_all _ ha1) h1 h10 hπ hρ).mp
          (Or.inr ⟨h10, ρ, hρ, hA⟩)
        have hn' := T.act_mem ha1 hρa hn hraw
        refine ⟨m, hm, (T.flat_ob' ha1).mpr hn', fun x' hx' => ?_⟩
        have hx'T := (T.flat_ob' ha2).mp hx'
        obtain ⟨x, hx, hxx', hx'x⟩ := T.low_pre ha1 hρa h21 ((ts x').mpr hx'T)
        have hxT := (ts x).mp hx
        rw [T.flat_el, ← T.mem_equi ha1 hρa hn hraw h21 h20 hxT hxx', ← T.flat_el,
          hnm.2 x ((T.flat_ob' ha2).mpr hxT)]
        exact ⟨fun hs => T.sz_low ha1 hρa h21 h20 h32 h30 hxx' hs,
          fun hs => T.sz_low ha1 (isAut_inv hρa) h21 h20 h32 h30 hx'x hs⟩)
  exact ⟨y, (T.flat_ob' ha).mpr hy, fun n hn => by
    rw [T.flat_el]
    exact h n ((T.flat_ob' ha1).mp hn)⟩

/-- **The set of the singletons of the members of an object.** -/
theorem us_ex {a a1 a2 x : H.W} (ha : T.Proper a) (h1 : a1 ∈ a) (h10 : a1 ≠ H.emp)
    (h21 : a2 ∈ a1) (h20 : a2 ≠ H.emp) (hx : x ∈ T.Tp a1) :
    ∃ y, y ∈ T.Tp a ∧ ∀ s, s ∈ T.Tp a1 → (H.Mem T.M T.d T.F a a1 s y ↔
      ∃ w, w ∈ T.Tp a2 ∧ (H.Mem T.M T.d T.F a1 a2 w x ∧ T.IsSing a1 a2 w s)) := by
  have hc := T.chain3_ok ha h1 h10 h21 h20
  obtain ⟨y, hy, h⟩ := T.pred hc (by omega)
    (φ := .ex 2 1 (.and (.mem 1 1 1) (fSing 1 0 1 9)))
    (by simp [CForm.Ok, fSing])
    (T.upd2_typed (j := 1) (y := 1) (T.env0_typed hc) hx) _ (upd2_supp env0_supp)
  refine ⟨y, hy, fun p hp => (h p hp).trans ?_⟩
  simp only [Sat]
  refine exists_congr fun q => and_congr Iff.rfl (and_congr ?_ ?_)
  · simp [upd2, chainL]
  · rw [T.sat_fSing _ _ 1 0 1 9 (by decide)]
    simp [upd2, chainL, IsSing, hp]

/-- **The successor of an object**: the set of the objects that are a member of it with one
further member. -/
theorem sc_ex {a a1 a2 c : H.W} (ha : T.Proper a) (h1 : a1 ∈ a) (h10 : a1 ≠ H.emp)
    (h21 : a2 ∈ a1) (h20 : a2 ≠ H.emp) (hc' : c ∈ T.Tp a) :
    ∃ y, y ∈ T.Tp a ∧ ∀ o, o ∈ T.Tp a1 → (H.Mem T.M T.d T.F a a1 o y ↔
      ∃ x, x ∈ T.Tp a1 ∧ (H.Mem T.M T.d T.F a a1 x c ∧ ∃ b, b ∈ T.Tp a2 ∧
        (¬ H.Mem T.M T.d T.F a1 a2 b x ∧ ∀ z, z ∈ T.Tp a2 →
          (H.Mem T.M T.d T.F a1 a2 z o ↔ H.Mem T.M T.d T.F a1 a2 z x ∨ z = b)))) := by
  have hc := T.chain3_ok ha h1 h10 h21 h20
  obtain ⟨y, hy, h⟩ := T.pred hc (by omega)
    (φ := .ex 1 2 (.and (.mem 0 2 1) (.ex 2 1 (.and (.neg (.mem 1 1 2))
      (.all 2 3 (.iff (.mem 1 3 0) (.or (.mem 1 3 2) (.eq 2 3 1))))))))
    (by simp [CForm.Ok])
    (T.upd2_typed (j := 0) (y := 1) (T.env0_typed hc) hc') _ (upd2_supp env0_supp)
  refine ⟨y, hy, fun p hp => (h p hp).trans ?_⟩
  simp only [Sat]
  simp [upd2, chainL]

/-- **The flat model of a tower satisfies the existence axioms for the symbols of the Axiom of
Counting.** -/
theorem flat_cax : T.flat.CAx where
  us := fun a a1 a2 x h1 h2 hx => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    obtain ⟨y, hy, h⟩ := T.us_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 ((T.flat_ob' hb).mp hx)
    refine ⟨y, (T.flat_ob' h1.1).mpr hy, fun s hs => ?_⟩
    rw [T.flat_el]
    exact (h s ((T.flat_ob' hb).mp hs)).trans (exists_congr fun w =>
      and_congr (T.flat_ob' hc).symm
        (and_congr T.flat_el.symm (T.flat_sg hb h2.2.1 h2.2.2).symm))
  sc := fun a a1 a2 c h1 h2 hc' => by
    have hb := T.lower_proper h1.1 h1.2.1 h1.2.2
    have hc := T.lower_proper hb h2.2.1 h2.2.2
    obtain ⟨y, hy, h⟩ := T.sc_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 ((T.flat_ob' h1.1).mp hc')
    refine ⟨y, (T.flat_ob' h1.1).mpr hy, fun o ho => ?_⟩
    rw [T.flat_el]
    refine (h o ((T.flat_ob' hb).mp ho)).trans ?_
    constructor
    · rintro ⟨x, hx, hxc, b, hb', hbx, hall⟩
      exact ⟨x, b, (T.flat_ob' hb).mpr hx, T.flat_el.mpr hxc, (T.flat_ob' hc).mpr hb',
        fun hh => hbx (T.flat_el.mp hh), fun z hz => by
          rw [T.flat_el, T.flat_el]
          exact hall z ((T.flat_ob' hc).mp hz)⟩
    · rintro ⟨x, b, hx, hxc, hb', hbx, hall⟩
      exact ⟨x, (T.flat_ob' hb).mp hx, T.flat_el.mp hxc, b, (T.flat_ob' hc).mp hb',
        fun hh => hbx (T.flat_el.mpr hh), fun z hz => by
          have h4 := hall z ((T.flat_ob' hc).mpr hz)
          rwa [T.flat_el, T.flat_el] at h4⟩
  dd := fun a a1 a2 a3 h1 h2 h3 =>
    T.dd_ex h1.1 h1.2.1 h1.2.2 h2.2.1 h2.2.2 h3.2.1 h3.2.2

end Tower

end Host
