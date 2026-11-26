module

public import ConNF.NF.NFUArith
public import CountAxioms

@[expose] public section

set_option autoImplicit false

/-!
# The Axiom of Counting in a model of NFU + Infinity

`M` is a model of NFU in the sense of `NFUCut.Model`, with Infinity. Two statements of the
Axiom of Counting are compared:

* `∀ n : M.Num, M.T n = n`, with the natural numbers and the operation `T` of `NFUArith`;
* `JensenNFU.Counting M.mem`, the statement that uses only membership (`CountAxioms.lean`).

They differ in what zero is. In `NFUArith` zero is `{∅}`, where `∅` is the empty *set*. With
membership alone the empty set cannot be told from the other objects without members, and zero
is the set `zeroN` of all of them. From `1` on the two sequences of numbers are the same
(`succ_zeroN`).

* `counting_iff_T`: the two statements are equivalent.
* `T_eq_self_of_T_T`: if `T (T n) = n` for every `n`, then `T n = n` for every `n`.
-/

namespace NFUCut.Model

open NFUCut JensenNFU

variable {V : Type} [Nonempty V] (M : NFUCut.Model V)

/-! ### Zero and successor in terms of membership -/

theorem exists_zeroN : ∃ z, M.isSet z ∧ ∀ e, M.mem e z ↔ ∀ w, ¬ M.mem w e := by
  obtain ⟨z, hz, h⟩ := M.comp (fun i => if i = 1 then 0 else 1) (.all 1 (.neg (.mem 1 0))) 0 rfl
    (fun _ => dflt)
  refine ⟨z, hz, fun e => ?_⟩
  rw [h e]
  simp [Sat]

/-- The set of the objects without members. -/
noncomputable def zeroN : V := Classical.choose M.exists_zeroN

theorem zeroN_isSet : M.isSet M.zeroN := (Classical.choose_spec M.exists_zeroN).1

theorem mem_zeroN {e : V} : M.mem e M.zeroN ↔ ∀ w, ¬ M.mem w e :=
  (Classical.choose_spec M.exists_zeroN).2 e

theorem emp_mem_zeroN : M.mem M.emp M.zeroN := M.mem_zeroN.mpr M.not_mem_emp

theorem isZeroN_zeroN : IsZeroN M.mem M.zeroN := fun _ => M.mem_zeroN

theorem isZeroN_iff {z : V} : IsZeroN M.mem z ↔ z = M.zeroN := by
  constructor
  · intro h
    exact M.ext (M.isSet_of_mem ((h M.emp).mpr M.not_mem_emp)) M.zeroN_isSet fun e =>
      (h e).trans M.mem_zeroN.symm
  · rintro rfl
    exact M.isZeroN_zeroN

/-- The successor of `NFUArith` is a successor in terms of membership. -/
theorem isSuccN_succ (k : V) : IsSuccN M.mem k (M.succ k) := by
  intro y
  rw [M.mem_succ]
  constructor
  · rintro ⟨x, b, hx, hb, rfl⟩
    exact ⟨x, hx, b, hb, fun z => M.mem_adj⟩
  · rintro ⟨x, hx, b, hb, h⟩
    exact ⟨x, b, hx, hb, M.eq_adj_iff.mp h⟩

/-- A successor in terms of membership of a number with a member that omits some object is the
successor of `NFUArith`. -/
theorem eq_succ_of_isSuccN {k k' : V} (hne : ∃ x b, M.mem x k ∧ ¬ M.mem b x)
    (h : IsSuccN M.mem k k') : k' = M.succ k := by
  obtain ⟨x, b, hx, hb⟩ := hne
  have hmem : M.mem (M.adj x b) k' := (h _).mpr ⟨x, hx, b, hb, fun z => M.mem_adj⟩
  exact M.ext (M.isSet_of_mem hmem) (M.succ_isSet k) fun y =>
    (h y).trans ((M.isSuccN_succ k) y).symm

/-- From `1` on, the two sequences of numbers are the same. -/
theorem succ_zeroN : M.succ M.zeroN = M.succ M.zero := by
  refine M.ext (M.succ_isSet _) (M.succ_isSet _) fun y => ?_
  rw [M.mem_succ, M.mem_succ]
  constructor
  · rintro ⟨x, b, hx, -, rfl⟩
    refine ⟨M.emp, b, M.mem_zero.mpr rfl, M.not_mem_emp b, ?_⟩
    refine M.ext (M.adj_isSet _ _) (M.adj_isSet _ _) fun z => ?_
    rw [M.mem_adj, M.mem_adj]
    exact or_congr ⟨fun hz => absurd hz (M.mem_zeroN.mp hx z), fun hz => absurd hz (M.not_mem_emp z)⟩
      Iff.rfl
  · rintro ⟨x, b, hx, hb, rfl⟩
    rw [M.mem_zero.mp hx]
    exact ⟨M.emp, b, M.emp_mem_zeroN, M.not_mem_emp b, rfl⟩

/-! ### The two statements of the Axiom of Counting -/

section infinity

variable [hinf : Fact M.Infinity]

theorem exists_omit {k : V} (hk : M.mem k M.nat) : ∃ x b, M.mem x k ∧ ¬ M.mem b x := by
  obtain ⟨x, hx⟩ := M.nat_nonempty hk
  obtain ⟨b, hb⟩ := M.infinity_iff.mp hinf.out k hk x hx
  exact ⟨x, b, hx, hb⟩

/-- A natural number in terms of membership is `zeroN` or a natural number of `NFUArith` other
than zero. -/
theorem isNatN_cases {n : V} (hn : IsNatN M.mem n) :
    n = M.zeroN ∨ (M.mem n M.nat ∧ n ≠ M.zero) := by
  obtain ⟨F, -, hF⟩ := M.comp (fun i => if i = 2 then 1 else 0)
    (Fml.or (.eq 0 1) (.and (.mem 0 2) (.neg (.eq 0 3)))) 0 rfl
    (Function.update (Function.update (Function.update (fun _ => dflt) 1 M.zeroN) 2 M.nat) 3 M.zero)
  have hF' : ∀ m, M.mem m F ↔ (m = M.zeroN ∨ (M.mem m M.nat ∧ m ≠ M.zero)) := by
    intro m
    rw [hF m]
    simp [M.sat_or, Sat]
  refine (hF' n).mp (hn F ⟨fun z hz => (hF' z).mpr (Or.inl (M.isZeroN_iff.mp hz)),
    fun k hk k' hk' => (hF' k').mpr (Or.inr ?_)⟩)
  rcases (hF' k).mp hk with rfl | ⟨hkn, -⟩
  · obtain ⟨b⟩ := ‹Nonempty V›
    rw [M.eq_succ_of_isSuccN ⟨M.emp, b, M.emp_mem_zeroN, M.not_mem_emp b⟩ hk', M.succ_zeroN]
    exact ⟨M.succ_mem_nat M.zero_mem_nat, fun e => M.zero_ne_succ _ e.symm⟩
  · rw [M.eq_succ_of_isSuccN (M.exists_omit hkn) hk']
    exact ⟨M.succ_mem_nat hkn, fun e => M.zero_ne_succ _ e.symm⟩

omit hinf in
/-- A natural number of `NFUArith` other than zero is a natural number in terms of
membership. -/
theorem isNatN_of_mem_nat {n : V} (hn : M.mem n M.nat) (h0 : n ≠ M.zero) : IsNatN M.mem n := by
  rintro F ⟨hF0, hFs⟩
  obtain ⟨I, -, hI⟩ := M.comp (fun i => if i = 2 then 1 else 0)
    (Fml.or (.eq 0 1) (.mem 0 2)) 0 rfl
    (Function.update (Function.update (fun _ => dflt) 1 M.zero) 2 F)
  have hI' : ∀ m, M.mem m I ↔ (m = M.zero ∨ M.mem m F) := by
    intro m
    rw [hI m]
    simp [M.sat_or, Sat]
  have key : M.mem n I := by
    refine M.nat_ind ((hI' _).mpr (Or.inl rfl)) (fun k hk => (hI' _).mpr (Or.inr ?_)) hn
    rcases (hI' k).mp hk with rfl | hkF
    · rw [← M.succ_zeroN]
      exact hFs _ (hF0 _ M.isZeroN_zeroN) _ (M.isSuccN_succ _)
    · exact hFs k hkF _ (M.isSuccN_succ k)
  exact ((hI' n).mp key).resolve_left h0

/-- **The two statements of the Axiom of Counting are equivalent.** -/
theorem counting_iff_T : Counting M.mem ↔ ∀ n : M.Num, M.T n = n := by
  constructor
  · intro h n
    rcases M.nat_cases n.2 with h0 | ⟨k, hk, hs⟩
    · have e : n = 0 := Subtype.ext h0
      rw [e]
      exact M.T_zero
    · have hn0 : n.1 ≠ M.zero := fun e => M.zero_ne_succ k (e.symm.trans hs)
      obtain ⟨x, hx⟩ := M.nat_nonempty n.2
      obtain ⟨y, hy, hys⟩ := h n.1 (M.isNatN_of_mem_nat n.2 hn0) x hx
      have e : y = M.simg x := by
        refine M.ext (M.isSet_of_mem_nat n.2 hy) (M.simg_isSet x) fun s => ?_
        rw [hys s, M.mem_simg]
        exact exists_congr fun a => and_congr Iff.rfl M.eq_sing_iff
      rw [e] at hy
      exact M.T_eq_of_mem hx hy
  · intro hT n hn x hx
    rcases M.isNatN_cases hn with rfl | ⟨hnat, -⟩
    · refine ⟨x, hx, fun s => ⟨fun hs => absurd hs (M.mem_zeroN.mp hx s), ?_⟩⟩
      rintro ⟨a, ha, -⟩
      exact absurd ha (M.mem_zeroN.mp hx a)
    · refine ⟨M.simg x, ?_, fun s => ?_⟩
      · have := M.simg_mem_T (m := ⟨n, hnat⟩) hx
        rwa [hT ⟨n, hnat⟩] at this
      · rw [M.mem_simg]
        exact exists_congr fun a => and_congr Iff.rfl M.eq_sing_iff.symm

/-! ### `T` is monotone -/

/-- `∀w v (w ∈ n → v ∈ n → w ⊆ v → v ⊆ w)`; the variable `0` is `n`. -/
def subEqFml : Fml :=
  .all 1 (.all 2 (Fml.imp (.mem 1 0) (Fml.imp (.mem 2 0)
    (Fml.imp (.all 3 (Fml.imp (.mem 3 1) (.mem 3 2))) (.all 3 (Fml.imp (.mem 3 2) (.mem 3 1)))))))

omit hinf in
theorem sat_subEqFml (m : V) :
    Sat M.mem M.isSet subEqFml (Function.update (fun _ => dflt) 0 m) ↔
      ∀ w v, M.mem w m → M.mem v m → (∀ e, M.mem e w → M.mem e v) → ∀ e, M.mem e v → M.mem e w := by
  simp [subEqFml, M.sat_imp, Sat]

omit hinf in
/-- **Two members of a natural number, one included in the other, have the same members.** -/
theorem subset_of_subset_of_mem_nat {n w v : V} (hn : M.mem n M.nat) (hw : M.mem w n)
    (hv : M.mem v n) (h : ∀ e, M.mem e w → M.mem e v) : ∀ e, M.mem e v → M.mem e w := by
  have key := M.nat_ind_fml' (fun i => if i = 0 then 2 else if i = 3 then 0 else 1) subEqFml 0 rfl
    (fun _ => dflt) ((M.sat_subEqFml _).mpr ?_) (fun k hk ih => (M.sat_subEqFml _).mpr ?_) hn
  · exact (M.sat_subEqFml n).mp key w v hw hv h
  · intro w v _ hv _ e he
    rw [M.mem_zero.mp hv] at he
    exact absurd he (M.not_mem_emp e)
  · have ih' := (M.sat_subEqFml _).mp ih
    intro w v hw hv hwv e he
    obtain ⟨w', b, hw', hb, rfl⟩ := M.mem_succ.mp hw
    have hbw : M.mem b (M.adj w' b) := M.mem_adj.mpr (Or.inr rfl)
    have hbv : M.mem b v := hwv b hbw
    by_cases heb : e = b
    · rw [heb]
      exact hbw
    · have h1 := M.rem_mem_of_succ hk hw hbw
      have h2 := M.rem_mem_of_succ hk hv hbv
      have h3 := ih' _ _ h1 h2 (fun e' he' =>
        M.mem_rem.mpr ⟨hwv e' (M.mem_rem.mp he').1, (M.mem_rem.mp he').2⟩)
      exact (M.mem_rem.mp (h3 e (M.mem_rem.mpr ⟨he, heb⟩))).1

/-- **`T` is monotone.** -/
theorem T_mono {a b : M.Num} (h : a ≤ b) : M.T a ≤ M.T b := by
  obtain ⟨c, hc⟩ := M.le_def.mp h
  obtain ⟨x, hxb⟩ := M.nat_nonempty b.2
  have hx : M.mem x (a + c).1 := by rw [hc]; exact hxb
  obtain ⟨y, hy, hyx⟩ := M.exists_subset_of_add a c hx
  have hsy : M.mem (M.simg y) (M.T a).1 := M.simg_mem_T hy
  have hsx : M.mem (M.simg x) (M.T b).1 := M.simg_mem_T hxb
  have hsub : ∀ e, M.mem e (M.simg y) → M.mem e (M.simg x) := fun e he => by
    obtain ⟨u, hu, rfl⟩ := M.mem_simg.mp he
    exact M.mem_simg.mpr ⟨u, hyx u hu, rfl⟩
  rcases M.le_total' (M.T a) (M.T b) with h' | h'
  · exact h'
  · obtain ⟨d, hd⟩ := M.le_def.mp h'
    have hsy' : M.mem (M.simg y) (M.T b + d).1 := by rw [hd]; exact hsy
    obtain ⟨w, hw, hwy⟩ := M.exists_subset_of_add (M.T b) d hsy'
    have h1 : ∀ e, M.mem e (M.simg x) → M.mem e w :=
      M.subset_of_subset_of_mem_nat (M.T b).2 hw hsx (fun e he => hsub e (hwy e he))
    have e : M.simg y = M.simg x := M.ext (M.simg_isSet y) (M.simg_isSet x) fun z =>
      ⟨hsub z, fun hz => hwy z (h1 z hz)⟩
    rw [e] at hsy
    exact le_of_eq (Subtype.ext (M.nat_disjoint (M.T a).2 (M.T b).2 hsy hsx))

/-- **If `T (T n) = n` for every natural number `n`, then `T n = n` for every `n`.** -/
theorem T_eq_self_of_T_T (h : ∀ n : M.Num, M.T (M.T n) = n) (n : M.Num) : M.T n = n := by
  rcases M.le_total' (M.T n) n with h' | h'
  · refine le_antisymm h' ?_
    have := M.T_mono h'
    rwa [h n] at this
  · refine le_antisymm ?_ h'
    have := M.T_mono h'
    rwa [h n] at this

end infinity

end NFUCut.Model
