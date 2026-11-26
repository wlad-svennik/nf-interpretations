module

public import ConNF.NF.NFUArith

@[expose] public section
set_option autoImplicit false
namespace NFUCut.Model.OrbitCounting
open NFUCut
variable {V : Type} [Nonempty V] (M : NFUCut.Model V)

/-- A finite initial part of the orbit, with its as-yet unused next member. -/
def Prefix (n d f t : V) : Prop := ∃ x a,
  M.mem x n ∧ M.mem a d ∧ ¬ M.mem a x ∧ (∀ y, M.mem y x → M.mem y d) ∧
  ∀ y, M.mem y x ∨ y = a → y = t ∨ ∃ z, M.mem z x ∧ M.mem (M.op z y) f

def prefixF : Fml := .ex 4 (.ex 5 (.and (.mem 4 0) (.and (.mem 5 1) (.and (.neg (.mem 5 4))
  (.and (.all 6 (.imp (.mem 6 4) (.mem 6 1)))
    (.all 6 (.imp (.or (.mem 6 4) (.eq 6 5))
     (.or (.eq 6 3) (.ex 7 (.and (.mem 7 4) (.ex 8 (.and (.mem 8 2) (fOp 8 7 6 9 10)))))))))))))

def level (i : Nat) := if i = 2 then 3 else if i = 0 ∨ i = 8 then 2 else if i = 1 ∨ i = 4 ∨ i = 9 then 1 else 0

private theorem sat_prefix (n d f t : V) :
    Sat M.mem M.isSet prefixF (Function.update (fun i => if i=1 then d else if i=2 then f else t) 0 n) ↔
      Prefix M n d f t := by
  simp only [prefixF, M.sat_ex, Sat, M.sat_imp, M.sat_or,
    M.sat_fOp (p:=8) (a:=7) (b:=6) (u:=9) (c:=10) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp [Prefix]

/-- A represented proper endoinjection on a strongly Cantorian set implies the Axiom of Counting on all internal natural numbers. -/
theorem all_inS (d f t : V) (F : V → V) (strong : M.SC d) (seed : M.mem t d)
    (maps : ∀ x, M.mem x d → M.mem (F x) d)
    (injective : ∀ x y, M.mem x d → M.mem y d → F x = F y → x = y)
    (misses : ∀ x, M.mem x d → F x ≠ t)
    (graph : ∀ x y, M.mem x d → (M.mem (M.op x y) f ↔ F x = y)) :
    ∀ n, M.mem n M.nat → M.InS n := by
  obtain ⟨i,_,hi⟩ := M.comp level prefixF 0 (by decide) (fun j => if j=1 then d else if j=2 then f else t)
  have mem (n : V) : M.mem n i ↔ Prefix M n d f t := (hi n).trans (sat_prefix M n d f t)
  have zero : Prefix M M.zero d f t := by
    refine ⟨M.emp,t,M.mem_zero.mpr rfl,seed,M.not_mem_emp t,fun y h => False.elim (M.not_mem_emp y h),?_⟩
    intro y hy
    exact Or.inl (hy.resolve_left (M.not_mem_emp y))
  have step (n : V) (hn : Prefix M n d f t) : Prefix M (M.succ n) d f t := by
    obtain ⟨x,a,hx,ha,fresh,sub,span⟩ := hn
    have free : ¬ M.mem (F a) (M.adj x a) := by
      intro h
      obtain old | predecessor := span _ (M.mem_adj.mp h)
      · exact misses a ha old
      · obtain ⟨z,hz,edge⟩ := predecessor
        have same := injective z a (sub z hz) ha ((graph z (F a) (sub z hz)).mp edge)
        exact fresh (same ▸ hz)
    refine ⟨M.adj x a,F a,M.mem_succ.mpr ⟨x,a,hx,fresh,rfl⟩,maps a ha,free,?_,?_⟩
    · intro y hy
      exact (M.mem_adj.mp hy).elim (sub y) (fun e => e ▸ ha)
    · intro y hy
      rcases hy with h | rfl
      · rcases span y (M.mem_adj.mp h) with old | ⟨z,hz,hzy⟩
        · exact Or.inl old
        · exact Or.inr ⟨z,M.mem_adj.mpr (Or.inl hz),hzy⟩
      · exact Or.inr ⟨a,M.mem_adj.mpr (Or.inr rfl),(graph a (F a) ha).mpr rfl⟩
  intro n hn
  obtain ⟨x,_,hx,_,_,sub,_⟩ := (mem n).mp (M.mem_nat.mp hn i ⟨(mem _).mpr zero,fun k hk => (mem _).mpr (step k ((mem _).mp hk))⟩)
  exact ⟨hn,x,hx,M.sc_subset strong sub⟩

theorem counting [Fact M.Infinity] (d f t : V) (F : V → V) (strong : M.SC d) (seed : M.mem t d)
    (maps : ∀ x, M.mem x d → M.mem (F x) d)
    (injective : ∀ x y, M.mem x d → M.mem y d → F x = F y → x = y)
    (misses : ∀ x, M.mem x d → F x ≠ t)
    (graph : ∀ x y, M.mem x d → (M.mem (M.op x y) f ↔ F x = y)) : ∀ n : M.Num, M.T n = n :=
  fun n => M.T_eq_self_of_inS (all_inS M d f t F strong seed maps injective misses graph n.1 n.2)
end NFUCut.Model.OrbitCounting
#print axioms NFUCut.Model.OrbitCounting.counting
