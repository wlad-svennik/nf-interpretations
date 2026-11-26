module

public import FnInfinity
public import DedekindNaturals

@[expose] public section


set_option autoImplicit false
namespace FFL.FirstOrder.FNF.FunctionCut
open NFUCut
open JensenNFU.TFm (scons)
noncomputable section
variable {M : Type} [Tarski.Structure ℒλ M] [Tarski.Structure.Eq ℒλ M] [Nonempty M]
  [M↓[ℒλ] ⊧* 𝗙𝗡𝗙]

def width : Fml → Nat
  | .mem x y | .eq x y => max (x+1) (y+1)
  | .set x => x+1
  | .neg f => width f
  | .and f g => max (width f) (width g)
  | .all x f => max (x+1) (width f)

def bindIndex (idx : Nat → Nat) (x i : Nat) := if i=x then 0 else idx i+1

theorem bind_apply (idx : Nat → Nat) (x : Nat) (e : Nat → M) (a : M) :
    (fun i => scons a e (bindIndex idx x i)) = Function.update (fun i => e (idx i)) x a := by
  funext i
  by_cases h : i=x
  · subst i; simp [bindIndex]
  · simp [bindIndex,h,Function.update_of_ne h]

theorem bind_levels (σ : Nat → Nat) (N : Nat) (Γ : List Nat) (idx : Nat → Nat)
    (levels : ∀ i, i < N → Γ[idx i]? = some (σ i+1)) (x : Nat) :
    ∀ i, i < N → getElem? ((σ x+1)::Γ) (bindIndex idx x i) = some (σ i+1) := by
  intro i hi
  by_cases h : i=x
  · subst i; simp [bindIndex]
  · simp [bindIndex,h,levels i hi]

def term (σ : Nat → Nat) (N : Nat) (f : Fml) (size : width f ≤ N) (hs : f.strat σ = true)
    (Γ : List Nat) (idx : Nat → Nat) (levels : ∀ i, i<N → Γ[idx i]? = some (σ i+1)) :
    BT Γ (fun e : Nat → M => NFUCut.Sat Mem IsSet f (fun i => e (idx i))) :=
  match f with
  | .mem x y => by
    have hx : x<N := by simp only [width] at size; omega
    have hy : y<N := by simp only [width] at size; omega
    have eq : σ y = σ x + 1 := beq_iff_eq.mp hs
    exact BT.mem (idx x) (idx y) (σ x+1) (levels x hx) (by rw [levels y hy,eq])
  | .eq x y => by
    have hx : x<N := by simp only [width] at size; omega
    have hy : y<N := by simp only [width] at size; omega
    have eq : σ x = σ y := beq_iff_eq.mp hs
    exact BT.eq (idx x) (idx y) (σ x+1) (levels x hx) (by rw [levels y hy,eq])
  | .set x => BT.isSet (idx x) (σ x) (levels x (by simp only [width] at size; omega))
  | .neg f => (term σ N f size hs Γ idx levels).not
  | .and f g =>
    (term σ N f (by simp only [width] at size; omega) (Bool.and_eq_true_iff.mp hs).1 Γ idx levels).and
      (term σ N g (by simp only [width] at size; omega) (Bool.and_eq_true_iff.mp hs).2 Γ idx levels)
  | .all x f => by
    let P : BT ((σ x+1)::Γ) (fun e : Nat → M => NFUCut.Sat Mem IsSet f (fun i => e (bindIndex idx x i))) := term σ N f (by simp only [width] at size; omega) hs ((σ x+1)::Γ) (bindIndex idx x)
      (bind_levels σ N Γ idx levels x)
    apply (P.all (σ x+1)).congr
    intro e
    change (∀ a, NFUCut.Sat Mem IsSet f (fun i => scons a e (bindIndex idx x i))) ↔ _
    simp only [bind_apply,NFUCut.Sat]
termination_by f

def model : NFUCut.Model M where
  mem := fun x y => Mem x y
  isSet := fun x => IsSet x
  isSet_of_mem := fun h => h.1
  ext := fun hx hy h => set_ext hx hy h
  comp := by
    intro σ f x hs ρ
    let N := width f
    let Γ := (List.range N).map fun i => σ i+1
    let idx : Nat → Nat := fun i => i
    have lev : ∀ i, i<N → Γ[idx i]? = some (σ i+1) := by
      intro i hi
      simp [Γ,idx,List.getElem?_eq_getElem,hi]
    let P := term (M:=M) σ N f (Nat.le_refl _) hs ((σ x+1)::Γ) (bindIndex idx x)
      (bind_levels σ N Γ idx lev x)
    obtain ⟨y,hy,hr⟩ := P.set ρ
    refine ⟨y,hy,fun a => (hr a).trans ?_⟩
    change NFUCut.Sat Mem IsSet f (fun i => scons a ρ (bindIndex idx x i)) ↔ _
    rw [bind_apply]

private theorem finite_induction {V : Type} [Nonempty V] (M : NFUCut.Model V) {F : V} (h0 : M.mem M.emp F) (hs : ∀ s b, M.mem s F → M.mem (M.adj s b) F)
    {x : V} (hx : M.Fin x) : M.mem x F := by
  obtain ⟨-, k, hk, hxk⟩ := hx
  obtain ⟨I, -, hI⟩ := M.comp (fun i => if i = 1 then 1 else 2)
    (.all 1 (Fml.imp (.mem 1 0) (.mem 1 2))) 0 rfl (Function.update (fun _ => F) 2 F)
  have hI' : ∀ k, M.mem k I ↔ ∀ x, M.mem x k → M.mem x F := by
    intro k
    rw [hI k]
    simp [Sat, M.sat_imp, Function.update_apply]
  have key : M.mem k I := by
    refine M.nat_ind ((hI' _).mpr fun x hx => ?_) (fun k hk => (hI' _).mpr fun x hx => ?_) hk
    · rw [M.mem_zero.mp hx]
      exact h0
    · obtain ⟨y, b, hy, -, rfl⟩ := M.mem_succ.mp hx
      exact hs y b ((hI' k).mp hk y hy)
  exact (hI' k).mp key x hxk

theorem infinity : (model (M:=M)).Infinity := by
  let T := model (M:=M)
  obtain ⟨F,base,step,miss⟩ := univInfinite (M:=M)
  intro n hn all
  have fin : T.Fin T.univ := ⟨T.univ_isSet,n,hn,all⟩
  exact miss _ T.mem_univ (finite_induction T (F:=F) (base _ T.not_mem_emp)
    (fun a b ha => step a ha b _ (fun _ => T.mem_adj)) fin)
end
end FFL.FirstOrder.FNF.FunctionCut
#print axioms FFL.FirstOrder.FNF.FunctionCut.infinity
