import HRS.Main.GFEVAux20

/-!
# Packet GFEVG, part 21: the coordinate projections `P_n` (Galerkin) and their properties
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

open Classical in
/-- the box of nonzero lattice points with `|k|_∞ ≤ n` -/
def gfevSn (d n : ℕ) : Finset (NonzeroLattice d) := (boxFinset d n).subtype (fun k => k ≠ 0)

theorem mem_gfevSn {n : ℕ} {k : NonzeroLattice d} : k ∈ gfevSn d n ↔ InBox n k.1 := by
  classical
  simp [gfevSn, mem_boxFinset]

def gfevP (S : Finset (NonzeroLattice d)) : L2 d →L[ℝ] L2 d :=
  ∑ k ∈ S, (innerSL ℝ (lp.single 2 k (1 : ℝ))).smulRight (lp.single 2 k (1 : ℝ))

theorem gfevP_coord (S : Finset (NonzeroLattice d)) (x : L2 d) (j : NonzeroLattice d) :
    (gfevP S x) j = if j ∈ S then x j else 0 := by
  classical
  unfold gfevP
  rw [ContinuousLinearMap.sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, lp.inner_single_left, lp.coeFn_smul,
    Pi.smul_apply, lp.single_apply, Pi.single_apply, smul_eq_mul]
  simp

theorem gfevP_idem (S : Finset (NonzeroLattice d)) (x : L2 d) : gfevP S (gfevP S x) = gfevP S x := by
  refine lp.ext (funext fun j => ?_)
  rw [gfevP_coord, gfevP_coord]
  by_cases hj : j ∈ S <;> simp [hj, gfevP_coord]

theorem gfevP_symm (S : Finset (NonzeroLattice d)) (x y : L2 d) :
    inner ℝ (gfevP S x) y = inner ℝ x (gfevP S y) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun j => ?_
  rw [gfevP_coord, gfevP_coord]
  by_cases hj : j ∈ S <;> simp [hj, mul_comm]

theorem gfevP_findim (S : Finset (NonzeroLattice d)) :
    FiniteDimensional ℝ (LinearMap.range (gfevP S : L2 d →ₗ[ℝ] L2 d)) := by
  classical
  have hle : LinearMap.range (gfevP S : L2 d →ₗ[ℝ] L2 d) ≤
      Submodule.span ℝ (↑(S.image fun k : NonzeroLattice d => lp.single 2 k (1 : ℝ)) : Set (L2 d)) := by
    rintro _ ⟨x, rfl⟩
    unfold gfevP
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    refine Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem _ hk)
  haveI := FiniteDimensional.span_finset ℝ (S.image fun k : NonzeroLattice d => lp.single 2 k (1 : ℝ))
  exact Submodule.finiteDimensional_of_le hle

theorem gfevSn_exhaust (F : Finset (NonzeroLattice d)) : ∃ n₀ : ℕ, ∀ n ≥ n₀, F ⊆ gfevSn d n := by
  classical
  refine ⟨F.sup fun k => ∑ i, (k.1 i).natAbs, fun n hn k hk => ?_⟩
  rw [mem_gfevSn]
  intro i
  have h1 : (k.1 i).natAbs ≤ F.sup fun k => ∑ i, (k.1 i).natAbs :=
    (Finset.single_le_sum (f := fun i => (k.1 i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun k : NonzeroLattice d => ∑ i, (k.1 i).natAbs) hk)
  have : ((k.1 i).natAbs : ℤ) ≤ n := by exact_mod_cast h1.trans hn
  simpa using this

theorem gfevP_tendsto (x : L2 d) : Tendsto (fun n : ℕ => gfevP (gfevSn d n) x) atTop (𝓝 x) := by
  classical
  have hs := lp.hasSum_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (by norm_num) x
  have heq : ∀ S : Finset (NonzeroLattice d), gfevP S x = ∑ k ∈ S, lp.single 2 k (x k) := by
    intro S
    refine lp.ext (funext fun j => ?_)
    rw [gfevP_coord, lp.coeFn_sum, Finset.sum_apply]
    simp [lp.single_apply, Pi.single_apply]
  have h0 : Tendsto (fun S : Finset (NonzeroLattice d) => ∑ k ∈ S, lp.single 2 k (x k)) atTop (𝓝 x) := hs
  have h1 : Tendsto (fun S : Finset (NonzeroLattice d) => gfevP S x) atTop (𝓝 x) :=
    h0.congr fun S => (heq S).symm
  have h2 : Tendsto (fun n : ℕ => gfevSn d n) atTop atTop :=
    Filter.tendsto_atTop_atTop.2 fun F => by
      obtain ⟨n₀, hn₀⟩ := gfevSn_exhaust F
      exact ⟨n₀, fun n hn => hn₀ n hn⟩
  exact h1.comp h2

end HRS.GF
