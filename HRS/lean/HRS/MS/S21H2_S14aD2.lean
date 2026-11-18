import HRS.MS.S21H2_S14aD1
import HRS.MS.S111X2Aux3

/-!
# S21H2, packet R26-T3.S14a (part D2): the operator `K` of `KRep` is the integral operator of the centered kernel, and its Hilbert-Schmidt bound

For `hK : KRep g μ K Mg` and `k(x,y) = g(x - y) ∈ L²(μ⊗μ)`: on centered classes `K U =ᵐ ∫ c(·,y) U(y) dμ(y)` (`c` the centered kernel), and for every
finite orthonormal family `v_i` of centered classes, `∑_i ‖K v_i‖² ≤ ‖c‖²_{L²(μ⊗μ)` (Bessel in the second variable for a.e. slice `c(x,·)`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS.Whole.Q34 HRS.MS.S111X2

variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] {g : HRS.Euc d → ℝ}
  {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {Mg : ℝ}

theorem s21h2_mean_zero {U : Lp ℝ 2 μ} (hU : inner ℝ (one2 μ) U = 0) : ∫ y, U y ∂μ = 0 := by
  rw [← inner_one2]; exact hU

theorem s21h2_KC (hK : KRep g μ K Mg)
    (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => g (z.1 - z.2)) 2 (μ.prod μ))
    (U : Lp ℝ 2 μ) (hU : inner ℝ (one2 μ) U = 0) :
    (K U : HRS.Euc d → ℝ) =ᵐ[μ] fun x => ∫ y, HRS.Whole.r2CenterKernel μ (fun a b => g (a - b)) x y * U y ∂μ := by
  have hPU : Pc μ U = U := by rw [Pc_apply, hU, zero_smul, sub_zero]
  have hkop := hK.kop U hPU
  have hc := s21h2_c_apply μ (k := fun a b => g (a - b)) hk (Lp.memLp U) (s21h2_mean_zero hU)
  filter_upwards [hkop, hc] with x h1 h2
  rw [← h1, h2]
  simp only [HRS.Whole.Kop, HRS.Whole.projMean, HRS.Whole.pair]

theorem s21h2_hs_bound (hK : KRep g μ K Mg)
    (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => g (z.1 - z.2)) 2 (μ.prod μ))
    {ι : Type*} (v : ι → Lp ℝ 2 μ) (hv : Orthonormal ℝ v) (hv0 : ∀ i, inner ℝ (one2 μ) (v i) = 0)
    (s : Finset ι) :
    ∑ i ∈ s, ‖K (v i)‖ ^ 2 ≤
      ∫ z : HRS.Euc d × HRS.Euc d, HRS.Whole.r2CenterKernel μ (fun a b => g (a - b)) z.1 z.2 ^ 2 ∂(μ.prod μ) := by
  set c := HRS.Whole.r2CenterKernel μ (fun a b => g (a - b)) with hc
  have hcm := s21h2_c_memLp μ (k := fun a b => g (a - b)) hk
  set a : ι → HRS.Euc d → ℝ := fun i x => ∫ y, c x y * v i y ∂μ with ha
  have hKa : ∀ i, (K (v i) : HRS.Euc d → ℝ) =ᵐ[μ] a i := fun i => s21h2_KC hK hk (v i) (hv0 i)
  have hnorm : ∀ i, ‖K (v i)‖ ^ 2 = ∫ x, a i x ^ 2 ∂μ := fun i =>
    (integral_sq_eq (hKa i).symm).symm
  have hint : ∀ i, Integrable (fun x => a i x ^ 2) μ := fun i =>
    ((Lp.memLp (K (v i))).integrable_sq).congr (by filter_upwards [hKa i] with x hx; rw [hx])
  simp_rw [hnorm]
  rw [← integral_finsetSum _ fun i _ => hint i]
  have hq : Integrable (fun x => ∫ y, c x y ^ 2 ∂μ) μ := hcm.integrable_sq.integral_prod_left
  have hfub : ∫ z : HRS.Euc d × HRS.Euc d, c z.1 z.2 ^ 2 ∂(μ.prod μ) = ∫ x, ∫ y, c x y ^ 2 ∂μ ∂μ :=
    integral_prod (fun z : HRS.Euc d × HRS.Euc d => c z.1 z.2 ^ 2) hcm.integrable_sq
  rw [hfub]
  refine integral_mono_ae (integrable_finsetSum _ fun i _ => hint i) hq ?_
  filter_upwards [s21h2_c_slice μ (k := fun a b => g (a - b)) hk] with x hx
  set w : Lp ℝ 2 μ := hx.1.toLp (fun y => c x y) with hw
  have hwa : (w : HRS.Euc d → ℝ) =ᵐ[μ] fun y => c x y := hx.1.coeFn_toLp
  have hin : ∀ i, inner ℝ (v i) w = a i x := fun i => by
    rw [lp_inner]
    refine integral_congr_ae ?_
    filter_upwards [hwa] with y hy
    rw [hy]; ring
  have hB := hv.sum_inner_products_le (𝕜 := ℝ) w (s := s)
  have hwn : ‖w‖ ^ 2 = ∫ y, c x y ^ 2 ∂μ := (integral_sq_eq hwa.symm).symm
  calc ∑ i ∈ s, a i x ^ 2 = ∑ i ∈ s, ‖inner ℝ (v i) w‖ ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hin, Real.norm_eq_abs, sq_abs]
    _ ≤ ‖w‖ ^ 2 := hB
    _ = _ := hwn

end HRS.MS.R26T3
