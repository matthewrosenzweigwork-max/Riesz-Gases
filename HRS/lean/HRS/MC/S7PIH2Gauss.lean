import HRS.MC.S7PIH1Taylor

/-!
# Packet piH, part 2: moments of a centred finite Gaussian
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIH

variable {q : ℕ}

/-- `‖Bz‖² = zᵀΔz` for `B = √Δ`. -/
theorem S7PIH_normB_sq {Δ : Matrix (Fin q) (Fin q) ℝ} (hΔ : Δ.PosSemidef)
    (z : EuclideanSpace ℝ (Fin q)) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Δ) z‖ ^ 2 = z.ofLp ⬝ᵥ Δ.mulVec z.ofLp := by
  set B := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Δ) with hB
  have hsa : IsSelfAdjoint B := (CFC.sqrt_nonneg Δ).isSelfAdjoint.map _
  have h1 : ‖B z‖ ^ 2 = inner ℝ (B z) (B z) := (real_inner_self_eq_norm_sq _).symm
  rw [h1, ← ContinuousLinearMap.adjoint_inner_left B z (B z), hsa.adjoint_eq, real_inner_comm,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, hB, ← map_mul,
    CFC.sqrt_mul_sqrt_self _ hΔ.nonneg, Matrix.inner_toEuclideanCLM]

/-- A matrix with entries bounded by `K` has quadratic form bounded by `q K ‖u‖²`. -/
theorem S7PIH_quad_bound {Δ : Matrix (Fin q) (Fin q) ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hΔ : ∀ i j, |Δ i j| ≤ K) (u : EuclideanSpace ℝ (Fin q)) :
    u.ofLp ⬝ᵥ Δ.mulVec u.ofLp ≤ q * K * ‖u‖ ^ 2 := by
  have h1 : u.ofLp ⬝ᵥ Δ.mulVec u.ofLp = ∑ i, ∑ j, u i * (Δ i j * u j) := by
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have h2 : ∑ i, ∑ j, u i * (Δ i j * u j) ≤ ∑ i, ∑ j, K * (|u i| * |u j|) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    calc u i * (Δ i j * u j) ≤ |u i * (Δ i j * u j)| := le_abs_self _
      _ = |u i| * (|Δ i j| * |u j|) := by rw [abs_mul, abs_mul]
      _ ≤ |u i| * (K * |u j|) := by gcongr; exact hΔ i j
      _ = K * (|u i| * |u j|) := by ring
  have h3 : ∑ i, ∑ j, K * (|u i| * |u j|) = K * (∑ i, |u i|) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have h4 : (∑ i, |u i|) ^ 2 ≤ q * ‖u‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |u i|)
    rw [EuclideanSpace.norm_sq_eq]
    simpa [Real.norm_eq_abs, sq_abs] using this
  calc u.ofLp ⬝ᵥ Δ.mulVec u.ofLp ≤ K * (∑ i, |u i|) ^ 2 := by rw [h1, ← h3]; exact h2
    _ ≤ K * (q * ‖u‖ ^ 2) := by gcongr
    _ = q * K * ‖u‖ ^ 2 := by ring

/-- The Gaussian tail integral. -/
def S7PIH_tail (q : ℕ) (R : ℝ) : ℝ :=
  ∫ z, Set.indicator {z : EuclideanSpace ℝ (Fin q) | R < ‖z‖} (fun z => ‖z‖ ^ 2) z
    ∂(stdGaussian (EuclideanSpace ℝ (Fin q)))

/-- The second moment of the standard Gaussian. -/
def S7PIH_V2 (q : ℕ) : ℝ := ∫ z, ‖z‖ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin q)))

theorem S7PIH_sq_integrable (q : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ (Fin q) => ‖z‖ ^ 2) (stdGaussian (EuclideanSpace ℝ (Fin q))) := by
  have := (IsGaussian.memLp_two_id (μ := stdGaussian (EuclideanSpace ℝ (Fin q)))).integrable_norm_pow
    (p := 2) (by norm_num)
  simpa using this

theorem S7PIH_tail_tendsto (q : ℕ) : Tendsto (S7PIH_tail q) atTop (𝓝 0) := by
  have := tendsto_integral_filter_of_dominated_convergence (μ := stdGaussian (EuclideanSpace ℝ (Fin q)))
    (l := (atTop : Filter ℝ))
    (F := fun (R : ℝ) (z : EuclideanSpace ℝ (Fin q)) =>
      Set.indicator {z : EuclideanSpace ℝ (Fin q) | R < ‖z‖} (fun z => ‖z‖ ^ 2) z)
    (f := fun _ => 0) (fun z => ‖z‖ ^ 2) ?_ ?_ (S7PIH_sq_integrable q) ?_
  · have h0 : (∫ _ : EuclideanSpace ℝ (Fin q), (0 : ℝ) ∂(stdGaussian (EuclideanSpace ℝ (Fin q)))) = 0 := by
      simp
    rw [h0] at this
    exact this
  · refine Filter.Eventually.of_forall fun R => ?_
    refine (continuous_pow 2 |>.comp continuous_norm).aestronglyMeasurable.indicator ?_
    exact measurableSet_lt measurable_const measurable_norm
  · refine Filter.Eventually.of_forall fun R => Filter.Eventually.of_forall fun z => ?_
    by_cases h : R < ‖z‖
    · simp [Set.indicator_of_mem (show z ∈ {z : EuclideanSpace ℝ (Fin q) | R < ‖z‖} from h)]
    · simp [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin q) | R < ‖z‖} from h)]
  · refine Filter.Eventually.of_forall fun z => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop ‖z‖] with R hR
    simp [Set.indicator_of_notMem (show z ∉ {z : EuclideanSpace ℝ (Fin q) | R < ‖z‖} from
      not_lt.2 hR.le)]

end HRS.MC.Sec7.S7PIH

end
