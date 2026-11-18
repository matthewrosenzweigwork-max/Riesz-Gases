import HRS.MS.Fp81S21FutureIndep6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- Past noise feature vectors: zero almost everywhere strictly after the cutoff. -/
def fp81s21_PastNoiseFeatures (d : ℕ) (r : ℝ) : Set (MovingNoiseHilbert d) :=
  {f | ∀ᵐ q ∂((volume : Measure ℝ).prod (volume : Measure (Euc d))),
    r < q.1 → f q = 0}

/-- Future noise feature vectors: zero almost everywhere through the cutoff. -/
def fp81s21_FutureNoiseFeatures (d : ℕ) (r : ℝ) : Set (MovingNoiseHilbert d) :=
  {f | ∀ᵐ q ∂((volume : Measure ℝ).prod (volume : Measure (Euc d))),
    q.1 ≤ r → f q = 0}

/-- The complete initial-and-past noise source is independent of the complete
future noise source. In particular this covers all supported noise features,
not only the features attached to a chosen countable list of tests. -/
theorem fp81s21_supported_source_families_independent
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (r : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h)) (hW2 : ∀ h, MemLp (W h) 2 P)
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    (hcov : ∀ h h', ∫ ω, W h ω * W h' ω ∂P = inner ℝ h h') :
    IndepFun
      (fun ω (i : Lp ℝ 2 (r26t3_mu R 0) × fp81s21_PastNoiseFeatures p.d r) =>
        W (J (WithLp.toLp 2 (i.1, i.2.1))) ω)
      (fun ω (j : fp81s21_FutureNoiseFeatures p.d r) =>
        W (J (WithLp.toLp 2 (0, j.1))) ω) P := by
  apply fp81s21_source_indep_of_orthogonal P W hWm hW2 hcomb hcov
  intro i j
  rw [J.inner_map_map]
  have hz : inner ℝ i.2.1 j.1 = 0 := by
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [i.2.2, j.2] with q hi hj
    by_cases hq : q.1 ≤ r
    · simp [hj hq]
    · simp [hi (lt_of_not_ge hq)]
  have hpair := WithLp.prod_inner_apply (𝕜 := ℝ)
    (WithLp.toLp 2 (i.1, i.2.1) : Fp81S21GaussFeatureHilbert p R)
    (WithLp.toLp 2 (0, j.1) : Fp81S21GaussFeatureHilbert p R)
  simpa [hz] using hpair

#print axioms fp81s21_supported_source_families_independent

end HRS.Fp81.S21
end
