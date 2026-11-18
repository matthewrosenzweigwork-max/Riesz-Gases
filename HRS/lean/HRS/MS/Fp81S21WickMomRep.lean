import HRS.MS.Fp81S21GaussMomRep2
import HRS.MS.Fp81S21WickFam7
import HRS.MS.Fp81S21WickFam16
import HRS.MS.Fp81S21WeightTrace2

/-! Jointly measurable moving half-Wick chart coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The supplied half-Wick operators admit jointly measurable strong-chart
coordinates. The Gaussian operator constant is selected before the realization
and time; the same event covers all chart coordinates at each fixed time. -/
theorem fp81s21_wick_strong_chart_coordinates (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ Kstar B : ℝ, ∃ hk : ∀ j, MemLp
          (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2) 2
          ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
        0 ≤ Kstar ∧ 0 ≤ B ∧
        Summable (fun j => ∫ xy : Euc p.d × Euc p.d,
          commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2 ^ 2
          ∂((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ))) ∧
        (∑' j, ∫ xy : Euc p.d × Euc p.d,
          commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2 ^ 2
          ∂((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ))) ≤ B ∧
        ∀ G : GaussianRealization R,
          ∃ T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P,
          ∃ W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
            (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P,
          ∃ q : ℝ → G.Ω → r26t6_Coeff,
            (∀ u : ℝ, 0 ≤ u → ∃ hL : ‖T u‖ ≤ Kstar,
              ∃ hJoint : ∀ r (v : Fin r → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
                HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
                W u = fp81s21_wickFam_operator R G (T u) Kstar hL hJoint) ∧
            (∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
              IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
              ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
              (T u (hφ.toLp φ) : G.Ω → ℝ) =ᵐ[G.P]
                fun ω => OscDual.eval (G.Z u ω) φ) ∧
            Measurable (Function.uncurry q) ∧
            ∀ u, 0 ≤ u → MemLp (q u) 2 G.P ∧
              (∫ ω, ‖q u ω‖ ^ 2 ∂G.P) ≤ Kstar ^ 4 * B / 2 ∧
              ∀ᵐ ω ∂G.P, ∀ j,
                q u ω j = (W u ((hk j).toLp
                  (fun xy : Euc p.d × Euc p.d =>
                    commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2)) : G.Ω → ℝ) ω := by
  obtain ⟨B, B', hB, hB', htrace⟩ := fp81s21_physical_reference_thermal_traces p
  obtain ⟨δ0, hδ0, hδhalf, hfamily⟩ := fp81s21_wickFam_supplied_linear_continuous p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨K, hK, hfamilyR⟩ := hfamily δ hδ hδle R
  let μ := HRS.Whole.withDensityReal R.ρβ
  have hker := (htrace δ R Es E).1.2
  let v : ℕ → Lp ℝ 2 (μ.prod μ) := fun j => (hker.1 j).toLp
    (fun xy : Euc p.d × Euc p.d => commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2)
  have hvnorm (j : ℕ) : ‖v j‖ ^ 2 = ∫ xy : Euc p.d × Euc p.d,
      commutatorKernel p.d p.s (gradient (Es.test j)) xy.1 xy.2 ^ 2 ∂(μ.prod μ) := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ((MemLp.coeFn_toLp (hker.1 j)).mono fun xy hxy => ?_)
    simp [v, hxy, sq]
  have hv : Summable (fun j => ‖v j‖ ^ 2) := by
    simpa only [hvnorm] using hker.2.1
  refine ⟨K, B, hker.1, hK, hB, hker.2.1, hker.2.2, ?_⟩
  intro G
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  obtain ⟨T, hgood, hc⟩ := hfamilyR G
  let hL (u : ℝ) := (hgood (max u 0) (le_max_right u 0)).choose
  let hJ (u : ℝ) := (hgood (max u 0) (le_max_right u 0)).choose_spec.choose
  let W := fun u : ℝ => fp81s21_wickFam_operator R G (T (max u 0)) K (hL u) (hJ u)
  have hW : ∀ u : ℝ, 0 ≤ u → ∃ hL : ‖T u‖ ≤ K,
      ∃ hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
        HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
        W u = fp81s21_wickFam_operator R G (T u) K hL hJoint := by
    intro u hu
    refine ⟨(hgood u hu).choose, (hgood u hu).choose_spec.choose, ?_⟩
    simp only [W, max_eq_left hu]
  have hag : ∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
      IsOscTest (wholeSpaceIndex p.d : ℝ) φ → ∀ hφ : MemLp φ 2 μ,
      (T u (hφ.toLp φ) : G.Ω → ℝ) =ᵐ[G.P] fun ω => OscDual.eval (G.Z u ω) φ := by
    intro u hu
    exact (hgood u hu).choose_spec.choose_spec.1
  have hcont := fp81s21_wickFam_supplied_wick_continuous_joint p R K G T W hW hag hc
  have hn : ∀ u, 0 ≤ u → ‖W u‖ ≤ K ^ 2 / Real.sqrt 2 := by
    intro u hu
    obtain ⟨hL', hJ', hWu⟩ := hW u hu
    rw [hWu]
    exact fp81s21_wickB311_operator_norm (T u) K hL' hJ'
  have hkn : 0 ≤ K ^ 2 / Real.sqrt 2 := div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  obtain ⟨q, hq, hsec⟩ := fp81s21_operator_coeff_field (μ.prod μ) G.P W
    (K ^ 2 / Real.sqrt 2) hkn hn (fun k => (hcont k).1) v hv
  refine ⟨T, W, q, hW, hag, hq, ?_⟩
  intro u hu
  obtain ⟨hmem, hmom, hcoords⟩ := hsec u hu
  refine ⟨hmem, ?_, ?_⟩
  · have hs : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have heq : (K ^ 2 / Real.sqrt 2) ^ 2 = K ^ 4 / 2 := by
      rw [div_pow, hs]
      ring
    rw [heq] at hmom
    calc
      _ ≤ K ^ 4 / 2 * ∑' j, ‖v j‖ ^ 2 := hmom
      _ ≤ K ^ 4 / 2 * B := mul_le_mul_of_nonneg_left (by simpa only [hvnorm] using hker.2.2)
        (div_nonneg (pow_nonneg hK 4) (by norm_num))
      _ = K ^ 4 * B / 2 := by ring
  · exact hcoords

#print axioms fp81s21_wick_strong_chart_coordinates
end HRS.Fp81.S21
end
