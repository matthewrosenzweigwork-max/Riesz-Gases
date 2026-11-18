import HRS.MS.Fp81S21GaussianFeatureBound

/-! A uniform thermal L² bound for the literal combined feature on classical data. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- The constant precedes the response representation, time, and classical terminal data. -/
theorem fp81s21_combinedFeature_classical_bound (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      letI := fp81s21_initialMeasure_isProbability p R
      ∃ B : ℝ, 0 ≤ B ∧
        ∀ (Mg : ℝ)
          (K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0))
          (hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg),
        ∀ r : ℝ, 0 ≤ r → ∀ (g : Euc p.d → ℝ) (u : ℝ → Euc p.d → ℝ),
          IsClassicalAdjointW (r26t3_coeff R) r g u →
          ‖fp81s21_combinedFeature p R hK r g‖ ^ 2 ≤
            B * ∫ x, g x ^ 2 ∂(HRS.Whole.withDensityReal R.ρβ) := by
  obtain ⟨δ₀, Q, C, c, hδ₀, hδ₀h, hQ, hQδ, hC, hc, henergy⟩ :=
    sol13_uniform_adjoint_energy p
  refine ⟨δ₀, hδ₀, hδ₀h, ?_⟩
  intro δ hδ hδle R
  letI := fp81s21_initialMeasure_isProbability p R
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  obtain ⟨cE, CE, hcE, hCE, hE⟩ := r26t3_energy_bounds R
  obtain ⟨-, hC₁, -, -⟩ := r26t3_reference_data p δ hδ (hδle.trans hδ₀h) R
  let D := max C 1
  have hD : 0 ≤ D := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_right _ _)
  let B := p.C₁ * (D + 2 * p.β⁻¹ * CE)
  have hβ : 0 ≤ 2 * p.β⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)
  have hB : 0 ≤ B := mul_nonneg hC₁.le (add_nonneg hD (mul_nonneg hβ hCE.le))
  refine ⟨B, hB, ?_⟩
  intro Mg K hK r hr g u hu
  have hu₀ : MemLp (u 0) 2 μ := HRS.MS.S111X1.x1_classical_memLp hu ⟨le_rfl, hr⟩ μ
  have hg : MemLp g 2 μ := by
    simpa only [hu.terminal] using
      (HRS.MS.S111X1.x1_classical_memLp hu ⟨hr, le_rfl⟩ μ)
  have hv : 0 ≤ s111x2_centeredSquare μ g := integral_nonneg fun x => sq_nonneg _
  have hv₀ : 0 ≤ s111x2_centeredSquare μ (u 0) := integral_nonneg fun x => sq_nonneg _
  have hvraw : s111x2_centeredSquare μ g ≤ ∫ x, g x ^ 2 ∂μ := s21f_centered_le μ hg
  have hclassical :
      s111x2_centeredSquare μ (u 0) ≤ D * s111x2_centeredSquare μ g ∧
      (∫ s in Icc (0 : ℝ) r, ∫ x, ‖gradient (u s) x‖ ^ 2 ∂μ) ≤
        CE * s111x2_centeredSquare μ g := by
    by_cases hz : r = 0
    · subst r
      constructor
      · rw [hu.terminal]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_right C 1) hv
      · simpa using mul_nonneg hCE.le hv
    · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
      obtain ⟨-, -, -, hbudget⟩ := henergy δ hδ hδle R r hrp g u hu
      obtain ⟨hb, hd⟩ := hbudget 0 ⟨le_rfl, hr⟩
      have hexp : Real.exp (-c * (r - 0)) ≤ 1 := by
        apply Real.exp_le_one_iff.2
        nlinarith [mul_nonneg hc.le hr]
      have hcoef : C * Real.exp (-c * (r - 0)) ≤ D :=
        (mul_le_mul_of_nonneg_left hexp hC.le).trans (by simpa [D] using le_max_left C 1)
      have hlow : 0 ≤ r26t3_energy R (u 0) :=
        (mul_nonneg hcE.le hv₀).trans (hE (u 0) hu₀).1
      refine ⟨?_, ?_⟩
      · exact hd.trans (mul_le_mul_of_nonneg_right hcoef hv)
      · have hupper := (hE g hg).2
        change r26t3_energy R (u 0) +
          (∫ s in Icc (0 : ℝ) r, ∫ x, ‖gradient (u s) x‖ ^ 2 ∂μ) ≤
            r26t3_energy R g at hb
        change r26t3_energy R g ≤ CE * s111x2_centeredSquare μ g at hupper
        linarith
  have hprop := fp81s21_feature_classical_eq p R hr hu 0 ⟨le_rfl, hr⟩
  have hu₀init := HRS.MS.S111X1.x1_classical_memLp hu ⟨le_rfl, hr⟩ (r26t3_mu R 0)
  have hdom : r26t3_mu R 0 ≤ ENNReal.ofReal p.C₁ • μ :=
    fp81s21_feature_measure_domination hC₁.le R.thermal.1.1.measurable
      (fun x => (R.resulting.ratio 0 le_rfl x).2)
  have hvar := fp81s21_feature_variance_domination hC₁.le hdom hu₀init hu₀
  have hinit : ‖fp81s21_initialGaussianFeature p R hK r g‖ ^ 2 ≤
      p.C₁ * D * s111x2_centeredSquare μ g := by
    have hn := HRS.MS.ProClosureS111.responseSqrt_norm_le hK.posOp p.hγ
      (HRS.Whole.Q34.Pc (r26t3_mu R 0) (s111x2_toLp (r26t3_mu R 0) (u 0)))
    have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
    rw [← s111x2_cl_eq_Pc hu₀init, s111x2_cl_norm_sq] at hs
    change ‖HRS.MS.ProClosureS111.responseSqrt hK.posOp p.hγ
      (HRS.Whole.Q34.Pc (r26t3_mu R 0) (s111x2_toLp (r26t3_mu R 0)
        (propagatorW (r26t3_coeff R) 0 r g)))‖ ^ 2 ≤ _
    rw [hprop]
    simpa only [s111x2_cl_eq_Pc, mul_assoc] using
      hs.trans (hvar.trans (mul_le_mul_of_nonneg_left hclassical.1 hC₁.le))
  have hnoise := (fp81s21_feature_classical_noise p R hδ (hδle.trans hδ₀h) hr hu).2
  have hn : ‖movingNoiseFeature R 0 r g‖ ^ 2 ≤
      (2 * p.β⁻¹ * p.C₁) * (CE * s111x2_centeredSquare μ g) :=
    hnoise.trans (mul_le_mul_of_nonneg_left hclassical.2 (mul_nonneg hβ hC₁.le))
  have hpair : ‖fp81s21_combinedFeature p R hK r g‖ ^ 2 =
      ‖fp81s21_initialGaussianFeature p R hK r g‖ ^ 2 +
        ‖movingNoiseFeature R 0 r g‖ ^ 2 := by
    simpa only [fp81s21_combinedFeature, WithLp.ofLp_toLp,
      real_inner_self_eq_norm_sq] using
      (WithLp.prod_inner_apply (𝕜 := ℝ)
        (fp81s21_combinedFeature p R hK r g) (fp81s21_combinedFeature p R hK r g))
  calc
    _ = _ := hpair
    _ ≤ p.C₁ * D * s111x2_centeredSquare μ g +
        (2 * p.β⁻¹ * p.C₁) * (CE * s111x2_centeredSquare μ g) := add_le_add hinit hn
    _ = B * s111x2_centeredSquare μ g := by dsimp [B]; ring
    _ ≤ B * ∫ x, g x ^ 2 ∂μ := mul_le_mul_of_nonneg_left hvraw hB

#print axioms fp81s21_combinedFeature_classical_bound
end HRS.Fp81.S21
end
