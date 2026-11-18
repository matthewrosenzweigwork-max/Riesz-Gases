import HRS.MS.Fp81S21GaussianWickPhysical
import HRS.MS.Fp81S21GaussianWickTime4

/-! The two integrated physical Wick identities, for arbitrary supplied chi.
All radii precede the selected source and preparation time. W1 and W2 are
literally the two equations in Skeleton.WickInput; no WickInput is assembled. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6
variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- The literal drift Wick equation for the retained physical D and Z. -/
def fp81s21_W1 (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (χ : Fin 3 → ℝ → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) : Prop :=
  ∀ i : Fin 3,
    (∫ ω, s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ i).2 (τ i)
        (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω) *
      fp81s21_cross37_X Q a τ φ hφ (i + 1) ω *
      fp81s21_cross37_X Q a τ φ hφ (i + 2) ω ∂Q.src.G0.P) =
    ∫ r in Icc (0 : ℝ) (a + τ i), ∫ x, ∫ y,
      commutatorKernel p.d p.s (gradient (fp81s21_wick_time_f R a τ φ i r)) x y *
        χ (i + 1) r x * χ (i + 2) r y

/-- The literal covariance Wick equation, with its single noise factor. -/
def fp81s21_W2 (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (χ : Fin 3 → ℝ → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) : Prop :=
  ∀ i : Fin 3,
    (∫ ω, fp81s21_cross37_X Q a τ φ hφ (i + 2) ω *
      (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
        TensorDual (Window p) 2)
        (HRS.MC.E213U18.mk2 (s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ i).2 (τ i))
          (s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ (i + 1)).2 (τ (i + 1))))
      ∂Q.src.G0.P) =
    (2 / p.β) * ∫ r in Icc (0 : ℝ) (min (a + τ i) (a + τ (i + 1))), ∫ x,
      inner ℝ (gradient (fp81s21_wick_time_f R a τ φ i r) x)
        (gradient (fp81s21_wick_time_f R a τ φ (i + 1) r) x) * χ (i + 2) r x

/-- W1 and W2 for arbitrary oscillator tests and arbitrary spatially agreeing
cross-densities, with the radius chosen before every physical realization. -/
theorem fp81s21_gaussian_wick_physical (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ), 0 ≤ a →
      ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
        (χ : Fin 3 → ℝ → Euc p.d → ℝ)
        (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
      fp81s21_W1 Q a τ φ χ hφ ∧ fp81s21_W2 Q a τ φ χ hφ := by
  obtain ⟨δA, hA, hhalf, hcoord⟩ := fp81s21_gaussian_wick_physical_coordinates p
  obtain ⟨δD, hD, _, hdom⟩ := fp81s21_gaussian_wick_time_dom p
  obtain ⟨δE, hE, _, horbit⟩ := fp81s21_moving_encoded_clamped_orbits p
  obtain ⟨δC, hC, _, hcross⟩ := fp81s21_gaussian_cross_density p
  obtain ⟨δS, hS, _, hspace⟩ := fp81s21_gaussian_wick_time_spatial_drift p
  refine ⟨min δA (min δD (min δE (min δC δS))),
    lt_min hA (lt_min hD (lt_min hE (lt_min hC hS))),
    (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q a ha τ φ χ hφ hχ
  have hl : δ ≤ δA ∧ δ ≤ δD ∧ δ ≤ δE ∧ δ ≤ δC ∧ δ ≤ δS := by
    simpa only [le_min_iff] using hδle
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  obtain ⟨hAD, hAJ⟩ := hcoord δ hδ hl.1 R Q a ha
  have hd := hdom δ hδ hl.2.1 R Q a ha τ φ hφ
  obtain ⟨hF, hB⟩ := horbit δ hδ hl.2.2.1 R Q.E a ha τ φ hφ
  have hc := hcross δ hδ hl.2.2.2.1 R Q a ha τ φ χ hφ hχ
  have hs := hspace δ hδ hl.2.2.2.2 R Q a ha τ φ χ hφ hχ
  have htH (i : Fin 3) : a + (τ i : ℝ) ≤ a + p.T :=
    by linarith [(τ i).property.2]
  constructor
  · intro i
    calc
      _ = ∫ ω, (∫ r in Icc (0 : ℝ) (a + τ i),
          fp81s21_wick_time_D Q a τ φ hφ i ω r) ∂Q.src.G0.P := by
        apply integral_congr_ae
        filter_upwards [hAD] with ω hω
        have he := (hω (τ i) (φ i) (hφ i)).2
        rw [min_eq_right (htH i)] at he
        simpa only [s21eObs_apply, fp81s21_wick_time_D, fp81s21_wick_time_f,
          integral_mul_const] using congrArg (fun x : ℝ =>
            x * fp81s21_cross37_X Q a τ φ hφ (i + 1) ω *
              fp81s21_cross37_X Q a τ φ hφ (i + 2) ω) he
      _ = ∫ r in Icc (0 : ℝ) (a + τ i), ∫ ω,
          fp81s21_wick_time_D Q a τ φ hφ i ω r ∂Q.src.G0.P :=
        integral_integral_swap (hd i).1
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hw := (hF i).2.1 r
        simp only [projIcc_of_mem _ hr] at hw
        simp only [fp81s21_wick_time_D]
        rw [fp81s21_wick_time_quadratic_pair Q a τ φ χ hφ hc (i + 1) (i + 2) r
          ⟨hr.1, hr.2.trans (htH i)⟩ (fp81s21_wick_time_f R a τ φ i r) hw]
        exact integral_prod (fun z : Euc p.d × Euc p.d =>
          commutatorKernel p.d p.s (gradient (fp81s21_wick_time_f R a τ φ i r))
            z.1 z.2 * χ (i + 1) r z.1 * χ (i + 2) r z.2)
          (by simpa only [fp81s21_wick_time_f, r26t3_coeff, Measure.volume_eq_prod]
            using hs i r hr)
  · intro i
    have htmin : min (a + (τ i : ℝ)) (a + (τ (i + 1) : ℝ)) ≤ a + p.T :=
      (min_le_left _ _).trans (htH i)
    have hν : 2 * (r26t3_coeff R).ν = 2 / p.β := by
      change 2 * p.β⁻¹ = 2 / p.β
      rw [div_eq_mul_inv]
    calc
      _ = (2 / p.β) * ∫ ω, (∫ r in
          Icc (0 : ℝ) (min (a + τ i) (a + τ (i + 1))),
          fp81s21_wick_time_J Q a τ φ hφ i ω r) ∂Q.src.G0.P := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [hAJ] with ω hω
        have he := (hω (τ i) (τ (i + 1)) (φ i) (φ (i + 1))
          (hφ i) (hφ (i + 1))).2
          (s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ i).2 (τ i))
          (s21eObs (wholeSpaceIndex p.d : ℝ) p.T (hφ (i + 1)).2 (τ (i + 1)))
          (s21eObs_apply _ _ _ _) (s21eObs_apply _ _ _ _)
        rw [min_eq_right htmin, hν] at he
        change _ * ((fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
          TensorDual (Window p) 2) _) = _
        simp only [HRS.MC.E213U18.mk2]
        rw [he]
        simp only [fp81s21_wick_time_J, fp81s21_wick_time_f, integral_mul_const]
        ring
      _ = (2 / p.β) * ∫ r in Icc (0 : ℝ) (min (a + τ i) (a + τ (i + 1))),
          ∫ ω, fp81s21_wick_time_J Q a τ φ hφ i ω r ∂Q.src.G0.P :=
        congrArg (fun x : ℝ => (2 / p.β) * x) (integral_integral_swap (hd i).2.2.1)
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hi : r ∈ Icc 0 (a + (τ i : ℝ)) := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
        have hj : r ∈ Icc 0 (a + (τ (i + 1) : ℝ)) := ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
        have hw := (hB i (i + 1)).2.1 r
        simp only [projIcc_of_mem _ hi, projIcc_of_mem _ hj] at hw
        exact fp81s21_wick_time_linear_pair Q a τ φ χ hφ hc (i + 2) r
          ⟨hr.1, hi.2.trans (htH i)⟩ _ hw

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_W1
#print axioms HRS.Fp81.S21.fp81s21_W2
#print axioms HRS.Fp81.S21.fp81s21_gaussian_wick_physical
end
