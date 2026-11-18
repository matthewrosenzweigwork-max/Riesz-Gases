import HRS.MS.MovAdjTie
import HRS.MS.R26T8AF09
import HRS.MS.R26T8AF12
import HRS.MS.R26T8AF13b

/-!
# S8.2 observed-time layer, packet T8A.F13: native S6.7 at the exact feature index

The stationary global adjoint decay (native `mov_global_adjoint_stationary`, proof `MovAdj.mov_global_adjoint_stationary_proof`)
is applied at the unique thermal density `ρ₀` (`s85_thermal_eq`), so its constants are independent of `rho`.
The terminal data `LIter j f` (F09) and the adjoint witness of F11 give the gradient jets of `u 0 = propagatorW 0 v (LIter j f)`;
F13b turns them into pointwise bounds of all derivatives of order `1 ≤ k ≤ testOrder d`, and the projection constant
does not affect positive derivatives.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

variable {d : ℕ}

/-- integral against the density measure `ρ dx` -/
theorem r26t8a_f13_wd_integral (ρ : Euc d → ℝ) (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (h : Euc d → ℝ) :
    ∫ y, h y ∂(HRS.Whole.withDensityReal ρ) = ∫ y, h y * ρ y := by
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρm).aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [ENNReal.toReal_ofReal (hρ0 y), smul_eq_mul]
  ring

/-- the projected mean at the density `ρ dx` -/
theorem r26t8a_f13_proj_apply (ρ : Euc d → ℝ) (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (h : Euc d → ℝ)
    (x : Euc d) :
    HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) h x = h x - ∫ y, h y * ρ y := by
  simp only [HRS.Whole.projMean, HRS.Whole.pair]
  rw [r26t8a_f13_wd_integral ρ hρm hρ0 h]

/-- shifting by a constant does not change derivatives of positive order -/
theorem r26t8a_f13_shift_norm (g : Euc d → ℝ) (c0 : ℝ) (j : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ (j + 1) (fun y => g y - c0) x‖ = ‖iteratedFDeriv ℝ (j + 1) g x‖ := by
  have hfd : fderiv ℝ (fun y => g y - c0) = fderiv ℝ g := funext fun y => fderiv_sub_const c0
  rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y => g y - c0) (x := x) (n := j),
    ← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := g) (x := x) (n := j), hfd]

/-- a constant shift of a function with pointwise derivative bounds has the same `TestBound` -/
theorem r26t8a_f13_tb (k : ℕ) (A : ℝ) (g : Euc d → ℝ) (c0 : ℝ) (hg : ContDiff ℝ ∞ g)
    (hb : ∀ j : ℕ, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ A) :
    TestBound k A (fun y => g y - c0) := by
  refine ⟨hg.sub contDiff_const, fun j hj1 hjk x => ?_⟩
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [r26t8a_f13_shift_norm]
  exact hb (j' + 1) hj1 hjk x

theorem r26t8a_feature_decay_exact (d : ℕ) (hd : 2 ≤ d) (a beta m : ℝ) (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho → ∀ alpha : MultiIndex d, ∀ v : ℝ, 0 ≤ v →
      ∀ j : ℕ, j ≤ 2 → TestBound (testOrder d)
        (C * HRS.MS.S82BD.s82Weight d m alpha * Real.exp (-c * v))
        (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
          (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v
            (oscTestFun m alpha))) := by
  have hd1 : 1 ≤ d := by omega
  have hs0' : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd' : criticalS d < d := HRS.MS.S82R.s82r_criticalS_lt hd1
  by_cases hex : ∃ ρ, IsThermalEquilibrium d (criticalS d) a beta ρ
  swap
  · refine ⟨0, 1, le_rfl, one_pos, fun rho hrho => (hex ⟨rho, hrho⟩).elim⟩
  -- the unique thermal density, its Schwartz class and the native S6.7 constants
  obtain ⟨ρ₀, hρ₀eq, hρ₀, hS⟩ : ∃ ρ₀ : Euc d → ℝ,
      (∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho → rho = ρ₀) ∧
      IsThermalEquilibrium d (criticalS d) a beta ρ₀ ∧ IsSchwartzDensity ρ₀ := by
    obtain ⟨r, hr⟩ := hex
    exact ⟨thermalDensity d (criticalS d) a beta,
      fun rho h => (HRS.MS.S85.s85_thermal_eq hd hs0' hsd' ha hbeta h).1,
      (HRS.MS.S85.s85_thermal_eq hd hs0' hsd' ha hbeta hr).2,
      HRS.MS.S85.s85_thermal_schwartz hd hs0' hsd' ha hbeta⟩
  have hρm : Measurable ρ₀ := by
    obtain ⟨ψ, hψ⟩ := hS.2
    rw [← hψ]
    exact ψ.continuous.measurable
  have hρ0 : ∀ x, 0 ≤ ρ₀ x := hS.1.nonneg
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = testOrder d - 1 := ⟨_, rfl⟩
  have hK8 : K = 8 * d + 79 := by
    rw [hK]
    unfold testOrder
    omega
  have hKe : K + 1 = testOrder d := by
    rw [hK8]
    unfold testOrder
    omega
  have hq : d ≤ 2 * ((d + 1) / 2) := by omega
  have hqR : (d : ℝ) ≤ 2 * (((d + 1) / 2 : ℕ) : ℝ) := by exact_mod_cast hq
  have hMlt : (d : ℝ) / 2 + (K : ℝ) + 5 < ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) := by
    rw [hK8]
    unfold HRS.MS.S82BD.s82FeatureOrder
    push_cast
    linarith
  obtain ⟨C6, c6, hc6, hS67⟩ := HRS.MS.MovAdj.mov_global_adjoint_stationary_proof (d := d)
    (s := criticalS d) hd hs0'.le hsd' beta a hbeta ha ρ₀ hρ₀ K (HRS.MS.S82BD.s82FeatureOrder d) hMlt
  obtain ⟨C09, hC09, h09⟩ := r26t8a_feature_terminal_data d hd a beta ha hbeta ρ₀ hρ₀
  refine ⟨|C6| * C09, c6, mul_nonneg (abs_nonneg _) hC09, hc6, ?_⟩
  intro rho hrho alpha v hv j hj
  rw [hρ₀eq rho hrho]
  obtain ⟨f, hf, hW⟩ := r26t8a_feature_weight d m alpha
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    rw [← hW]
    unfold oscNorm
    exact Real.sqrt_nonneg _
  obtain ⟨-, -, -, -, hgen⟩ := r26t8a_projected_orbit_regularity d hd a beta m ha hbeta ρ₀ hρ₀
  obtain ⟨F, hF1, hF2, -, hF4, -⟩ := r26t8a_four_orbits d hd a beta ha hbeta ρ₀ hρ₀ f
  have hj4 : j < 4 := by omega
  obtain ⟨u, hu, hFu⟩ := hF2 ⟨j, hj4⟩ v hv
  have hu0 : ContDiff ℝ ∞ (u 0) := by
    rw [← hFu]
    exact hF4 ⟨j, hj4⟩ v hv
  have hh : propagatorW (critCoeff d a beta ρ₀) 0 v (r26t8a_LIter a beta ρ₀ j f) = u 0 :=
    (hF1 ⟨j, hj4⟩ v hv).symm.trans hFu
  -- the terminal datum `φ = L^j f` and the Schwartz-data bounds
  have hCK : ContDiff ℝ ((K : WithTop ℕ∞) + 1) (r26t8a_LIter a beta ρ₀ j f) := by
    have h9 := (h09 f j hj).1
    rw [← hKe] at h9
    exact_mod_cast h9
  have hproj : ∀ (h : Euc d → ℝ) (x : Euc d),
      HRS.Whole.projMean (HRS.Whole.withDensityReal ρ₀) h x = h x - ∫ y, h y * ρ₀ y :=
    fun h x => r26t8a_f13_proj_apply ρ₀ hρm hρ0 h x
  have hM1 : MemOsc ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ)
      (fun x => Real.sqrt (ρ₀ x) * (r26t8a_LIter a beta ρ₀ j f x - ∫ y, r26t8a_LIter a beta ρ₀ j f y * ρ₀ y)) := by
    have h9 := (h09 f j hj).2.1
    simp only [hproj] at h9
    exact h9
  have hEsum : cbNormVecE K (fun x => gradient (r26t8a_LIter a beta ρ₀ j f) x) +
      ENNReal.ofReal (oscNorm ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ)
        (fun x => Real.sqrt (ρ₀ x) * (r26t8a_LIter a beta ρ₀ j f x - ∫ y, r26t8a_LIter a beta ρ₀ j f y * ρ₀ y))) ≤
      ENNReal.ofReal (C09 * HRS.MS.S82BD.s82Weight d m alpha) := by
    have h9 := (h09 f j hj).2.2
    simp only [hproj] at h9
    rw [← hK, hW] at h9
    exact h9
  -- S6.7 at time `v`, read at `r = 0`
  have h6 := hS67 v (r26t8a_LIter a beta ρ₀ j f) u hv hu hCK hM1 0 ⟨le_rfl, hv⟩
  simp only [sub_zero] at h6
  have hbd : cbNormVecE K (fun x => gradient (u 0) x) ≤
      ENNReal.ofReal (|C6| * C09 * HRS.MS.S82BD.s82Weight d m alpha * Real.exp (-c6 * v)) := by
    calc cbNormVecE K (fun x => gradient (u 0) x)
        ≤ ENNReal.ofReal (C6 * Real.exp (-c6 * v)) *
            (cbNormVecE K (fun x => gradient (r26t8a_LIter a beta ρ₀ j f) x) +
              ENNReal.ofReal (oscNorm ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ)
                (fun x => Real.sqrt (ρ₀ x) * (r26t8a_LIter a beta ρ₀ j f x -
                  ∫ y, r26t8a_LIter a beta ρ₀ j f y * ρ₀ y)))) := h6.2
      _ ≤ ENNReal.ofReal (|C6| * Real.exp (-c6 * v)) * ENNReal.ofReal (C09 * HRS.MS.S82BD.s82Weight d m alpha) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_nonneg _))) hEsum
      _ = ENNReal.ofReal (|C6| * Real.exp (-c6 * v) * (C09 * HRS.MS.S82BD.s82Weight d m alpha)) :=
          (ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) (Real.exp_nonneg _))).symm
      _ = ENNReal.ofReal (|C6| * C09 * HRS.MS.S82BD.s82Weight d m alpha * Real.exp (-c6 * v)) := by
          congr 1
          ring
  -- the orbit identity and the pointwise bounds
  have hgen' := hgen alpha j hj v hv
  rw [← hf] at hgen' ⊢
  rw [hgen', hh]
  have hX0 : 0 ≤ |C6| * C09 * HRS.MS.S82BD.s82Weight d m alpha * Real.exp (-c6 * v) :=
    mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hC09) hW0) (Real.exp_nonneg _)
  refine r26t8a_f13_tb (testOrder d) _ (u 0) (HRS.Whole.pair (HRS.Whole.withDensityReal ρ₀) (u 0)) hu0
    (fun k hk1 hkk x => ?_)
  have hkK : k ≤ K + 1 := by omega
  exact r26t8a_f13b_bound (u 0) hu0 K _ hX0 hbd k hk1 hkK x

end HRS.MS.R26T8A
