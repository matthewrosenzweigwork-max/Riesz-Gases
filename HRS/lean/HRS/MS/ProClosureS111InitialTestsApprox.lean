import HRS.MS.S111X1Aux6
import HRS.MS.MovOscAux5
import HRS.MS.CovMeasAux22
import HRS.MS.GenPathAux47

/-!
Hermite sections for the initial source. The approximation is in the
original oscillator norm. In particular every fixed continuous oscillator
functional converges, without any spatial measurability assumption on a
family of such functionals.
-/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.S111X1 HRS.MS.MovOsc

variable {d : ℕ} {m : ℝ}

def initialTestBasis (m : ℝ) (alpha : MultiIndex d) : oscSub d m :=
  ⟨oscTestFun m alpha, HRS.MS.GenPath.s56_isOscTest m alpha⟩

def initialTestSection (phi : oscSub d m) (n : ℕ) : oscSub d m :=
  ∑ alpha ∈ mova2_S d n,
    (oscEigenvalue d alpha ^ (m / 2) * HRS.Whole.hermiteCoeff phi alpha) •
      initialTestBasis m alpha

theorem initialTestSection_apply (phi : oscSub d m) (n : ℕ) (x : Euc d) :
    (initialTestSection phi n : Euc d → ℝ) x =
      ∑ alpha ∈ mova2_S d n,
        (oscEigenvalue d alpha ^ (m / 2) * HRS.Whole.hermiteCoeff phi alpha) *
          oscTestFun m alpha x := by
  simp [initialTestSection, initialTestBasis]

theorem initialTestSection_coe (phi : oscSub d m) (n : ℕ) :
    (initialTestSection phi n : Euc d → ℝ) = mo_pSum phi n := by
  funext x
  rw [initialTestSection_apply]
  unfold mo_pSum mo_hsum
  refine Finset.sum_congr rfl fun alpha _ => ?_
  have hc := rpow_neg_half_mul m (oscEigenvalue d alpha) (oscEv_pos alpha)
  unfold oscTestFun
  calc
    _ = (oscEigenvalue d alpha ^ (-(m / 2)) *
        oscEigenvalue d alpha ^ (m / 2)) *
        HRS.Whole.hermiteCoeff phi alpha * hermiteFunD alpha x := by ring
    _ = _ := by rw [hc, one_mul]

theorem initialTestSection_tail (phi : oscSub d m) :
    Tendsto (fun n => oscNorm m ((phi - initialTestSection phi n : oscSub d m) :
      Euc d → ℝ)) atTop (𝓝 0) := by
  change Tendsto (fun n => oscNorm m
    (fun x => (phi : Euc d → ℝ) x - (initialTestSection phi n : Euc d → ℝ) x))
      atTop (𝓝 0)
  simpa only [initialTestSection_coe] using mo_hsum_tail m phi.property.2

theorem initialTest_ofFun_sub (phi psi : oscSub d m) :
    OscSpace.ofFun m ((phi - psi : oscSub d m) : Euc d → ℝ) =
      OscSpace.ofFun m (phi : Euc d → ℝ) - OscSpace.ofFun m (psi : Euc d → ℝ) := by
  apply lp.ext
  funext alpha
  change OscSpace.coord (OscSpace.ofFun m ((phi - psi : oscSub d m) : Euc d → ℝ)) alpha =
    OscSpace.coord (OscSpace.ofFun m (phi : Euc d → ℝ) -
      OscSpace.ofFun m (psi : Euc d → ℝ)) alpha
  have hsub : OscSpace.coord (OscSpace.ofFun m (phi : Euc d → ℝ) -
      OscSpace.ofFun m (psi : Euc d → ℝ)) alpha =
      OscSpace.coord (OscSpace.ofFun m (phi : Euc d → ℝ)) alpha -
        OscSpace.coord (OscSpace.ofFun m (psi : Euc d → ℝ)) alpha := by
    rfl
  rw [hsub, OscSpace.coord_ofFun_eq (phi - psi).property.2,
    OscSpace.coord_ofFun_eq phi.property.2, OscSpace.coord_ofFun_eq psi.property.2]
  change oscEigenvalue d alpha ^ (m / 2) *
      HRS.Whole.hermiteCoeff (fun x => (phi : Euc d → ℝ) x - (psi : Euc d → ℝ) x) alpha = _
  rw [mova2_coeff_sub phi.property.2.1 psi.property.2.1]
  ring

theorem initialTestSection_eval_tendsto (phi : oscSub d m) (z : OscDual d m) :
    Tendsto (fun n => OscDual.eval z (initialTestSection phi n : Euc d → ℝ))
      atTop (𝓝 (OscDual.eval z (phi : Euc d → ℝ))) := by
  have hlim : Tendsto
      (fun n => OscSpace.ofFun m (initialTestSection phi n : Euc d → ℝ))
      atTop (𝓝 (OscSpace.ofFun m (phi : Euc d → ℝ))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have heq : ∀ n,
        ‖OscSpace.ofFun m (initialTestSection phi n : Euc d → ℝ) -
          OscSpace.ofFun m (phi : Euc d → ℝ)‖ =
        oscNorm m ((phi - initialTestSection phi n : oscSub d m) : Euc d → ℝ) := by
      intro n
      rw [norm_sub_rev, ← initialTest_ofFun_sub,
        OscSpace.norm_ofFun _ (phi - initialTestSection phi n).property.2]
    simpa only [heq] using initialTestSection_tail phi
  have ht := ((OscDual.toDual z).continuous.tendsto
    (OscSpace.ofFun m (phi : Euc d → ℝ))).comp hlim
  have ht' : Tendsto (fun n => OscDual.toDual z
      (OscSpace.ofFun m (initialTestSection phi n : Euc d → ℝ))) atTop
      (𝓝 (OscDual.toDual z (OscSpace.ofFun m (phi : Euc d → ℝ)))) := by
    convert ht using 1 <;> rfl
  have heval : ∀ n, OscDual.toDual z
      (OscSpace.ofFun m (initialTestSection phi n : Euc d → ℝ)) =
      OscDual.eval z (initialTestSection phi n : Euc d → ℝ) :=
    fun n => OscDual.toDual_ofFun z _ (initialTestSection phi n).property.2
  simpa only [OscDual.toDual_ofFun z _ phi.property.2, heval] using ht'

theorem initialTestSection_eval (phi : oscSub d m) (n : ℕ) (z : OscDual d m) :
    OscDual.eval z (initialTestSection phi n : Euc d → ℝ) =
      ∑ alpha ∈ mova2_S d n,
        (oscEigenvalue d alpha ^ (m / 2) * HRS.Whole.hermiteCoeff phi alpha) *
          OscDual.coord z alpha := by
  have heq : (initialTestSection phi n : Euc d → ℝ) =
      fun x => ∑ alpha ∈ mova2_S d n,
        (oscEigenvalue d alpha ^ (m / 2) * HRS.Whole.hermiteCoeff phi alpha) *
          oscTestFun m alpha x := funext (initialTestSection_apply phi n)
  rw [heq]
  exact HRS.MS.CovMeas.s101_eval_combo z _ _

/-- The original oscillator norm controls the input square integral for any
bounded nonnegative reference density. -/
theorem initialTest_sq_bound {rho : Euc d → ℝ} (hrho : Measurable rho)
    (h0 : ∀ x, 0 ≤ rho x) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ x, rho x ≤ M)
    (hm : 0 ≤ m) (phi : oscSub d m) :
    (∫ x, (phi : Euc d → ℝ) x ^ 2 ∂HRS.Whole.withDensityReal rho) ≤
      M * oscNorm m (phi : Euc d → ℝ) ^ 2 := by
  have hs : Integrable (fun x => (phi : Euc d → ℝ) x ^ 2) :=
    phi.property.2.1.integrable_sq
  have hms : Integrable (fun x => M * (phi : Euc d → ℝ) x ^ 2) := hs.const_mul M
  have hrhos : Integrable (fun x => rho x * (phi : Euc d → ℝ) x ^ 2) := by
    refine hms.mono'
      (hrho.mul (phi.property.1.continuous.measurable.pow_const 2)).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (mul_nonneg (h0 x) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (hM x) (sq_nonneg _)
  have hsq : (∫ x, (phi : Euc d → ℝ) x ^ 2) ≤ oscNorm m (phi : Euc d → ℝ) ^ 2 := by
    have heq : oscNorm 0 (phi : Euc d → ℝ) ^ 2 =
        ∫ x, (phi : Euc d → ℝ) x ^ 2 := by
      rw [oscNorm_zero _ phi.property.2.1]
      exact Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)
    rw [← heq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
      (mo_mono hm phi.property.2).2 2
  calc
    _ = ∫ x, rho x * (phi : Euc d → ℝ) x ^ 2 :=
      HRS.MS.Gap.gap1_integral_wdr hrho h0 _
    _ ≤ ∫ x, M * (phi : Euc d → ℝ) x ^ 2 :=
      integral_mono hrhos hms (fun x =>
        mul_le_mul_of_nonneg_right (hM x) (sq_nonneg _))
    _ = M * ∫ x, (phi : Euc d → ℝ) x ^ 2 := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hM0

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.initialTestSection_eval_tendsto
#print axioms HRS.MS.ProClosureS111.initialTest_sq_bound
