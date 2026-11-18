import HRS.MS.SA12X3C9G
import HRS.MS.QMul
import HRS.MS.QMulAux2
import HRS.MS.SA12X2R36Q1

/-!
# S.A.12 C10 (SA12X3), part A: the Fourier `H^m` norm versus the jet integrals

For `f ∈ C^m_c`: `‖f‖²_{H^m} ≤ 2^m J(f)` and `J(f) ≤ (m+1) ‖f‖²_{H^m}`, `J(f) = ∑_{n≤m} ∑_i ∫ (∂^i f)²`.
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd.Phase2SA12 HRS.MS.QMul HRS.MS.UlocMW HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- The raw jet energy `∑_{n≤m} ∑_i ∫ (∂^i f)²`. -/
def sa12x3_Jraw (m : ℕ) (f : Euc d → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (m + 1), ∑ i : Fin n → Fin d, ∫ x, (partialDeriv i f x) ^ 2

theorem sa12x3_sob_jet (m : ℕ) {f : Euc d → ℝ} (hf : ContDiff ℝ m f) (hc : HasCompactSupport f) :
    HRS.Whole.sobolevNormE (m : ℝ) f ^ 2 ≤ ENNReal.ofReal (2 ^ m * sa12x3_Jraw m f) ∧
      ENNReal.ofReal (sa12x3_Jraw m f) ≤ ENNReal.ofReal ((m : ℝ) + 1) * HRS.Whole.sobolevNormE (m : ℝ) f ^ 2 := by
  set g : Euc d → ℂ := fun x => ((f x : ℝ) : ℂ) with hg
  have hgC : ContDiff ℝ m g := Complex.ofRealCLM.contDiff.comp hf
  have hgc : HasCompactSupport g := hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hfc : Continuous f := hf.continuous
  have hfL2 : MemLp f 2 volume := hfc.memLp_of_hasCompactSupport hc
  have hgi : Integrable g := (Complex.ofRealCLM.continuous.comp hfc).integrable_of_hasCompactSupport hgc
  have hgL2 : MemLp g 2 volume := (Complex.ofRealCLM.continuous.comp hfc).memLp_of_hasCompactSupport hgc
  have hQ : QOk m g := by
    refine ⟨hgC, fun k hk => ?_⟩
    have hcont : Continuous (iteratedFDeriv ℝ k g) := hgC.continuous_iteratedFDeriv (by exact_mod_cast hk)
    have hcs : HasCompactSupport (iteratedFDeriv ℝ k g) := hgc.iteratedFDeriv (𝕜 := ℝ) k
    exact ⟨hcont.integrable_of_hasCompactSupport hcs, hcont.memLp_of_hasCompactSupport hcs⟩
  have hae : ∀ᵐ ξ ∂(volume : Measure (Euc d)), fourierL2 f ξ = 𝓕 g ξ := by
    have := qm_L1L2 hgi hgL2
    unfold fourierL2
    rw [dif_pos hfL2]
    exact this
  have hsob := um_sobE_sq hfL2 (m : ℝ)
  simp only [Real.rpow_natCast] at hsob
  have hsob' : HRS.Whole.sobolevNormE (m : ℝ) f ^ 2 = ∫⁻ ξ, ENNReal.ofReal (wt ξ ^ m * ‖𝓕 g ξ‖ ^ 2) := by
    rw [hsob]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ]
  have hpd : ∀ (n : ℕ) (i : Fin n → Fin d), n ≤ m → ∫⁻ x, ‖qm_pd i g x‖ₑ ^ 2 =
      ENNReal.ofReal (∫ x, (partialDeriv i f x) ^ 2) := by
    intro n i hn
    have hfn : ContDiff ℝ n f := hf.of_le (by exact_mod_cast hn)
    have hcpd : Continuous (partialDeriv i f) := (sa12x2_pd_cd (n := n) (k := 0) (by simpa using hfn) i).continuous
    have hcs : HasCompactSupport (partialDeriv i f) := sa12z3_pd_compact hc i
    have hint : Integrable (fun x => (partialDeriv i f x) ^ 2) :=
      Continuous.integrable_of_hasCompactSupport (f := fun x => (partialDeriv i f x) ^ 2) (hcpd.pow 2)
        (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    have hq : ∀ x, qm_pd i g x = ((partialDeriv i f x : ℝ) : ℂ) := by
      intro x
      have e : g = Complex.ofRealCLM ∘ f := rfl
      unfold qm_pd partialDeriv
      rw [e, ContinuousLinearMap.iteratedFDeriv_comp_left Complex.ofRealCLM hfn.contDiffAt le_rfl]
      simp
    simp_rw [hq, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => sq_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hJ : ENNReal.ofReal (sa12x3_Jraw m f) = ∑ n ∈ Finset.range (m + 1), ∑ i : Fin n → Fin d,
      ∫⁻ x, ‖qm_pd i g x‖ₑ ^ 2 := by
    unfold sa12x3_Jraw
    rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _)]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hnm : n ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg fun x => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => (hpd n i hnm).symm
  have hlow := qm_lower hQ
  have hup := qm_upper hQ
  rw [← hJ] at hlow hup
  refine ⟨?_, ?_⟩
  · rw [hsob']
    refine hlow.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp
  · rw [hsob']
    refine hup.trans (le_of_eq ?_)
    rw [show ((m : ℝ≥0∞) + 1) = ENNReal.ofReal ((m : ℝ) + 1) by
      rw [ENNReal.ofReal_add (by positivity) (by norm_num)]; simp]

end HRS.MH.AdjointRd.Phase2SA12Near
