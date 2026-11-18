import HRS.Commutator.Whole.XNRSAux22
import Mathlib.Analysis.Fourier.Convolution

/-!
# Packet X-NRS, part 23: the Fourier-localised approximants of a Schwartz function
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xσ_good {n : ℝ} (hn : 0 < n) : XGoodCut (xσ n : Euc d → ℝ) := xcut_good hn hn

/-- The cutoff `σ_n` as a Schwartz function. -/
def xSσ (n : ℝ) (hn : 0 < n) : 𝓢(Euc d, ℂ) :=
  xsch (xσ n : Euc d → ℝ) (xσ_good hn).smooth (xσ_good hn).cpt

lemma xσ_neg (n : ℝ) (ξ : Euc d) : xσ n (-ξ) = xσ n ξ := xcut_neg n n ξ

/-- The (Schwartz) kernel `G_n = 𝓕⁻ σ_n`. -/
def xGS (n : ℝ) (hn : 0 < n) : 𝓢(Euc d, ℂ) := 𝓕⁻ (xSσ n hn)

lemma xGS_apply (n : ℝ) (hn : 0 < n) (z : Euc d) :
    xGS n hn z = ((xKr (xσ n) z : ℝ) : ℂ) :=
  xinvF_even (xSσ n hn) (xσ n) (fun ξ => rfl) (xσ_neg n) z

/-- The Fourier-localised approximant, as a Schwartz function. -/
def xφn (φ : 𝓢(Euc d, ℂ)) (n : ℝ) (hn : 0 < n) : 𝓢(Euc d, ℂ) :=
  SchwartzMap.convolution (𝕜 := ℂ) (ContinuousLinearMap.mul ℂ ℂ) φ (xGS n hn)

lemma xφn_apply (φ : 𝓢(Euc d, ℂ)) (n : ℝ) (hn : 0 < n) (x : Euc d) :
    xφn φ n hn x = ∫ y, φ y * ((xKr (xσ n) (x - y) : ℝ) : ℂ) := by
  unfold xφn
  rw [SchwartzMap.convolution_apply, convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [xGS_apply]

lemma fourier_xφn (φ : 𝓢(Euc d, ℂ)) (n : ℝ) (hn : 0 < n) (ξ : Euc d) :
    𝓕 (xφn φ n hn) ξ = 𝓕 φ ξ * ((xσ n ξ : ℝ) : ℂ) := by
  have h : 𝓕 (xφn φ n hn) = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 φ) (𝓕 (xGS n hn)) :=
    SchwartzMap.fourier_convolution _ φ (xGS n hn)
  have h2 : (𝓕 (xGS n hn) : 𝓢(Euc d, ℂ)) = xSσ n hn := by
    unfold xGS; exact FourierTransform.fourier_fourierInv_eq _
  rw [h, SchwartzMap.pairing_apply_apply, h2]
  rfl

/-- The real approximant. -/
def xan (a : Euc d → ℝ) (n : ℝ) (x : Euc d) : ℝ := ∫ y, a y * xKr (xσ n) (x - y)

lemma xφn_real {a : Euc d → ℝ} {φ : 𝓢(Euc d, ℂ)} (ha : ∀ x, φ x = (a x : ℂ)) (n : ℝ) (hn : 0 < n)
    (x : Euc d) : xφn φ n hn x = ((xan a n x : ℝ) : ℂ) := by
  rw [xφn_apply, xan, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [ha y]

lemma xInD_xφn (φ : 𝓢(Euc d, ℂ)) {n : ℝ} (hn : 0 < n) : XInD (xρ n) (xφn φ n hn) := by
  intro ξ
  rw [fourier_xφn]
  have := xρ_mul_xσ hn ξ
  rw [mul_left_comm]
  have h2 : (((xρ n ξ : ℝ) : ℂ)) * ((xσ n ξ : ℝ) : ℂ) = ((xσ n ξ : ℝ) : ℂ) := by exact_mod_cast this
  rw [h2]

lemma xρ_good {n : ℝ} (hn : 0 < n) : XGoodCut (xρ n : Euc d → ℝ) :=
  xcut_good (by positivity) (by positivity)

end HRS.Commutator.Whole.XNRS
