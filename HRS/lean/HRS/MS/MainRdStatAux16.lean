import HRS.MS.MainRdStatAux15

/-!
# SA2, packet 8c: the per-`N` `W₁` and `W₂` bounds with the rate `rdRate`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

/-- the real arithmetic of the Wasserstein rate -/
theorem sa2_arith_wass {Bs c0 Cy Ct T ε q σ E w : ℝ} (hBs : 0 ≤ Bs) (hc0 : 0 ≤ c0) (hCy : 0 ≤ Cy)
    (hCt : 0 ≤ Ct) (hT : 0 ≤ T) (hε : 0 ≤ ε) (hq0 : 0 ≤ q) (hσ : 0 ≤ σ) (hE : 0 ≤ E) (hw : 0 ≤ w) :
    ε * (Cy * Bs) + Real.sqrt (2 * q * Ct * Bs ^ 2 * T * w) + σ * c0 * Bs * (E * T) ≤
      (Cy + Real.sqrt (2 * Ct * T) + c0 * T) * Bs * (ε + Real.sqrt q * Real.sqrt w + σ * (E + 0)) := by
  set r : ℝ := ε + Real.sqrt q * Real.sqrt w + σ * (E + 0) with hr
  have hsq : 0 ≤ Real.sqrt q * Real.sqrt w := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hσE : 0 ≤ σ * (E + 0) := by positivity
  have hs1 : Real.sqrt (2 * q * Ct * Bs ^ 2 * T * w) =
      Real.sqrt (2 * Ct * T) * Bs * (Real.sqrt q * Real.sqrt w) := by
    have e : 2 * q * Ct * Bs ^ 2 * T * w = (2 * Ct * T * Bs ^ 2) * (q * w) := by ring
    rw [e, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hBs,
      Real.sqrt_mul hq0]
  have hεr : ε ≤ r := by rw [hr]; linarith
  have hqr : Real.sqrt q * Real.sqrt w ≤ r := by rw [hr]; linarith
  have hσr : σ * E ≤ r := by rw [hr]; linarith
  have h1 : ε * (Cy * Bs) ≤ Cy * Bs * r := by
    calc ε * (Cy * Bs) = (Cy * Bs) * ε := by ring
      _ ≤ (Cy * Bs) * r := mul_le_mul_of_nonneg_left hεr (by positivity)
  have h2 : Real.sqrt (2 * Ct * T) * Bs * (Real.sqrt q * Real.sqrt w) ≤
      Real.sqrt (2 * Ct * T) * Bs * r :=
    mul_le_mul_of_nonneg_left hqr (by positivity)
  have h3 : σ * c0 * Bs * (E * T) ≤ c0 * T * Bs * r := by
    calc σ * c0 * Bs * (E * T) = (c0 * T * Bs) * (σ * E) := by ring
      _ ≤ (c0 * T * Bs) * r := mul_le_mul_of_nonneg_left hσr (by positivity)
  rw [hs1]
  calc _ ≤ Cy * Bs * r + Real.sqrt (2 * Ct * T) * Bs * r + c0 * T * Bs * r := by linarith
    _ = _ := by ring

section WassRate

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

/-- `L²` form of the coupling (I1) -/
theorem sa2_I1L2_diff (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈) {N : ℕ}
    (hN : 1 ≤ N) {χ : Euc d → ℝ} {m₀ : ℕ} {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ}
    (hE2 : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Euc d → ℝ) (a : Fin q)
    (hmem : propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N))
    {Y : ℝ} (hY : y0Norm m₀ χ (propagatorW (S.coeff N) 0 (ts a) (φ a)) ≤ Y)
    (hY0 : Y0Class m₀ χ (propagatorW (S.coeff N) 0 (ts a) (φ a))) :
    ∫⁻ ζ, ENNReal.ofReal (((sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal ((ε2 N * Y) ^ 2) := by
  have hε : 0 ≤ ε2 N := hE2.ε2_nonneg N hN
  have hI1 := hE2.I1_L2 N hN _ hmem hY0
  have hinit := HRS.MS.PathFidi.sa26_init_ae (hS.flow N hN)
  have hdat := hS.mean_field.datum N hN
  have hA0 := sa2_AN_nonneg S N
  have hA1 := sa2_AN_le_one S N
  have hAk := sa2_AN_mul S N
  have hy0 : 0 ≤ y0Norm m₀ χ (propagatorW (S.coeff N) 0 (ts a) (φ a)) := sa2_y0Norm_nonneg
  refine le_trans (lintegral_mono_ae ?_) (hI1.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [hinit] with ζ hζ
    refine ENNReal.ofReal_le_ofReal ?_
    have heq : (sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a =
        S.AN N * (S.κ N * (HRS.Whole.pair (HRS.Whole.empirical ((R N).X₀ ζ)) (propagatorW (S.coeff N) 0 (ts a) (φ a)) -
          HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 (ts a) (φ a))) -
          (R N).η ζ (propagatorW (S.coeff N) 0 (ts a) (φ a))) := by
      simp only [sa2Iemp, sa2Itil, PiLp.sub_apply, WithLp.ofLp_toLp, hζ, hdat]
      rw [← hAk]; ring
    rw [heq, mul_pow]
    calc S.AN N ^ 2 * _ ≤ 1 * _ := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          nlinarith
      _ = _ := one_mul _
  · calc ε2 N ^ 2 * y0Norm m₀ χ (propagatorW (S.coeff N) 0 (ts a) (φ a)) ^ 2 ≤ ε2 N ^ 2 * Y ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy0 hY 2) (sq_nonneg _)
      _ = (ε2 N * Y) ^ 2 := by ring

end WassRate

end HRS.MS.MainRdStat
