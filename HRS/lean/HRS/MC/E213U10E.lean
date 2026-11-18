import HRS.MC.E213U10D
import HRS.MC.E213U7b

/-!
# Packet e213u10, part E: the drift functional on the pair space

For `x = (w, β) ∈ 𝒳_{r,L} × L²([0,L];E_r)` put `Y_x^τ = winPred (lift w) τ` and `c_x = nearCoef b (embed (β(· - b)))`;
`u10_SD x` is the drift summand `DU(τ, Y_x^τ)[𝒟_{c_x}((u,u'])]` and `u10_FD x = rsLim (u10_SD x)` the drift integral.  The
integral exists for every `x`; `u10_FD` is Lipschitz in the sense of `u10_FD_lip` and bounded by `u10_FD_abs_le`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

section Defs

variable (hE : EdgeworthHyp S β₀ m) (T : ℝ) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (b L : ℝ)
  (hL : 0 ≤ L) (hH : a + T ≤ b + L)

/-- The predicted window of the lifted window path. -/
def u10_Y (w : PathSpace d (rLvl d) L) (τ : ℝ) : PathSpace d m T :=
  winPred (regime S β₀ hE) m T a ha (u10_liftW hE b L (a + T) hL hH w) τ

/-- The near drift coefficient of an `L²` element. -/
def u10_cD (m : ℝ) (β : L2Path d (rLvl d) L) : ℝ → NegSobolev d m :=
  nearCoef b (fun v => NegSobolev.embed m (u10_bq b L β v))

/-- The drift summand on the pair space. -/
def u10_SD (x : PathSpace d (rLvl d) L × L2Path d (rLvl d) L) : ℝ → ℝ → ℝ → ℝ :=
  rsSumD (Ucan hE T a ha Φ) (u10_Y hE T a ha b L hL hH x.1)
    (fun u u' => winDrift (regime S β₀ hE) m T a ha (u10_cD b L m x.2) u u')

/-- The drift integral on the pair space. -/
def u10_FD (x : PathSpace d (rLvl d) L × L2Path d (rLvl d) L) : ℝ :=
  rsLim (a + T) (u10_SD hE T a ha Φ b L hL hH x)

end Defs

theorem u10_cD_memLp (hE : EdgeworthHyp S β₀ m) (T a b L : ℝ) (hL : 0 ≤ L) (hH : a + T ≤ b + L)
    (β : L2Path d (rLvl d) L) :
    MemLp (u10_cD b L m β) 1 (volume.restrict (Set.Icc (0 : ℝ) (a + T))) := by
  have h := HRS.MC.E213U7.e213u7_memLp_embed hE (a + T) (f := nearCoef b (u10_bq b L β))
    (g := nearCoef b (u10_bq b L β)) (u10_nearCoef0_meas b (u10_bq_meas b L β))
    (u10_nearCoef_norm_int hH (u10_bq_meas b L β) (u10_bq_int b L hL β)) (fun v => le_rfl)
  have e := HRS.MC.E213U7.e213u7_near_embed hE b (u10_bq b L β)
  unfold u10_cD
  rw [e]
  exact h

theorem u10_SD_isRS (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (b L : ℝ) (hL : 0 ≤ L) (hH : a + T ≤ b + L)
    (x : PathSpace d (rLvl d) L × L2Path d (rLvl d) L) :
    IsRS (a + T) (u10_SD hE T a ha Φ b L hL hH x) (u10_FD hE T a ha Φ b L hL hH x) := by
  have hH0 : 0 < a + T := by linarith
  have hreg : HRS.MC.E213U7.e213u7_Reg hE T a ha Φ := HRS.MC.E213U5.Ucan_regular_proof hE T hT a ha Φ hΦ
  have hY := HRS.MC.E213U7.e213u7_Y_cont hE T hT a ha (u10_liftW hE b L (a + T) hL hH x.1)
  have hA := HRS.MC.E213U7.e213u7_fderiv_cont hE T a ha Φ hreg _ hY
  obtain ⟨I, hI⟩ := HRS.MC.E213U7.e213u7_drift_exists hE T hT a ha
    (fun τ => fderiv ℝ (Ucan hE T a ha Φ τ) (winPred (regime S β₀ hE) m T a ha (u10_liftW hE b L (a + T) hL hH x.1) τ))
    hA (u10_cD b L m x.2) (u10_cD_memLp hE T a b L hL hH x.2)
  have hI' : IsRS (a + T) (u10_SD hE T a ha Φ b L hL hH x) I := hI
  have : u10_FD hE T a ha Φ b L hL hH x = I := HRS.MC.E213U7.e213u7_rsLim_eq hH0 hI'
  rw [this]
  exact hI'

theorem u10_Y_sub_norm_le (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (b L : ℝ)
    (hL : 0 ≤ L) (hH : a + T ≤ b + L) (CY : ℝ) (hCY0 : 0 ≤ CY)
    (hCY : ∀ (w : PathSpace d m (a + T)) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) (a + T) →
      ‖winPred (regime S β₀ hE) m T a ha w τ‖ ≤ CY * ‖w‖)
    (w w' : PathSpace d (rLvl d) L) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) :
    ‖u10_Y hE T a ha b L hL hH w τ - u10_Y hE T a ha b L hL hH w' τ‖ ≤ CY * ‖w - w'‖ := by
  unfold u10_Y
  rw [← u10_winPred_sub hE T hT a ha _ _ hτ, ← map_sub]
  refine (hCY _ τ hτ).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hCY0
  have h1 := (u10_liftW hE b L (a + T) hL hH).le_opNorm (w - w')
  have h2 := mul_le_mul_of_nonneg_right (u10_liftW_norm_le hE b L (a + T) hL hH) (norm_nonneg (w - w'))
  linarith

/-- Splitting of the near drift coefficient: `c_β = c_{β'} + c_{β - β'}` (pointwise differences of representatives). -/
theorem u10_cD_split (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (b L : ℝ) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (β β' : L2Path d (rLvl d) L) {u u' : ℝ} (hu : 0 ≤ u) (huu' : u ≤ u') (hu' : u' ≤ a + T) :
    winDrift (regime S β₀ hE) m T a ha (u10_cD b L m β) u u' =
      winDrift (regime S β₀ hE) m T a ha (u10_cD b L m β') u u' +
      winDrift (regime S β₀ hE) m T a ha
        (nearCoef b (fun v => NegSobolev.embed m (u10_bqd b L β β' v))) u u' := by
  have hadd := HRS.MC.E213U1.winDrift_add_proof hE T hT a ha (nearCoef b (u10_bq b L β'))
    (nearCoef b (u10_bqd b L β β')) (u10_nearCoef0_meas b (u10_bq_meas b L β'))
    (u10_nearCoef0_meas b (u10_bqd_meas b L β β'))
    (u10_nearCoef_norm_int hH (u10_bq_meas b L β') (u10_bq_int b L hL β'))
    (u10_nearCoef_norm_int hH (u10_bqd_meas b L β β') (u10_bqd_int b L hL β β')) u u' hu huu' hu'
  have e1 : (fun v => NegSobolev.embed m (nearCoef b (u10_bq b L β') v + nearCoef b (u10_bqd b L β β') v)) =
      u10_cD b L m β := by
    funext v
    unfold u10_cD nearCoef u10_bqd
    by_cases h : b ≤ v
    · simp only [if_pos h]
      congr 1
      abel
    · simp only [if_neg h, add_zero]
      exact HRS.MC.E213U7.e213u7_embed_zero hE
  have e2 : (fun v => NegSobolev.embed m (nearCoef b (u10_bq b L β') v)) = u10_cD b L m β' :=
    (HRS.MC.E213U7.e213u7_near_embed hE b (u10_bq b L β')).symm
  have e3 : (fun v => NegSobolev.embed m (nearCoef b (u10_bqd b L β β') v)) =
      nearCoef b (fun v => NegSobolev.embed m (u10_bqd b L β β' v)) :=
    (HRS.MC.E213U7.e213u7_near_embed hE b (u10_bqd b L β β')).symm
  rw [e1, e2, e3] at hadd
  exact hadd

end HRS.MC.E213U10

end
