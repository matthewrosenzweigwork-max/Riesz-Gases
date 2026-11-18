import HRS.MS.R26T8AP11b1
import HRS.MS.R26T8AP11b0
import HRS.MS.R26T8AY5
import HRS.MS.R26T8AP11f

/-!
# S8.2 T8A W1 (= P11b2 same-k): the `x`-projected nonlocal row
For `Q` conormal of regularity `k + 2` (no `gainReg`), degree `b+1`, order `σ-2`: `oneJ(Q(·,y))(x) - ∫ oneJ(Q(·,y)) dμ` is
`Conormal k (b+2) (M+2) (σ - criticalS d)`.  Pieces: local Riesz gain of the divergence source (P11e, `a4`), outer remainder of every order
(`P11h`), the averaged row (P11g jets + `b0` smoothness).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_p11_Px_same (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hsd : sigma < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ Q : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal (k + 2) (b + 1) M (sigma - 2) A Q →
      Conormal k (b + 2) (M + 2) (sigma - criticalS d) (C * A)
        (fun x y => oneJ (critCoeff d a beta rho) (fun u => Q u y) x -
          ∫ x', oneJ (critCoeff d a beta rho) (fun u => Q u y) x' ∂(HRS.Whole.withDensityReal rho)) := by
  classical
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta ρ0
  swap
  · exact ⟨0, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩
  obtain ⟨ρ0, h0⟩ := hex
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd' : criticalS d < d := by unfold criticalS; linarith
  set K : ℕ := k with hK
  have hkK : k ≤ K := hK.ge
  obtain ⟨hρs, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith)
    ha hbeta h0
  obtain ⟨Cρ, cρ, hCρ, hcρ, hρb⟩ := r26t8a_f23_rho_unif hg (K + 1)
  have hρj : ∀ j ≤ K + 1, ∀ x, ‖iteratedFDeriv ℝ j ρ0 x‖ ≤ Cρ := fun j hj x =>
    (hρb j hj x).trans (mul_le_of_le_one_right hCρ
      (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, hcρ])))
  obtain ⟨C3, hC30, hC3⟩ := r26t8a_local_riesz_gain_same d hd k (b + 1) (criticalS d) M sigma hs0 hsd' hM hsd chi hchi
  obtain ⟨C4, hC40, hC4⟩ := r26t8a_nonlocal_outer_gen d hd k (b + 1) a beta M sigma ha hbeta hM hsd (sigma - criticalS d) chi hchi
  obtain ⟨C5, hC50, hC5⟩ := r26t8a_g7_jets d hd k (b + 1) a beta M sigma ha hbeta hM hsd h0
  set c2 : ℝ := (d : ℝ) * (2 ^ K * (((K : ℝ) + 1) ^ 2 * Cρ * 4)) + (d : ℝ) * (2 ^ K * (((K : ℝ) + 1) ^ 2 * Cρ * 2))
    with hc2
  have hc20 : 0 ≤ c2 := by positivity
  refine ⟨C4 + C3 * c2 + 2 ^ k * C5, by positivity, ?_⟩
  intro rho hrho Q A hA hQ
  have hρeq : rho = ρ0 :=
    (critical_thermal_eq d hd a beta ha hbeta hrho).trans (critical_thermal_eq d hd a beta ha hbeta h0).symm
  subst hρeq
  have hQk : Conormal (k + 2) (b + 1) M (sigma - 2) A Q := hQ
  -- the divergence source
  have hρK : ContDiff ℝ ((K + 1 : ℕ) : WithTop ℕ∞) rho := hρs.of_le (by exact_mod_cast le_top)
  have hS0 := r26t8a_divSource_conormal hchi K (b + 1) hA hCρ hQ hρK hρj
  have hSc : Conormal K (b + 1) M sigma (c2 * A) (r26t8a_divSource rho Q) :=
    r26t8a_conormal_mono_sA (by positivity) (le_of_eq (by rw [hc2]; ring)) (by linarith) hS0
  have hLR := (hC3 (r26t8a_divSource rho Q) (c2 * A) (by positivity) hSc).2
  -- outer remainder
  have hOut := hC4 rho hrho Q A hA hQk
  -- the averaged row
  have hrs := r26t8a_p11_row_smooth d hd k (b + 1) a beta M sigma ha hbeta hM hsd hrho Q A hA hQk
  have hrj := hC5 Q A hA hQk
  have hr' : ContDiff ℝ (k : WithTop ℕ∞) (fun z => -(∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u z) x
      ∂(HRS.Whole.withDensityReal rho))) := hrs.neg
  have hjr' : ∀ j ≤ k, ∀ y, ‖iteratedFDeriv ℝ j (fun z => -(∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u z) x
      ∂(HRS.Whole.withDensityReal rho))) y‖ ≤ (C5 * A) * jbracket y ^ (M + 2) := by
    intro j hj y
    have := hrj j hj y
    rw [show (fun z => -(∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u z) x
      ∂(HRS.Whole.withDensityReal rho))) = -(fun z => ∫ x, oneJ (critCoeff d a beta rho) (fun u => Q u z) x
      ∂(HRS.Whole.withDensityReal rho)) from rfl, iteratedFDeriv_neg_apply, norm_neg]
    linarith
  have hRow := r26t8a_conormal_of_snd (b := b + 2) (σ := sigma - criticalS d) (by linarith) (by positivity) hr' hjr'
  have f1 := r26t8a_conormal_mono_b (b' := b + 2) (by positivity) (by omega) hOut
  have f2 := r26t8a_f23_conormal_M_mono (M' := M + 2) (by linarith) (by positivity) hLR
  have hsum := r26t8a_conormal_add hchi (r26t8a_conormal_add hchi f1 f2) hRow
  refine r26t8a_conormal_congr (fun x y _ => ?_)
    (r26t8a_conormal_mono_sA (A' := (C4 + C3 * c2 + 2 ^ k * C5) * A) (by positivity) (le_of_eq (by ring)) le_rfl hsum)
  ring

end HRS.MS.R26T8A
