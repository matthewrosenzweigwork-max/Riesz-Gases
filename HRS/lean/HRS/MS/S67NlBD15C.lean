import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux1
import HRS.MS.S67NlBD08

/-!
# S6.7 nonlinear breakdown, packet 15C: a.e. identification and Sobolev norm-convergence transfer

`s67bd_sobolev_limit_identify`: `H^b` convergence (`b ≥ 0`) dominates `L²` convergence, so a continuous
pointwise limit `F` equals the `H^b` limit `w` a.e. (`mn_ae_of_tendsto`); `fourierL2` and hence all
Sobolev quantities only see the a.e. class.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
/-- `H^b` is closed under differences (`b ≥ 0`). -/
theorem s67bd_memSob_sub {b : ℝ} {u v : Euc d → ℝ}
    (hu : HRS.PDE.ToolboxRd.MemSobolev b u) (hv : HRS.PDE.ToolboxRd.MemSobolev b v) :
    HRS.PDE.ToolboxRd.MemSobolev b (fun x => u x - v x) := by
  refine ⟨hu.1.sub hv.1, ?_⟩
  have hsub := fourierL2_sub hu.1 hv.1
  have hmeas : AEStronglyMeasurable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b *
      ‖fourierL2 (fun x => u x - v x) ξ‖ ^ 2) volume :=
    (continuous_wt_rpow b).aestronglyMeasurable.mul
      ((aestronglyMeasurable_fourierL2 (hu.1.sub hv.1)).norm.pow 2)
  refine Integrable.mono' ((hu.2.add hv.2).const_mul 2) hmeas ?_
  filter_upwards [hsub] with ξ hξ
  have hW : 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b := Real.rpow_nonneg (wt_pos ξ).le _
  rw [Real.norm_of_nonneg (mul_nonneg hW (sq_nonneg _)), hξ]
  have h1 := norm_sub_le (fourierL2 u ξ) (fourierL2 v ξ)
  have h2 : ‖fourierL2 u ξ - fourierL2 v ξ‖ ^ 2 ≤ 2 * (‖fourierL2 u ξ‖ ^ 2 + ‖fourierL2 v ξ‖ ^ 2) := by
    nlinarith [norm_nonneg (fourierL2 u ξ - fourierL2 v ξ), norm_nonneg (fourierL2 u ξ),
      norm_nonneg (fourierL2 v ξ), sq_nonneg (‖fourierL2 u ξ‖ - ‖fourierL2 v ξ‖)]
  have h3 := mul_le_mul_of_nonneg_left h2 hW
  simp only [Pi.add_apply]
  linarith

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
/-- `‖u‖_{L²} ≤ ‖u‖_{H^b}` for `b ≥ 0`. -/
theorem s67bd_l2_le_Hnorm {b : ℝ} (hb : 0 ≤ b) {u : Euc d → ℝ} (hu : HRS.PDE.ToolboxRd.MemSobolev b u) :
    Real.sqrt (∫ x, u x ^ 2) ≤ s67bd_Hnorm b u := by
  unfold s67bd_Hnorm
  refine Real.sqrt_le_sqrt ?_
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  rw [← integral_norm_sq_fourierL2 hu.1]
  refine integral_mono (integrable_norm_sq_fourierL2 hu.1) hu.2 fun ξ => ?_
  have h1 : 1 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b :=
    Real.one_le_rpow (one_le_wt ξ) hb
  exact le_mul_of_one_le_left (sq_nonneg _) h1

/-- The `L²` norm of a square-integrable real function is `√(∫ g²)`. -/
theorem s67bd_eLpNorm_two {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) :
    eLpNorm g 2 (volume : Measure (Euc d)) = ENNReal.ofReal (Real.sqrt (∫ x, g x ^ 2)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  have e : ∀ x : ℝ, ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.rpow_two, sq_abs]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg (g x)),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => sq_nonneg _) (by norm_num),
    Real.sqrt_eq_rpow]

open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux in
theorem s67bd_sobolev_limit_identify (d : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (fn : ℕ → Euc d → ℝ) (w F : Euc d → ℝ)
    (hw : HRS.PDE.ToolboxRd.MemSobolev b w)
    (hfn : ∀ n, HRS.PDE.ToolboxRd.MemSobolev b (fn n))
    (hlim : Tendsto (fun n => s67bd_Hnorm b (fun x => fn n x - w x)) atTop (𝓝 0))
    (hF : Continuous F) (hpoint : ∀ x, Tendsto (fun n => fn n x) atTop (𝓝 (F x))) :
    w =ᵐ[volume] F ∧ HRS.PDE.ToolboxRd.MemSobolev b F ∧
    Tendsto (fun n => s67bd_Hnorm b (fun x => fn n x - F x)) atTop (𝓝 0) ∧
    s67bd_Hnorm b F = s67bd_Hnorm b w := by
  -- L² convergence of fn to w
  have hL2 : Tendsto (fun n => eLpNorm (fun x => w x - fn n x) 2 (volume : Measure (Euc d)))
      atTop (𝓝 0) := by
    have hle : ∀ n, eLpNorm (fun x => w x - fn n x) 2 (volume : Measure (Euc d)) ≤
        ENNReal.ofReal (s67bd_Hnorm b (fun x => fn n x - w x)) := by
      intro n
      have hmem := s67bd_memSob_sub (hfn n) hw
      have hmemL : MemLp (fun x => w x - fn n x) 2 (volume : Measure (Euc d)) := hw.1.sub (hfn n).1
      rw [s67bd_eLpNorm_two hmemL]
      refine ENNReal.ofReal_le_ofReal (le_trans (le_of_eq ?_) (s67bd_l2_le_Hnorm hb hmem))
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using ENNReal.tendsto_ofReal hlim) (fun n => bot_le) hle
  have hae : w =ᵐ[volume] F := mn_ae_of_tendsto fn hL2 hpoint
  have hFw : fourierL2 F = fourierL2 w := (fourierL2_congr_ae hae).symm
  refine ⟨hae, ⟨hw.1.ae_eq hae, ?_⟩, ?_, ?_⟩
  · rw [hFw]; exact hw.2
  · refine hlim.congr fun n => ?_
    unfold s67bd_Hnorm sobolevNormSq
    rw [fourierL2_congr_ae (u := fun x => fn n x - w x) (v := fun x => fn n x - F x)]
    filter_upwards [hae] with x hx
    rw [hx]
  · unfold s67bd_Hnorm sobolevNormSq
    rw [hFw]

end HRS.MS.BreakdownS67
