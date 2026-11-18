import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.ThCorrSAux3
import HRS.MS.S67NlBD08

/-!
# S6.7 nonlinear breakdown, packet 15E: Sobolev lower semicontinuity under an honest `L²` limit

`s67bd_sobolev_fatou`: `fn ∈ H^b`, `fn → F` in `L²`, `‖fn‖_{H^b} ≤ a_n → A` imply `F ∈ H^b`,
`‖F‖_{H^b} ≤ A`.  Plancherel turns the `L²` convergence into `L²` convergence of the Fourier
transforms; `tcs_fatou` is applied to the tail `n ≥ N` with the constant bound `(A+ε)²`, then `ε → 0`.
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

/-- `‖g‖_{L²}` is `√(∫ g²)` for square-integrable `g`. -/
theorem s67bd_fatou_eLpNorm_two {g : Euc d → ℝ} (hg : MemLp g 2 (volume : Measure (Euc d))) :
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
theorem s67bd_sobolev_fatou (d : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (fn : ℕ → Euc d → ℝ) (F : Euc d → ℝ)
    (hfn : ∀ n, HRS.PDE.ToolboxRd.MemSobolev b (fn n)) (hF : MemLp F 2 volume)
    (hL2 : Tendsto (fun n => (eLpNorm (fun x => fn n x - F x) 2 volume).toReal)
      atTop (𝓝 0))
    (a : ℕ → ℝ) (A : ℝ) (ha : ∀ n, s67bd_Hnorm b (fn n) ≤ a n)
    (halim : Tendsto a atTop (𝓝 A)) :
    HRS.PDE.ToolboxRd.MemSobolev b F ∧ s67bd_Hnorm b F ≤ A := by
  have hA0 : 0 ≤ A :=
    ge_of_tendsto halim (Filter.Eventually.of_forall fun n => (Real.sqrt_nonneg _).trans (ha n))
  -- Fourier-side `L²` convergence (Plancherel)
  have hconv0 : Tendsto (fun n : ℕ => ∫⁻ ξ, ‖fourierL2 (fn n) ξ - fourierL2 F ξ‖ₑ ^ 2)
      atTop (𝓝 0) := by
    have e : ∀ n : ℕ, ∫⁻ ξ, ‖fourierL2 (fn n) ξ - fourierL2 F ξ‖ₑ ^ 2 =
        ENNReal.ofReal ((eLpNorm (fun x => fn n x - F x) 2 volume).toReal ^ 2) := by
      intro n
      have hw : MemLp (fun x => fn n x - F x) 2 (volume : Measure (Euc d)) := (hfn n).1.sub hF
      have h1 := fourierL2_sub (hfn n).1 hF
      have h2 : ∫⁻ ξ, ‖fourierL2 (fn n) ξ - fourierL2 F ξ‖ₑ ^ 2 =
          ∫⁻ ξ, ENNReal.ofReal (‖fourierL2 (fun x => fn n x - F x) ξ‖ ^ 2) := by
        refine lintegral_congr_ae ?_
        filter_upwards [h1] with ξ hξ
        rw [← hξ, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rw [h2, ← ofReal_integral_eq_lintegral_ofReal (integrable_norm_sq_fourierL2 hw)
        (Eventually.of_forall fun ξ => sq_nonneg _), integral_norm_sq_fourierL2 hw,
        s67bd_fatou_eLpNorm_two hw, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
        Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
    simp_rw [e]
    rw [← ENNReal.ofReal_zero]
    exact ENNReal.tendsto_ofReal (by simpa using hL2.pow 2)
  have hG : MemLp (fourierL2 F) 2 volume := memLp_fourierL2 hF
  have hnn : ∀ ξ : Euc d, 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b * ‖fourierL2 F ξ‖ ^ 2 := fun ξ =>
    mul_nonneg (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _)
  -- Fatou for each `ε > 0`
  have hε : ∀ ε : ℝ, 0 < ε → ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b *
      ‖fourierL2 F ξ‖ ^ 2) ≤ ENNReal.ofReal ((A + ε) ^ 2) := by
    intro ε hεpos
    obtain ⟨N, hN⟩ := eventually_atTop.1 (halim.eventually (gt_mem_nhds (by linarith : A < A + ε)))
    have hFat := HRS.MS.TcS.tcs_fatou b (G := fourierL2 F)
      (Gn := fun k => fourierL2 (fn (k + N))) hG
      (fun k => memLp_fourierL2 (hfn (k + N)).1)
      (hconv0.comp (tendsto_add_atTop_nat N))
      (B := ENNReal.ofReal ((A + ε) ^ 2)) (fun k => by
        have hi := (hfn (k + N)).2
        have e := ofReal_integral_eq_lintegral_ofReal hi
          (Eventually.of_forall fun ξ => mul_nonneg
            (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _))
        refine e.symm.trans_le (ENNReal.ofReal_le_ofReal ?_)
        have h0 : 0 ≤ s67bd_Hnorm b (fn (k + N)) := Real.sqrt_nonneg _
        have h1 : s67bd_Hnorm b (fn (k + N)) ≤ A + ε := (ha _).trans (hN _ (by omega)).le
        have h2 : sobolevNormSq b (fn (k + N)) = s67bd_Hnorm b (fn (k + N)) ^ 2 := by
          unfold s67bd_Hnorm
          exact (Real.sq_sqrt (integral_nonneg fun ξ => mul_nonneg
            (Real.rpow_nonneg (wt_pos ξ).le _) (sq_nonneg _))).symm
        show sobolevNormSq b (fn (k + N)) ≤ (A + ε) ^ 2
        rw [h2]
        exact pow_le_pow_left₀ h0 h1 2)
    exact hFat
  -- finiteness and limit
  have hfin : ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b *
      ‖fourierL2 F ξ‖ ^ 2) < ⊤ := (hε 1 one_pos).trans_lt ENNReal.ofReal_lt_top
  have hmeas : AEStronglyMeasurable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b *
      ‖fourierL2 F ξ‖ ^ 2) volume :=
    (continuous_wt_rpow b).aestronglyMeasurable.mul
      ((aestronglyMeasurable_fourierL2 hF).norm.pow 2)
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b *
      ‖fourierL2 F ξ‖ ^ 2) volume := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ ξ, ‖(1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b * ‖fourierL2 F ξ‖ ^ 2‖ₑ
        = ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ b *
          ‖fourierL2 F ξ‖ ^ 2) := lintegral_congr fun ξ => Real.enorm_of_nonneg (hnn ξ)
      _ < ⊤ := hfin
  refine ⟨⟨hF, hint⟩, ?_⟩
  have hval : sobolevNormSq b F ≤ A ^ 2 := by
    have hε' : ∀ ε : ℝ, 0 < ε → sobolevNormSq b F ≤ (A + ε) ^ 2 := by
      intro ε hεpos
      unfold sobolevNormSq
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeas]
      exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) (hε ε hεpos)
    have hcont : Tendsto (fun ε : ℝ => (A + ε) ^ 2) (𝓝[>] 0) (𝓝 (A ^ 2)) := by
      have : Tendsto (fun ε : ℝ => (A + ε) ^ 2) (𝓝 0) (𝓝 ((A + 0) ^ 2)) :=
        ((continuous_const.add continuous_id).pow 2).tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact ge_of_tendsto hcont (by
      filter_upwards [self_mem_nhdsWithin] with ε hεpos using hε' ε hεpos)
  unfold s67bd_Hnorm
  exact (Real.sqrt_le_iff.2 ⟨hA0, hval⟩)

end HRS.MS.BreakdownS67
