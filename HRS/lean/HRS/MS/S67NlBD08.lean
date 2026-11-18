import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovBridgeAux3
import HRS.MS.MovOscAux5
import HRS.MS.ThCorrSAux3

/-!
# S6.7 nonlinear breakdown, packet 08: oscillator-to-Sobolev completion

`s67bd_osc_sobolev`: for `r ≥ 0` and `u ∈ Σ^r`, `u ∈ H^r` with `‖u‖_{H^r} ≤ C ‖u‖_{Σ^r}`.
Route: `mo_bridge1` (multiplier `1`) on the Hermite partial sums, `mo_hsum_tail` at order `0` for
`L²` convergence of the partial sums, `Plancherel` for the Fourier side, and `tcs_fatou`.
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

def s67bd_Hnorm (r : ℝ) (u : Euc d → ℝ) : ℝ :=
  Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r u)

/-- Iterated coordinate derivatives of the constant `1` vanish from order one on. -/
theorem s67bd_dirBdd_one (d N : ℕ) :
    mova3b1_DirBdd N (fun _ : Euc d => (1 : ℝ)) 1 := by
  intro j i _ x
  have hD0 : mova3b1_Dj j (fun _ : Euc d => (0 : ℝ)) = fun _ => 0 := by
    funext y; simp [mova3b1_Dj]
  have hD1 : mova3b1_Dj j (fun _ : Euc d => (1 : ℝ)) = fun _ => 0 := by
    funext y; simp [mova3b1_Dj]
  have hit0 : ∀ k : ℕ, (mova3b1_Dj j)^[k] (fun _ : Euc d => (0 : ℝ)) = fun _ => 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply, hD0, ih]
  cases i with
  | zero => simp
  | succ k => rw [Function.iterate_succ_apply, hD1, hit0 k]; simp

theorem s67bd_osc_sobolev (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Euc d → ℝ, MemOsc r u →
      HRS.PDE.ToolboxRd.MemSobolev r u ∧ s67bd_Hnorm r u ≤ C * oscNorm r u := by
  obtain ⟨C, hC0, hC⟩ := mo_bridge1 (d := d) r hr ⌈r⌉₊ (Nat.le_ceil r)
  refine ⟨C, hC0, fun u hu => ?_⟩
  -- the Hermite partial sums
  have hpL2 : ∀ n, MemLp (mo_pSum u n) 2 (volume : Measure (Euc d)) :=
    fun n => mova2_hsum_memLp _ _
  have hB : ∀ n, HRS.PDE.ToolboxRd.MemSobolev r (mo_pSum u n) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r (mo_pSum u n)) ≤ C * oscNorm r u := by
    intro n
    have h := hC (fun _ => 1) 1 (fun x => by simp) contDiff_const (s67bd_dirBdd_one d _)
      (mo_pSum u n) (mova3_comb_mem _ _)
    simp only [one_mul, mul_one] at h
    exact ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left (mo_pSum_oscNorm_le r hu n).2 hC0)⟩
  set K : ℝ := C * oscNorm r u with hK
  have hK0 : 0 ≤ K := mul_nonneg hC0 (Real.sqrt_nonneg _)
  have hBsq : ∀ n, HRS.PDE.ToolboxRd.sobolevNormSq r (mo_pSum u n) ≤ K ^ 2 :=
    fun n => ((Real.sqrt_le_iff.1 (hB n).2).2)
  -- L² convergence of the partial sums
  have hu0 : MemOsc 0 u := by
    refine ⟨hu.1, Summable.of_nonneg_of_le (fun α => ?_) (fun α => ?_) hu.2⟩
    · exact mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
    · rw [Real.rpow_zero, one_mul]
      exact le_mul_of_one_le_left (sq_nonneg _) (Real.one_le_rpow (oscEv_one_le α) hr)
  have htail := mo_hsum_tail 0 hu0
  have hconv : Tendsto (fun n : ℕ => ∫⁻ ξ, ‖HRS.PDE.ToolboxRd.fourierL2 (mo_pSum u n) ξ -
      HRS.PDE.ToolboxRd.fourierL2 u ξ‖ₑ ^ 2) atTop (𝓝 0) := by
    have e : ∀ n : ℕ, ∫⁻ ξ, ‖HRS.PDE.ToolboxRd.fourierL2 (mo_pSum u n) ξ -
        HRS.PDE.ToolboxRd.fourierL2 u ξ‖ₑ ^ 2 =
        ENNReal.ofReal (oscNorm 0 (fun x => u x - mo_pSum u n x) ^ 2) := by
      intro n
      have hw : MemLp (fun x => mo_pSum u n x - u x) 2 (volume : Measure (Euc d)) :=
        (hpL2 n).sub hu.1
      have hw' : MemLp (fun x => u x - mo_pSum u n x) 2 (volume : Measure (Euc d)) :=
        hu.1.sub (hpL2 n)
      have h1 := HRS.PDE.ToolboxRd.FourierAux.fourierL2_sub (hpL2 n) hu.1
      have h2 : ∫⁻ ξ, ‖HRS.PDE.ToolboxRd.fourierL2 (mo_pSum u n) ξ -
          HRS.PDE.ToolboxRd.fourierL2 u ξ‖ₑ ^ 2 =
          ∫⁻ ξ, ENNReal.ofReal (‖HRS.PDE.ToolboxRd.fourierL2 (fun x => mo_pSum u n x - u x) ξ‖ ^ 2) := by
        refine lintegral_congr_ae ?_
        filter_upwards [h1] with ξ hξ
        rw [← hξ, ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      rw [h2, ← ofReal_integral_eq_lintegral_ofReal
        (HRS.PDE.ToolboxRd.FourierAux.integrable_norm_sq_fourierL2 hw)
        (Eventually.of_forall fun ξ => sq_nonneg _),
        HRS.PDE.ToolboxRd.FourierAux.integral_norm_sq_fourierL2 hw,
        oscNorm_zero _ hw', Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      ring
    simp_rw [e]
    have := (htail.pow 2)
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.tendsto_ofReal (by simpa using this))
  -- Fatou on the Fourier side
  have hFat := HRS.MS.TcS.tcs_fatou r (G := HRS.PDE.ToolboxRd.fourierL2 u)
    (Gn := fun n => HRS.PDE.ToolboxRd.fourierL2 (mo_pSum u n))
    (HRS.PDE.ToolboxRd.FourierAux.memLp_fourierL2 hu.1)
    (fun n => HRS.PDE.ToolboxRd.FourierAux.memLp_fourierL2 (hpL2 n)) hconv
    (B := ENNReal.ofReal (K ^ 2)) (fun n => by
      have hi := (hB n).1.2
      have e := ofReal_integral_eq_lintegral_ofReal hi
        (Eventually.of_forall fun ξ => mul_nonneg
          (Real.rpow_nonneg (HRS.PDE.ToolboxRd.FourierAux.wt_pos ξ).le _) (sq_nonneg _))
      exact e.symm.trans_le (ENNReal.ofReal_le_ofReal (hBsq n)))
  have hmeas : AEStronglyMeasurable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r *
      ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2) volume :=
    (HRS.PDE.ToolboxRd.FourierAux.continuous_wt_rpow r).aestronglyMeasurable.mul
      ((HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hu.1).norm.pow 2)
  have hnn : ∀ ξ : Euc d, 0 ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r *
      ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2 := fun ξ =>
    mul_nonneg (Real.rpow_nonneg (HRS.PDE.ToolboxRd.FourierAux.wt_pos ξ).le _) (sq_nonneg _)
  have hint : Integrable (fun ξ : Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r *
      ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2) volume := by
    refine ⟨hmeas, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ ξ, ‖(1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r *
          ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2‖ₑ
        = ∫⁻ ξ, ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ r *
          ‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2) :=
          lintegral_congr fun ξ => Real.enorm_of_nonneg (hnn ξ)
      _ ≤ ENNReal.ofReal (K ^ 2) := hFat
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨⟨hu.1, hint⟩, ?_⟩
  have hval : HRS.PDE.ToolboxRd.sobolevNormSq r u ≤ K ^ 2 := by
    unfold HRS.PDE.ToolboxRd.sobolevNormSq
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn) hmeas]
    exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hFat
  unfold s67bd_Hnorm
  exact (Real.sqrt_le_iff.2 ⟨hK0, hval⟩)

end HRS.MS.BreakdownS67
