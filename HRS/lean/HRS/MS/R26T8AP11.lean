import HRS.MS.R26T8AP11b2
import HRS.MS.R26T8AP09

/-!
# S8.2 T8A packet P11: two-pole potential gain for the actual nonlocal Newton term
`r26t8a_newton_nonlocal_bound_full`: for `F` with `Conormal (rawGainReg (gainReg k σ + 2) σ) b M σ A F` (regularity corrected for
`σ < 0`, as in P09; `= k+2` plus nothing for `σ ≥ 0` up to the extra derivatives of the divergence source),
`pairJ (localNewton F)` is `Conormal k (b+2) (M+2) (σ - criticalS d)`.
Proof: P09 gives `Q = localNewton F` conormal of order `σ-2`; `r26t8a_p11_Px` (P11e on the divergence source, P11f/P11h outer remainder,
P11g averaged row) handles the `x`-projected row; the `y`-projected row is the same statement for the swapped kernel.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 3200000 in
theorem r26t8a_newton_nonlocal_bound_full (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal (r26t8a_rawGainReg (r26t8a_gainReg k sigma + 2) sigma) b M sigma A F →
        Conormal k (b + 2) (M + 2) (sigma - criticalS d) (C * A)
          (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho)
            (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F)) := by
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_local_newton_bound_full d hd (r26t8a_gainReg k sigma + 2) b a beta M sigma
    ha hbeta hM hsd chi hchi
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_p11_Px d hd k b a beta M sigma ha hbeta hM hsd hchi
  refine ⟨2 * C2 * C1, by positivity, fun rho hrho F A hA hF => ?_⟩
  obtain ⟨-, -, hQ⟩ := hC1 rho hrho F A hA hF
  set Q := localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F with hQdef
  have hQ' : Conormal (r26t8a_gainReg k sigma + 2) (b + 1) M (sigma - 2) (C1 * A) Q := hQ
  have hA1 : 0 ≤ C1 * A := mul_nonneg hC10 hA
  have P1 := hC2 rho hrho Q (C1 * A) hA1 hQ'
  have hQs := r26t8a_f24_conormal_swap hchi hQ'
  have P2 := hC2 rho hrho (fun x y => Q y x) (C1 * A) hA1 hQs
  have P2s := r26t8a_f24_conormal_swap hchi P2
  have hsum := r26t8a_conormal_add hchi P1 P2s
  refine r26t8a_conormal_congr (fun x y _ => ?_)
    (r26t8a_conormal_mono_sA (A' := (2 * C2 * C1) * A) (by positivity) (le_of_eq (by ring)) le_rfl hsum)
  simp only [pairJ, HRS.Whole.projMean, HRS.Whole.pair]

theorem r26t8a_newton_nonlocal_bound_nonneg (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hσ : 0 ≤ sigma)
    (hsd : sigma < d) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal (k + 2) b M sigma A F →
        Conormal k (b + 2) (M + 2) (sigma - criticalS d) (C * A)
          (pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho)
            (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F)) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_newton_nonlocal_bound_full d hd k b a beta M sigma ha hbeta hM hsd chi hchi
  refine ⟨C, hC0, fun rho hrho F A hA hF => hC rho hrho F A hA ?_⟩
  simpa only [r26t8a_gainReg, r26t8a_rawGainReg, if_pos hσ] using hF

end HRS.MS.R26T8A
