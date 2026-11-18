import HRS.MS.R26T8AP29k
import HRS.MS.R26T8AP23
import HRS.MS.R26T8AP12
import HRS.MS.R26T8AV2

/-!
# S8.2 T8A P29 (part l): the `PairCorrector` fields of `Q0 + Psi`
Pure assembly for fixed `rho` and `f`.  `Q0` is the parametrix (conormal, Poisson equation up to a remainder `R`, P23 bounds),
`Psi` is a smooth canonical symmetric kernel with `-pairA Psi = R` and `C^8` jets.  Then `Q0 + Psi` is a `PairCorrector`
for the weight `MU + 2` and any amplitude `Afin` dominating the displayed constants.  The nonlocal pole bound enters through the
hypothesis `hJ` (discharged by `r26t8a_p29_pairJ_bound` for `Conormal 4 1`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_p29_fields (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (f : Euc d → ℝ) (Q0 Psi R : Euc d → Euc d → ℝ)
    {M1 MU M2 A1 A2 B CJ Afin : ℝ} (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (hB : 0 ≤ B) (hCJ : 0 ≤ CJ)
    (hM1 : M1 ≤ MU) (hM2 : M2 ≤ MU + 2) (hMU : 0 ≤ MU)
    (hQc : Conormal 8 1 M1 (criticalS d - 2) A1 Q0)
    (hQcan : CanonicalPair (HRS.Whole.withDensityReal rho) Q0) (hQsym : ∀ x y, Q0 x y = Q0 y x)
    (hQdiag : ∀ x, Q0 x x = 0)
    (hQpois : ∀ x y, x ≠ y → -pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q0 x y =
      HSource (HRS.Whole.withDensityReal rho) f x y - R x y)
    (hQ0 : ∀ x y : Euc d, x ≠ y → |Q0 x y| ≤ A2 * Phase2S82.pairWeight M2 x y *
      (1 + smallRadius x y ^ (2 - criticalS d) + if d = 4 then |Real.log (smallRadius x y)| else 0))
    (hQ1 : ∀ x y : Euc d, x ≠ y → ‖pairGradX Q0 x y‖ + ‖pairGradY Q0 x y‖ ≤
      A2 * Phase2S82.pairWeight M2 x y * (1 + smallRadius x y ^ (1 - criticalS d)))
    (hQ2 : ∀ x y : Euc d, x ≠ y → ‖iteratedFDeriv ℝ 2 (Function.uncurry Q0) (x, y)‖ ≤
      A2 * Phase2S82.pairWeight M2 x y * (1 + smallRadius x y ^ (-criticalS d)))
    (hPcan : CanonicalPair (HRS.Whole.withDensityReal rho) Psi) (hPc : ContDiff ℝ 8 (Function.uncurry Psi))
    (hPsym : ∀ x y, Psi x y = Psi y x)
    (hPj : ∀ j : ℕ, j ≤ 8 → ∀ x y : Euc d,
      ‖iteratedFDeriv ℝ j (Function.uncurry Psi) (x, y)‖ ≤ B * Phase2S82.pairWeight MU x y)
    (hPpois : ∀ x y, x ≠ y → -pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Psi x y = R x y)
    (hJ : ∀ (G : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal 4 1 MU (criticalS d - 2) A G →
      ∀ x y : Euc d, x ≠ y →
        |pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G x y| ≤
          CJ * A * Phase2S82.pairWeight (MU + 2) x y * (1 + smallRadius x y ^ (-criticalS d)))
    (hAf1 : A2 + 2 * B ≤ Afin) (hAf2 : A1 + 2 ^ 6 * B ≤ Afin) (hAf3 : CJ * (A1 + 2 ^ 6 * B) ≤ Afin) :
    PairCorrector a beta rho (MU + 2) Afin f (fun x y => Q0 x y + Psi x y) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hU : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hQ8 : ContDiffOn ℝ 8 (Function.uncurry Q0) {p : Euc d × Euc d | p.1 ≠ p.2} := by exact_mod_cast hQc.1
  have hQat : ∀ x y : Euc d, x ≠ y → ContDiffAt ℝ 8 (Function.uncurry Q0) (x, y) := fun x y hxy =>
    hQ8.contDiffAt (hU.mem_nhds (show (x, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} from hxy))
  have hA' : 0 ≤ A1 + 2 ^ 6 * B := by positivity
  -- conormal structure of the sum
  have hPcon : Conormal 6 1 MU (criticalS d - 2) (2 ^ 6 * B) Psi :=
    r26t8a_conormal_of_smooth hB (hPc.of_le (by norm_num)) (fun j hj x y => hPj j (by omega) x y)
  have hQcon6 : Conormal 6 1 MU (criticalS d - 2) A1 Q0 :=
    r26t8a_conormal_mono_M hA1 hM1 (r26t8a_conormal_mono (by norm_num) hQc)
  have hsum6 : Conormal 6 1 MU (criticalS d - 2) (A1 + 2 ^ 6 * B) (fun x y => Q0 x y + Psi x y) :=
    r26t8a_conormal_add hchi hQcon6 hPcon
  have hsum4 : Conormal 4 1 MU (criticalS d - 2) (A1 + 2 ^ 6 * B) (fun x y => Q0 x y + Psi x y) :=
    r26t8a_conormal_mono (by norm_num) hsum6
  have hcan : CanonicalPair (HRS.Whole.withDensityReal rho) (fun x y => Q0 x y + Psi x y) :=
    r26t8a_p29_canonical_add hQcan hPcan
  have hPval : ∀ x y : Euc d, |Psi x y| ≤ B * Phase2S82.pairWeight MU x y := fun x y => by
    have := hPj 0 (by norm_num) x y
    rwa [norm_iteratedFDeriv_zero] at this
  refine ⟨?_, ?_, ?_, hcan, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- measurable
    have h1 : Measurable (Function.uncurry Q0) := r26t8a_p29_measurable_of_diag hQ8 hQdiag
    have h2 : Measurable (Function.uncurry Psi) := hPc.continuous.measurable
    exact h1.add h2
  · -- smooth
    have : ContDiffOn ℝ 8 (Function.uncurry Psi) {p : Euc d × Euc d | p.1 ≠ p.2} := hPc.contDiffOn
    exact hQ8.add this
  · intro x y; rw [hQsym x y, hPsym x y]
  · -- poisson
    intro x y hxy
    have hQ2c : Conormal 2 1 MU (criticalS d - 2) A1 Q0 := r26t8a_conormal_mono (by norm_num) hQcon6
    have hP2c : Conormal 2 1 MU (criticalS d - 2) (2 ^ 6 * B) Psi := r26t8a_conormal_mono (by norm_num) hPcon
    have hadd := r26t8a_V2_pairA_add hd a beta MU (criticalS d) ha hbeta hMU hsd rho hrho hchi hA1 (by positivity)
      hQ2c hP2c hxy
    rw [hadd, neg_add, hQpois x y hxy, hPpois x y hxy]
    ring
  · -- value
    intro x y hxy
    exact r26t8a_p29_value Q0 Psi hA2 hB hM2 (by linarith) hQ0 hPval (by linarith) x y hxy
  · -- gradient
    intro x y hxy
    exact r26t8a_p29_gradient Q0 Psi hA2 hB hM2 (by linarith)
      (fun x y hxy => ((hQat x y hxy).differentiableAt (by norm_num))) hQ1 hPc
      (fun x y => hPj 1 (by norm_num) x y) hAf1 x y hxy
  · -- hessian
    intro x y hxy
    exact r26t8a_p29_hessian Q0 Psi hA2 hB hM2 (by linarith)
      (fun x y hxy => ((hQat x y hxy).of_le (by norm_num))) hQ2 hPc
      (fun x y => hPj 2 (by norm_num) x y) (by linarith) x y hxy
  · -- tangential
    exact r26t8a_conormal_mono_sA hA' (by linarith) le_rfl (r26t8a_conormal_mono_M hA' (by linarith : MU ≤ MU + 2) hsum6)
  · -- nonlocal
    refine ⟨r26t8a_nonlocal_canonical hd a beta MU (A1 + 2 ^ 6 * B) ha hbeta hMU hA' rho hrho _ hcan hsum4, ?_⟩
    intro x y hxy
    refine (hJ _ _ hA' hsum4 x y hxy).trans ?_
    have h0 := r26t8a_p29_pw_nonneg (d := d) (MU + 2) x y
    have h1 : 0 ≤ 1 + smallRadius x y ^ (-criticalS d) := by
      have := Real.rpow_nonneg (r26t8a_p29_smallRadius_nonneg x y) (-criticalS d)
      linarith
    have := mul_nonneg h0 h1
    nlinarith

end HRS.MS.R26T8A

end
