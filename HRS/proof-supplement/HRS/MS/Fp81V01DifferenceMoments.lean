import HRS.MS.ProClosureS111ObservationMoments
import HRS.MS.ProClosureS111PairedGaussianDecay
import HRS.MS.ProClosureS111PairedGaussianFamilies
import HRS.MS.S111X2Aux44

/-!
Scalar fourth-moment decay for the difference of the two sides of the
shared thermal coupling. This is the fixed-time input for the canonical
window difference estimate.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.ProClosureS111 HRS.MS.S111X1 HRS.MS.S111X2
  HRS.MS.S111T HRS.MS.R26T6

variable {d : ℕ} {Omega : Type} [MeasurableSpace Omega]
variable {P : Measure Omega} [IsProbabilityMeasure P]
variable {s a β γ H lam : ℝ} {ρ : Euc d → ℝ}
variable {Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d)}

/-- Mixed-time covariance of the shared-noise difference observations. The
common noise term cancels between the two sides, even when the observation
times differ. -/
theorem fp81v01_difference_observation_cross_moment (hd : 2 ≤ d)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ)
    (hρ : IsThermalEquilibrium d s a β ρ)
    (hZ : r26t6_SharedThermalLaw P s a β γ H ρ Z)
    {t v : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (hv : v ∈ Icc (0 : ℝ) H)
    {phi : Euc d → ℝ} (hphi : IsOscTest (wholeSpaceIndex d) phi) :
    let D : Omega → ℝ := fun w =>
      (OscDual.eval (Z 0 t w) phi - OscDual.eval (Z 1 t w) phi)
      * (OscDual.eval (Z 0 v w) phi - OscDual.eval (Z 1 v w) phi)
    ∫ w, D w ∂P =
      HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ
        (propagatorW (r26t6_thermalCoeff d s a β ρ) 0 t phi)
        (propagatorW (r26t6_thermalCoeff d s a β ρ) 0 v phi) +
      HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
        (propagatorW (r26t6_thermalCoeff d s a β ρ) 0 t phi)
        (propagatorW (r26t6_thermalCoeff d s a β ρ) 0 v phi) := by
  classical
  let C := r26t6_thermalCoeff d s a β ρ
  let mu := HRS.Whole.withDensityReal ρ
  let X0t : Omega → ℝ := fun w => OscDual.eval (Z 0 t w) phi
  let X0v : Omega → ℝ := fun w => OscDual.eval (Z 0 v w) phi
  let X1t : Omega → ℝ := fun w => OscDual.eval (Z 1 t w) phi
  let X1v : Omega → ℝ := fun w => OscDual.eval (Z 1 v w) phi
  let D : Omega → ℝ := fun w => (X0t w - X1t w) * (X0v w - X1v w)
  let side : Fin 4 → Fin 2 := ![0, 0, 1, 1]
  let ts : Fin 4 → ℝ := ![t, v, t, v]
  obtain ⟨G, hG, hmem⟩ := physical_observation_gaussian_space Z hZ
  have hXt4 : MemLp X0t 4 P := by simpa [X0t] using (hG _ (hmem 0 t ht phi hphi)).1
  have hXv4 : MemLp X0v 4 P := by simpa [X0v] using (hG _ (hmem 0 v hv phi hphi)).1
  have hYt4 : MemLp X1t 4 P := by simpa [X1t] using (hG _ (hmem 1 t ht phi hphi)).1
  have hYv4 : MemLp X1v 4 P := by simpa [X1v] using (hG _ (hmem 1 v hv phi hphi)).1
  have hsec := physical_shared_observation_second hd hs0 hs ha hβ hγ hρ hZ
    4 side ts (fun _ => phi) (fun i => by fin_cases i <;> assumption)
    (fun _ => hphi)
  have h00 : (∫ w, X0t w * X0v w ∂P) =
      HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ
        (propagatorW C 0 t phi) (propagatorW C 0 v phi) + noiseCovW C β⁻¹ t v phi phi := by
    simpa [X0t, X0v, side, ts, C, mu, r26t6_preparation] using hsec 0 1
  have h11 : (∫ w, X1t w * X1v w ∂P) =
      HRS.Whole.susceptibilityCov (rieszKernel d s) mu β
        (propagatorW C 0 t phi) (propagatorW C 0 v phi) + noiseCovW C β⁻¹ t v phi phi := by
    simpa [X1t, X1v, side, ts, C, mu, r26t6_preparation] using hsec 2 3
  have h01 : (∫ w, X0t w * X1v w ∂P) = noiseCovW C β⁻¹ t v phi phi := by
    simpa [X0t, X1v, side, ts, C, mu, r26t6_preparation] using hsec 0 3
  have h10 : (∫ w, X1t w * X0v w ∂P) = noiseCovW C β⁻¹ t v phi phi := by
    simpa [X1t, X0v, side, ts, C, mu, r26t6_preparation] using hsec 2 1
  have hpoly : (fun w => D w) = fun w =>
      X0t w * X0v w - X0t w * X1v w - X1t w * X0v w + X1t w * X1v w := by
    funext w
    dsimp [D]
    ring
  have hprod00 : Integrable (fun w => X0t w * X0v w) P :=
    (HRS.MC.QRSpec.Wick.qrpw_int_mul hXt4 hXv4)
  have hprod01 : Integrable (fun w => X0t w * X1v w) P :=
    (HRS.MC.QRSpec.Wick.qrpw_int_mul hXt4 hYv4)
  have hprod10 : Integrable (fun w => X1t w * X0v w) P :=
    (HRS.MC.QRSpec.Wick.qrpw_int_mul hYt4 hXv4)
  have hprod11 : Integrable (fun w => X1t w * X1v w) P :=
    (HRS.MC.QRSpec.Wick.qrpw_int_mul hYt4 hYv4)
  have hI01 : Integrable (fun w => X0t w * X0v w - X0t w * X1v w) P :=
    hprod00.sub hprod01
  have hI012 : Integrable (fun w =>
      X0t w * X0v w - X0t w * X1v w - X1t w * X0v w) P := hI01.sub hprod10
  calc
    ∫ w, D w ∂P = ∫ w, (X0t w * X0v w - X0t w * X1v w -
        X1t w * X0v w + X1t w * X1v w) ∂P := by rw [hpoly]
    _ = (∫ w, X0t w * X0v w ∂P) - (∫ w, X0t w * X1v w ∂P) -
        (∫ w, X1t w * X0v w ∂P) + (∫ w, X1t w * X1v w ∂P) := by
      rw [integral_add hI012 hprod11,
        integral_sub hI01 hprod10,
        integral_sub hprod00 hprod01]
    _ = _ := by rw [h00, h01, h10, h11]; ring

/-- The shared-noise difference has a squared-increment estimate whose
constant is the horizon-free H01 orbit constant. -/
theorem fp81v01_difference_observation_increment_variance_le (hd : 2 ≤ d)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hlam : 0 < lam)
    (hρ : IsThermalEquilibrium d s a β ρ)
    (hP : IsR2Poincare (HRS.Whole.withDensityReal ρ) lam)
    (hZ : r26t6_SharedThermalLaw P s a β γ H ρ Z)
    {t v : ℝ} (ht : t ∈ Icc (0 : ℝ) H) (hv : v ∈ Icc (0 : ℝ) H)
    (htv : t ≤ v) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ alpha : MultiIndex d,
      (∫ w, ((OscDual.eval (Z 0 t w) (oscTestFun (wholeSpaceIndex d : ℝ) alpha) -
        OscDual.eval (Z 1 t w) (oscTestFun (wholeSpaceIndex d : ℝ) alpha)) -
        (OscDual.eval (Z 0 v w) (oscTestFun (wholeSpaceIndex d : ℝ) alpha) -
        OscDual.eval (Z 1 v w) (oscTestFun (wholeSpaceIndex d : ℝ) alpha))) ^ 2 ∂P) ≤
          2 * s111x2_centeredSquare (HRS.Whole.withDensityReal ρ)
            (fun x => propagatorW (r26t6_thermalCoeff d s a β ρ) 0 v
              (oscTestFun (wholeSpaceIndex d : ℝ) alpha) x -
              propagatorW (r26t6_thermalCoeff d s a β ρ) 0 t
                (oscTestFun (wholeSpaceIndex d : ℝ) alpha) x) ∧
        (∫ w, ((OscDual.eval (Z 0 t w) (oscTestFun (wholeSpaceIndex d : ℝ) alpha) -
        OscDual.eval (Z 1 t w) (oscTestFun (wholeSpaceIndex d : ℝ) alpha)) -
        (OscDual.eval (Z 0 v w) (oscTestFun (wholeSpaceIndex d : ℝ) alpha) -
        OscDual.eval (Z 1 v w) (oscTestFun (wholeSpaceIndex d : ℝ) alpha))) ^ 2 ∂P) ≤
        2 * B * (v - t) ^ 2 * Real.exp (-2 * (lam / β) * t) := by
  classical
  obtain ⟨B, hB, hmemU, hH01⟩ := s111x2_H01 hd s a β lam hs0 hs ha hβ hlam hρ hP
  refine ⟨B, hB, ?_⟩
  intro alpha
  let psi := oscTestFun (wholeSpaceIndex d : ℝ) alpha
  have hpsi : IsOscTest (wholeSpaceIndex d) psi :=
    HRS.MS.GenPath.s56_isOscTest (wholeSpaceIndex d) alpha
  have ht0 : 0 ≤ t := ht.1
  have hv0 : 0 ≤ v := hv.1
  have hft : MemLp (propagatorW (r26t6_thermalCoeff d s a β ρ) 0 t psi) 2
      (HRS.Whole.withDensityReal ρ) := by
    simpa [psi, r26t6_thermalCoeff] using hmemU alpha t ht0
  have hfv : MemLp (propagatorW (r26t6_thermalCoeff d s a β ρ) 0 v psi) 2
      (HRS.Whole.withDensityReal ρ) := by
    simpa [psi, r26t6_thermalCoeff] using hmemU alpha v hv0
  obtain ⟨hDt, hDtSq, _⟩ := physical_shared_difference_moments
    hd hs0 hs ha hβ hγ hρ hZ ht hpsi
  obtain ⟨hDv, hDvSq, _⟩ := physical_shared_difference_moments
    hd hs0 hs ha hβ hγ hρ hZ hv hpsi
  have hcross := fp81v01_difference_observation_cross_moment
    hd hs0 hs ha hβ hγ hρ hZ ht hv hpsi
  let Dt : Omega → ℝ := fun w =>
    OscDual.eval (Z 0 t w) psi - OscDual.eval (Z 1 t w) psi
  let Dv : Omega → ℝ := fun w =>
    OscDual.eval (Z 0 v w) psi - OscDual.eval (Z 1 v w) psi
  have hDt4 : MemLp Dt 4 P := by simpa [Dt] using hDt
  have hDv4 : MemLp Dv 4 P := by simpa [Dv] using hDv
  have hDtI : Integrable (fun w => Dt w ^ 2) P :=
    HRS.MC.QRSpec.Wick.qrpw_int_sq hDt4
  have hDvI : Integrable (fun w => Dv w ^ 2) P :=
    HRS.MC.QRSpec.Wick.qrpw_int_sq hDv4
  have hcrossI : Integrable (fun w => Dt w * Dv w) P :=
    HRS.MC.QRSpec.Wick.qrpw_int_mul hDt4 hDv4
  let C := r26t6_thermalCoeff d s a β ρ
  let mu := HRS.Whole.withDensityReal ρ
  letI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hρ.2.1
  let ft : Euc d → ℝ := propagatorW C 0 t psi
  let fv : Euc d → ℝ := propagatorW C 0 v psi
  let delta : Euc d → ℝ := fun x => ft x - fv x
  have hdReal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨M0, c, S0, hc, hTc⟩ :=
    HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  have hmax : 0 ≤ max γ β := le_trans hγ (le_max_left _ _)
  obtain ⟨eta, heta, heta1, hforms⟩ :=
    s111x2_thermal_response_forms hd s a β (max γ β) hs0 hs ha hβ hmax
  have hformγ := hforms ρ hρ γ ⟨hγ, le_max_left _ _⟩
  have hformβ := hforms ρ hρ β ⟨hβ.le, le_max_right _ _⟩
  -- The cross covariance identity and the diagonal identities combine into
  -- the response covariance of the propagated-test increment.
  have hvar : (∫ w, (Dt w - Dv w) ^ 2 ∂P) =
      HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ delta delta +
      HRS.Whole.susceptibilityCov (rieszKernel d s) mu β delta delta := by
    have hsq : (fun w => (Dt w - Dv w) ^ 2) =
        fun w => Dt w ^ 2 + Dv w ^ 2 - 2 * (Dt w * Dv w) := by
      funext w
      ring
    have hIadd : Integrable (fun w => Dt w ^ 2 + Dv w ^ 2) P := hDtI.add hDvI
    rw [hsq, integral_sub hIadd (hcrossI.const_mul 2), integral_const_mul,
      integral_add hDtI hDvI, hDtSq, hDvSq]
    have hcrosseq : (∫ w, Dt w * Dv w ∂P) =
        HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ ft fv +
        HRS.Whole.susceptibilityCov (rieszKernel d s) mu β ft fv := by
      simpa [Dt, Dv, ft, fv, C, mu, psi] using hcross
    rw [hcrosseq]
    have hsubγ := s111x2_susc_sub hK hγ hft hfv
    have hsubβ := s111x2_susc_sub hK hβ.le hft hfv
    have hsymγ := hformγ.symmetry ft fv hft hfv
    have hsymβ := hformβ.symmetry ft fv hft hfv
    have hsubγ' : HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ delta delta =
        HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ ft ft -
          HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ ft fv -
          HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ ft fv +
          HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ fv fv := by
      rw [← hsymγ] at hsubγ
      simpa [mu, C, ft, fv, delta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsubγ
    have hsubβ' : HRS.Whole.susceptibilityCov (rieszKernel d s) mu β delta delta =
        HRS.Whole.susceptibilityCov (rieszKernel d s) mu β ft ft -
          HRS.Whole.susceptibilityCov (rieszKernel d s) mu β ft fv -
          HRS.Whole.susceptibilityCov (rieszKernel d s) mu β ft fv +
          HRS.Whole.susceptibilityCov (rieszKernel d s) mu β fv fv := by
      rw [← hsymβ] at hsubβ
      simpa [mu, C, ft, fv, delta, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsubβ
    rw [hsubγ', hsubβ']
    rw [hsymγ, hsymβ]
    ring
  have hdelta : MemLp delta 2 mu := hft.sub hfv
  have hcovγ := hformγ.coercive delta hdelta
  have hcovβ := hformβ.coercive delta hdelta
  let S : Finset (MultiIndex d) := {alpha}
  have henergy := (hH01 S t v ht0 htv).2
  have hsign : s111x2_centeredSquare mu delta =
      s111x2_centeredSquare mu (fun x => fv x - ft x) := by
    have hdeltaEq : delta = fun x => -(fv x - ft x) := by
      funext x
      simp [delta, ft, fv, C, psi]
    have hIf : Integrable ft mu := hft.integrable (by norm_num)
    have hIg : Integrable fv mu := hfv.integrable (by norm_num)
    have hpairNeg : HRS.Whole.pair mu (fun x => -(fv x - ft x)) =
        -HRS.Whole.pair mu (fun x => fv x - ft x) := by
      unfold HRS.Whole.pair
      rw [integral_neg]
    have hproj : HRS.Whole.projMean mu (fun x => -(fv x - ft x)) =
        -HRS.Whole.projMean mu (fun x => fv x - ft x) := by
      funext x
      simp only [HRS.Whole.projMean]
      rw [Pi.neg_apply]
      simp only [HRS.Whole.projMean]
      rw [hpairNeg]
      ring
    unfold s111x2_centeredSquare
    rw [hdeltaEq, hproj]
    simp
  have henergy' : s111x2_centeredSquare mu delta ≤
      B * (v - t) ^ 2 * Real.exp (-2 * (lam / β) * t) := by
    have hsum : s111x2_centeredSquare mu (fun x => fv x - ft x) ≤
        B * (v - t) ^ 2 * Real.exp (-2 * (lam / β) * t) := by
      simpa [S, psi, mu, HRS.MS.R26T6.r26t6_thermalCoeff, C, fv, ft] using henergy
    rw [hsign]
    exact hsum
  have hbound : HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ delta delta +
      HRS.Whole.susceptibilityCov (rieszKernel d s) mu β delta delta ≤
      2 * s111x2_centeredSquare mu delta := by
    linarith [hcovγ.2, hcovβ.2]
  have hvar' : (∫ w, ((OscDual.eval (Z 0 t w) psi - OscDual.eval (Z 1 t w) psi) -
        (OscDual.eval (Z 0 v w) psi - OscDual.eval (Z 1 v w) psi)) ^ 2 ∂P) =
      HRS.Whole.susceptibilityCov (rieszKernel d s) mu γ delta delta +
        HRS.Whole.susceptibilityCov (rieszKernel d s) mu β delta delta := by
    simpa [Dt, Dv] using hvar
  have hpointvar : (∫ w, ((OscDual.eval (Z 0 t w) psi - OscDual.eval (Z 1 t w) psi) -
      (OscDual.eval (Z 0 v w) psi - OscDual.eval (Z 1 v w) psi)) ^ 2 ∂P) ≤
      2 * s111x2_centeredSquare mu delta := by
    rw [hvar']
    exact hbound
  have hfinal : (∫ w, ((OscDual.eval (Z 0 t w) psi - OscDual.eval (Z 1 t w) psi) -
      (OscDual.eval (Z 0 v w) psi - OscDual.eval (Z 1 v w) psi)) ^ 2 ∂P) ≤
      2 * B * (v - t) ^ 2 * Real.exp (-2 * (lam / β) * t) := by
    rw [hvar']
    calc
      _ ≤ 2 * s111x2_centeredSquare mu delta := hbound
      _ ≤ 2 * (B * (v - t) ^ 2 * Real.exp (-2 * (lam / β) * t)) :=
        mul_le_mul_of_nonneg_left henergy' (show 0 ≤ (2 : ℝ) by norm_num)
      _ = 2 * B * (v - t) ^ 2 * Real.exp (-2 * (lam / β) * t) := by ring
  exact ⟨by simpa [psi, mu, C, hsign] using hpointvar, by simpa [psi, mu, C] using hfinal⟩

/-- At every fixed time, the shared-noise difference has the sharp
fourth-moment decay inherited from its two independent initial components.
The statement applies to any realization of the frozen shared law. -/
theorem fp81v01_difference_observation_moments_decay (hd : 2 ≤ d)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hβ : 0 < β) (hγ : 0 ≤ γ) (hlam : 0 < lam)
    (hρ : IsThermalEquilibrium d s a β ρ)
    (hP : IsR2Poincare (HRS.Whole.withDensityReal ρ) lam)
    (hZ : r26t6_SharedThermalLaw P s a β γ H ρ Z) :
    ∃ A : ℝ, 0 < A ∧ ∀ t ∈ Icc (0 : ℝ) H,
      ∀ phi : Euc d → ℝ, IsOscTest (wholeSpaceIndex d) phi →
      let D : Omega → ℝ := fun w =>
        OscDual.eval (Z 0 t w) phi - OscDual.eval (Z 1 t w) phi
      let V := ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) phi x ^ 2
        ∂HRS.Whole.withDensityReal ρ
      MemLp D 4 P ∧
        (∫ w, D w ^ 2 ∂P) ≤ A * Real.exp (-2 * (lam / β) * t) * V ∧
        (∫ w, D w ^ 4 ∂P) ≤ 3 * A ^ 2 * Real.exp (-4 * (lam / β) * t) * V ^ 2 := by
  obtain ⟨A, hA, hdec⟩ := physical_initial_difference_variance_decay
    hd s a β lam hs0 hs ha hβ hlam
  refine ⟨A, hA, fun t ht phi hphi => ?_⟩
  let mu := HRS.Whole.withDensityReal ρ
  let D : Omega → ℝ := fun w =>
    OscDual.eval (Z 0 t w) phi - OscDual.eval (Z 1 t w) phi
  let f := propagatorW (r26t6_thermalCoeff d s a β ρ) 0 t phi
  let V := ∫ x, HRS.Whole.projMean mu phi x ^ 2 ∂mu
  have hV : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  obtain ⟨hD, hsecond, hfour⟩ := physical_shared_difference_moments
    hd hs0 hs ha hβ hγ hρ hZ ht hphi
  have hbound : (∫ w, D w ^ 2 ∂P) ≤ A * Real.exp (-2 * (lam / β) * t) * V := by
    rw [hsecond]
    exact hdec ρ hρ hP γ hγ t ht.1 phi hphi
  refine ⟨hD, hbound, ?_⟩
  have hexp : Real.exp (-2 * (lam / β) * t) ^ 2 =
      Real.exp (-4 * (lam / β) * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  calc
    (∫ w, D w ^ 4 ∂P) = 3 * (∫ w, D w ^ 2 ∂P) ^ 2 := hfour
    _ ≤ 3 * (A * Real.exp (-2 * (lam / β) * t) * V) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (integral_nonneg fun w => sq_nonneg _) hbound 2) (by norm_num)
    _ = _ := by
      rw [mul_pow, mul_pow, hexp]
      ring

#print axioms fp81v01_difference_observation_moments_decay
#print axioms fp81v01_difference_observation_cross_moment
#print axioms fp81v01_difference_observation_increment_variance_le

end HRS.Fp81.V01
