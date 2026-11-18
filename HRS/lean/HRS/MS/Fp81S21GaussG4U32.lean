import HRS.MS.Fp81S21GaussG4U3
import HRS.MS.S111K4ATH
import HRS.MS.ProClosureS111OscOrbitApprox
import HRS.MS.ProClosureS111ChartedOrbits
import HRS.MS.ProClosureS111PhysicalWick
import HRS.MS.MovLinAux7
import HRS.MS.MainRdFieldAux4
import HRS.MS.ThmLog
import HRS.MS.ThmSpec
import HRS.MS.SA12CompB3
import HRS.MS.FixEqP1Aux1

/-!
The Hermite truncations converge in the oscillator norm.  At terminal time
zero the physical oscillator estimate bounds all derivatives through order
two by that norm, and the weighted Sobolev embedding then controls `J`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.FixEq HRS.MS.S111K4AT
open HRS.MS.ProClosureS111 HRS.MS.MovLin HRS.MS.MainRdField

private theorem fp81s21_g4_thermalDensity_equilibrium (p : Parameters) :
    IsThermalEquilibrium p.d p.s p.a p.β (thermalDensity p.d p.s p.a p.β) := by
  have hex : ∃ ρ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρ := by
    by_cases hs : p.s = 0
    · have hex0 : ∃ ρ : Euc p.d → ℝ,
          IsThermalEquilibrium p.d 0 p.a p.β ρ := by
        rcases (HRS.MS.Thm.logThermalDensity_spec_proof (d := p.d)
          p.hd p.a p.β p.ha p.hβ).1 with ⟨ρ, hρ, hbound⟩
        exact ⟨ρ, hρ⟩
      simpa [hs] using hex0
    · have hspos : 0 < p.s := lt_of_le_of_ne p.hs0 (Ne.symm hs)
      have hsd : p.s < (p.d : ℝ) := by
        have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
        linarith [p.hs]
      rcases (HRS.MS.Thm.thermalDensity_spec_proof (d := p.d) (s := p.s)
        p.hd hspos hsd p.a p.β p.ha p.hβ).1 with ⟨ρ, hρ, hbound⟩
      exact ⟨ρ, hρ⟩
  unfold thermalDensity
  rw [dif_pos hex]
  exact hex.choose_spec

/-- Hermite truncation converges in the squared weighted Sobolev cost. -/
theorem fp81s21_g4_cost_approx (p : Parameters) {f : Euc p.d → ℝ}
    (hf : IsR2Test f) :
    Tendsto (fun n => fp81s21_g4_J p.d
      (k4hs (wholeSpaceIndex p.d : ℝ) n f - f)) atTop (𝓝 0) := by
  let m : ℝ := wholeSpaceIndex p.d
  let P : ℝ := 2 * (p.d : ℝ) + 4
  let k : ℕ := 2 * p.d + 9
  have hosc : IsOscTest m f := by
    simpa [m] using r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) hf
  have hthermal : IsThermalEquilibrium p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) := fp81s21_g4_thermalDensity_equilibrium p
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith [p.hs]
  obtain ⟨B, hB, hcb⟩ := physical_oscillator_cb_bound p.hd p.hs0 hsd
    p.ha p.hβ hthermal (H := 0) le_rfl
  have hoscConv := k4at_eta_tendsto m hosc.2
  have hP : (p.d : ℝ) < 2 * P := by
    dsimp [P]
    nlinarith
  have hnormConv : Tendsto
      (fun n => oscNorm m (k4hs m n f - f)) atTop (𝓝 0) := by
    have hnormId (n : ℕ) :
        ‖OscSpace.ofFun m (k4hs m n f) - OscSpace.ofFun m f‖ =
          oscNorm m (k4hs m n f - f) := by
      have hk4 : MemOsc m (k4hs m n f) := (k4hs_osc m n f).2
      have herr : MemOsc m (k4hs m n f - f) :=
        HRS.MS.MovLin.mov2d_memOsc_sub hk4 hosc.2
      rw [← HRS.MS.MovLin.mov2d_ofFun_sub hk4 hosc.2]
      exact OscSpace.norm_ofFun _ herr
    simpa only [hnormId] using hoscConv
  have hmajor : Tendsto (fun n =>
      ((s57pC p.d 2 P * B) * oscNorm m (k4hs m n f - f)) ^ 2)
      atTop (𝓝 0) := by
    have hlinear := hnormConv.const_mul (s57pC p.d 2 P * B)
    simpa using hlinear.pow 2
  have hcost (n : ℕ) : fp81s21_g4_J p.d (k4hs m n f - f) ≤
      ((s57pC p.d 2 P * B) * oscNorm m (k4hs m n f - f)) ^ 2 := by
    have herrOsc : IsOscTest m (k4hs m n f - f) := by
      refine ⟨(k4hs_osc m n f).1.sub hosc.1,
        HRS.MS.MovLin.mov2d_memOsc_sub (k4hs_osc m n f).2 hosc.2⟩
    have hzero := hcb (k4hs m n f - f) herrOsc 0 0 le_rfl le_rfl le_rfl
    have hterminal := sa6_prop_terminal hzero.1
    have hzero' := hzero
    rw [hterminal] at hzero'
    have hmem : MemCb k (k4hs m n f - f) := by
      simpa [k] using hzero'.2.1
    have hcbBound : cbNorm k (k4hs m n f - f) ≤ B *
        oscNorm m (k4hs m n f - f) := by
      simpa [k] using hzero'.2.2
    have hderiv : ∀ j ≤ 2, ∀ x : Euc p.d,
        ‖iteratedFDeriv ℝ j (k4hs m n f - f) x‖ ≤
          cbNorm k (k4hs m n f - f) := by
      intro j hj x
      exact HRS.MH.AdjointRd.Phase2SA12Companions.sa12y_single_le_cb hmem
        (by dsimp [k]; omega) x
    have hcb0 : 0 ≤ cbNorm k (k4hs m n f - f) :=
      (norm_nonneg _).trans (hderiv 0 (by omega) 0)
    have hweighted := s57p_E_le_cb (d := p.d) (r := 2) (P := P)
      hP hcb0 hderiv
    have hreal : (weightedSobolevE 2 P (k4hs m n f - f)).toReal ≤
        s57pC p.d 2 P * cbNorm k (k4hs m n f - f) := by
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hweighted
      rwa [ENNReal.toReal_ofReal
        (mul_nonneg (s57pC_nonneg p.d 2 P) hcb0)] at h
    have hreal' : (weightedSobolevE 2 P (k4hs m n f - f)).toReal ≤
        (s57pC p.d 2 P * B) * oscNorm m (k4hs m n f - f) := by
      calc
        _ ≤ s57pC p.d 2 P * cbNorm k (k4hs m n f - f) := hreal
        _ ≤ s57pC p.d 2 P * (B * oscNorm m (k4hs m n f - f)) :=
          mul_le_mul_of_nonneg_left hcbBound (s57pC_nonneg p.d 2 P)
        _ = _ := by ring
    change (weightedSobolevE 2 P (k4hs m n f - f)).toReal ^ 2 ≤ _
    exact pow_le_pow_left₀ ENNReal.toReal_nonneg hreal' 2
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hmajor
    (fun n => show (0 : ℝ) ≤ fp81s21_g4_J p.d (k4hs m n f - f) from sq_nonneg _)
  intro n
  exact hcost n

#print axioms fp81s21_g4_cost_approx

end HRS.Fp81.S21

