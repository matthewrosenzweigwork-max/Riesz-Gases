import HRS.MS.ProClosureS111PhysicalLinear
import HRS.MS.ProClosureS111OrbitSummable
import HRS.MS.R2WinOrbAux15
import HRS.MS.R26T6CD03

/-!
The complete frozen window-orbit input, produced from the stationary physical
thermal data. All six fields are proved: nonnegative amplitudes, classical
existence, gradient decay, the actual terminal derivative including time zero,
the summable orbit predicate, and linearity on finite oscillator tests.
The decay rate and square-summable amplitudes are selected before the thermal
density, and before any time shift or window length.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R2WinOrb HRS.MS.R26T6 HRS.MS.S111K2

theorem cbNormVecE_order_mono {d j k : ℕ} (hjk : j ≤ k) (f : Euc d → Euc d) :
    cbNormVecE j f ≤ cbNormVecE k f := by
  unfold cbNormVecE
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))

theorem r2OrbitGrad_order_mono {d j k : ℕ} {C : WholeCoeff d}
    {t A c : ℝ} {phi : Euc d → ℝ} (hjk : j ≤ k)
    (h : R2OrbitGrad C k t phi A c) : R2OrbitGrad C j t phi A c := by
  intro f hf v hv
  obtain ⟨hcd, hbd⟩ := h f hf v hv
  exact ⟨hcd.of_le (by exact_mod_cast hjk),
    (cbNormVecE_order_mono hjk _).trans hbd⟩

/-- A physical producer of the entire original `S111k2WindowOrbitInput`. -/
theorem physical_window_orbit_input {d : ℕ} (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ (c0 : ℝ) (b : MultiIndex d → ℝ), 0 < c0 ∧
      Summable (fun alpha => b alpha ^ 2) ∧
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
        S111k2WindowOrbitInput (r26t6_thermalCoeff d s a beta rho)
          (wholeSpaceIndex d) c0 (r26t6_coreOrder d) b := by
  obtain ⟨A, c0, hc0, hsum, hstationary⟩ :=
    s103_stationary hd s hs0 hsd a beta ha hbeta 1 one_pos
  have hr : r26t6_coreOrder d + 1 ≤ 4 * d + 42 := by
    unfold r26t6_coreOrder
    omega
  refine ⟨c0, fun alpha => max A 0 * s103_b d alpha, hc0, ?_, ?_⟩
  · have hb := (stationary_weight_square_summable (by omega : 1 ≤ d)).mul_left
      ((max A 0) ^ 2)
    convert hb using 1
    ext alpha
    ring
  · intro rho hrho
    refine {
      nonneg := fun alpha => mul_nonneg (le_max_right _ _) (s103_b_nonneg alpha)
      classical := fun alpha t ht =>
        physical_classical_orbits hd hs0 hsd ha hbeta hrho alpha ht
      grad := ?_
      terminal_derivative := fun alpha v t hv hvt x =>
        physical_terminal_derivative hd hs0 hsd ha hbeta hrho alpha hv hvt x
      orbit := fun H hH =>
        physical_orbit_summable hd hs0 hsd ha hbeta hrho H hH (r26t6_coreOrder d) hr
      linear := fun v t hv hvt phi psi c hphi hpsi =>
        physical_propagator_linear hd hs0 hsd ha hbeta hrho v t hv hvt phi psi c hphi hpsi
    }
    intro alpha t ht
    obtain ⟨hsup0, hgrad0, hsup1, hgrad1, hsup2⟩ := (hstationary rho hrho alpha).1 t ht
    have hm : A * s103_b d alpha ≤ max A 0 * s103_b d alpha :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (s103_b_nonneg alpha)
    exact ⟨r2OrbitGrad_order_mono (by omega) (s103_orbitGrad_mono hgrad0 hm),
      r2OrbitGrad_order_mono (by omega) (s103_orbitGrad_mono hgrad1 hm)⟩

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_window_orbit_input
