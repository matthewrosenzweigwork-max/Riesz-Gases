import HRS.MS.Fp81S21MovingM1
import HRS.MS.Fp81S21MovingDuality2
import HRS.MS.R2InterpAux10
import HRS.MS.R2InterpAux85
import HRS.MS.R2InterpAux129

/-!
# HRS S2.1(iii), packet 19a-i: continuity of moving orbit coordinates

For rational-grid terminal times (including the full horizon), the moving
centered orbit has continuous paths on its active time interval. The orbit
identity uses the moving reference density at every drift time; the M1 bound
controls its drift primitive, and the filtered Brownian integral has a
continuous version.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MS.FixEq

/-- For every terminal time in the S10.2 rational grid and every Hermite
coordinate, the moving centered orbit `ζ ↦ ζ_N^v(U^{v,t} φ_α)` is almost surely
continuous on `[0,t]`. The horizon-wide moving standing data and physical
inputs are explicit so this statement can be applied under the common-radius
construction. -/
theorem fp81s21_moving_orbit_continuous
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) c hH)
    (hphys : Fp81MovingPhysicalInputs R hN A H) :
    ∀ t ∈ s102_Qset H, ∀ α : MultiIndex p.d,
      ∀ᵐ ω ∂A.P,
        ContinuousOn
          (fun v => s102_zf A.P F.X ω v
            (propagatorW (r26t3_coeff R) v t
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))
          (Icc 0 t) := by
  classical
  have hH0 : 0 ≤ H := hH.le
  have hr : (p.d : ℝ) / 2 + 2 < (2 * p.d + 8 : ℕ) := by
    have hdcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    norm_num [Nat.cast_add, Nat.cast_mul]
    nlinarith
  obtain ⟨Mb, hMb, hMbInt⟩ :=
    fp81s21_moving_M1 p R hH hN A hstd hr hphys
  intro t htQ α
  have htH : t ∈ Icc (0 : ℝ) H := s102_Qset_sub hH0 htQ
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := wholeSpaceIndex p.d
  let φ : Euc p.d → ℝ := oscTestFun m α
  let f : ℝ → Euc p.d → ℝ := fun v => propagatorW C v t φ
  have hf : IsClassicalAdjointW C t φ f :=
    s102_propagator_classical (hstd.hcls α t htH)
  obtain ⟨Bg, hBg⟩ := s102_Ig_bdd hf F.X
  have hPhi : IsProgressiveL2 A.P F.ℱ (s102_Ig f t F.X) :=
    IsProgressiveL2.of_bounded A.P
      (s102_Ig_progressive hf F.filtered.progressive) Bg hBg
  have hItoCont : ∀ ω : A.Ω,
      Continuous (fun v => itoIntegral A.P F.ℱ F.Wc
        (s102_Ig f t F.X) v ω) :=
    (isItoIntegral_itoIntegral F.filtered.brownian hPhi).cont
  have hOrbit :=
    fp81s21_moving_orbit_zeta p R hδ hδh hH hN A F hphys htH α
  filter_upwards [hOrbit, hMb, F.indist] with ω hOrbitω hMbω hIndω
  have hItoω := hItoCont ω
  let bA : ℝ → (Euc p.d → ℝ) → ℝ := fun v g =>
    fp81s21_moving_r2QuadField R A v ω g
  have hb : S102Drift C m H (2 * p.d + 8) ((p.d : ℝ) + 2) bA (Mb ω) := by
    simpa [bA, C, m] using hMbω
  have hmap (v : ℝ≥0) :
      A.P.map (F.X v) = A.P.map (A.X v) := by
    apply Measure.map_congr
    filter_upwards [F.indist] with ω' hω'
    exact hω' v
  have hzfEq (v : ℝ) (g : Euc p.d → ℝ) :
      s102_zf A.P F.X ω v g = s102_zf A.P A.X ω v g := by
    unfold s102_zf
    rw [hIndω v.toNNReal, hmap v.toNNReal]
  have hmeanEq (v : ℝ) (g : Euc p.d → ℝ) :
      (∫ ω', pairEnergy (commutatorKernel p.d p.s (fun x => gradient g x))
        (F.X v.toNNReal ω') (r26t3_mu R v) ∂A.P) =
      ∫ ω', pairEnergy (commutatorKernel p.d p.s (fun x => gradient g x))
        (A.X v.toNNReal ω') (r26t3_mu R v) ∂A.P := by
    apply integral_congr_ae
    filter_upwards [F.indist] with ω' hω'
    rw [hω' v.toNNReal]
  have hquadEq (v : ℝ) (g : Euc p.d → ℝ) :
      r2QuadField p.s (r26t3_mu R v) A.P F.X v ω g =
        r2QuadField p.s (r26t3_mu R v) A.P A.X v ω g := by
    unfold r2QuadField
    rw [hIndω v.toNNReal, hmeanEq v g]
  let gA : ℝ → ℝ := fun v => bA v (f v)
  let gA' : ℝ → ℝ := fun v => -(Real.sqrt N)⁻¹ * gA v
  let gF : ℝ → ℝ := fun v => -(Real.sqrt N)⁻¹ *
    r2QuadField p.s (r26t3_mu R v) A.P F.X v ω (f v)
  have hgEq : gF = gA' := by
    funext v
    simp only [gF, gA', gA, bA, fp81s21_moving_r2QuadField]
    rw [hquadEq v (f v)]
  let Kα : ℝ := s57pC p.d (2 * p.d + 8) ((p.d : ℝ) + 2) * c α
  have hK0 : 0 ≤ Kα :=
    mul_nonneg (s57pC_nonneg _ _ _) (hstd.hD.nonneg α)
  have hMbOn : IntegrableOn (fun v => Mb ω v) (Icc (0 : ℝ) t) :=
    hb.Mb_int.mono_set (Icc_subset_Icc le_rfl htH.2)
  have hgAMeas : AEStronglyMeasurable gA (volume.restrict (Icc (0 : ℝ) t)) := by
    simpa [gA, bA] using hb.meas t htH α
  have hgAInt : IntegrableOn gA (Icc (0 : ℝ) t) := by
    refine Integrable.mono' (hMbOn.mul_const Kα) hgAMeas ?_
    refine (ae_restrict_iff' measurableSet_Icc).2
      (Filter.Eventually.of_forall fun v hv => ?_)
    have hvH : v ∈ Icc (0 : ℝ) H := ⟨hv.1, hv.2.trans htH.2⟩
    have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
      have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
      nlinarith
    have htest := s102_orbit_test
      (C := C) (m := m) (T := H) (r := 2 * p.d + 8)
      (c := c) (Pw := (p.d : ℝ) + 2)
      hP hstd.hD hvH ⟨hv.2, htH.2⟩ α
    have hbound := hb.hM v hvH (f v) htest.1
    have hnorm := htest.2
    have hpoint : |gA v| ≤ Mb ω v * Kα := by
      simpa [gA, bA, f, C, m, Kα, fp81s21_moving_r2QuadField] using
        hbound.trans (mul_le_mul_of_nonneg_left hnorm (hb.Mb_nonneg v))
    exact hpoint
  have hgA'Int : IntegrableOn gA' (Icc (0 : ℝ) t) := by
    change Integrable (fun v => -(Real.sqrt N)⁻¹ * gA v)
      (volume.restrict (Icc (0 : ℝ) t))
    exact hgAInt.const_mul (-(Real.sqrt N)⁻¹)
  have hprimA : ContinuousOn
      (fun τ => ∫ v in Icc (0 : ℝ) τ, gA' v) (Icc (0 : ℝ) t) := by
    have hcont := intervalIntegral.continuousOn_primitive_interval
      (a := (0 : ℝ)) (b := t) (μ := volume) (f := gA') (by
        rwa [uIcc_of_le htH.1])
    rw [uIcc_of_le htH.1] at hcont
    refine hcont.congr fun τ hτ => ?_
    beta_reduce
    rw [intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]
  have hprimF : ContinuousOn
      (fun τ => ∫ v in Icc (0 : ℝ) τ, gF v) (Icc 0 t) := by
    have heq : (fun τ => ∫ v in Icc (0 : ℝ) τ, gF v) =
        fun τ => ∫ v in Icc (0 : ℝ) τ, gA' v := by
      funext τ
      exact setIntegral_congr_fun measurableSet_Icc fun v hv => congrFun hgEq v
    rw [heq]
    exact hprimA
  have hR : ContinuousOn
      (fun τ => s102_zf A.P F.X ω 0 (f 0) +
        (Real.sqrt N * (Real.sqrt (2 * p.β⁻¹) / N)) *
          itoIntegral A.P F.ℱ F.Wc (s102_Ig f t F.X) τ ω +
        ∫ v in Icc (0 : ℝ) τ, gF v) (Icc 0 t) := by
    exact (continuousOn_const.add
      (continuousOn_const.mul hItoω.continuousOn)).add hprimF
  refine hR.congr fun τ hτ => ?_
  simpa [f, C, m, φ, gF] using hOrbitω τ hτ

#print axioms HRS.Fp81.S21.fp81s21_moving_orbit_continuous

end HRS.Fp81.S21

end
