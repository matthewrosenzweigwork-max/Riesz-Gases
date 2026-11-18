import HRS.MS.Fp81S21GaussG4U4

/-! Terminal Duhamel formula for each oscillator mode. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.Fp81.S21
open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

/-- The physical scalar Duhamel identity for each oscillator mode, with the
integrability required for the integral explicitly retained. -/
theorem fp81s21_g4_duhamel_mode (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ α : MultiIndex p.d, ∀ r v w : ℝ, 0 ≤ r → r ≤ v → v ≤ w →
      ∀ x : Euc p.d,
        IntegrableOn (fun q => r26t3_U R r q
          (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x)
          (Icc v w) ∧
        r26t3_U R r w (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x -
          r26t3_U R r v (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x =
          ∫ q in Icc v w, r26t3_U R r q
            (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x := by
  obtain ⟨δ0, Co, co, hδ0, hhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R α r v w hr hrv hvw x
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ hδle R.ρβ R.thermal
  let H : ℝ := w + 1
  have hH : 0 < H := by dsimp [H]; linarith
  have hrH : r ∈ Icc (0 : ℝ) H := ⟨hr, by dsimp [H]; linarith⟩
  have hrHlt : r < H := by dsimp [H]; linarith
  let f : ℝ → ℝ := fun q => r26t3_U R r q (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x
  let g : ℝ → ℝ := fun q => r26t3_U R r q
    (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x
  have hder : ∀ q ∈ Icc r H, HasDerivWithinAt f (g q) (Icc r H) q := by
    intro q hq
    simpa [f, g, r26t3_U] using
      fp81s21_moving_terminal_derivative_within p R hH hterm α r hrH q hq hrHlt x
  have hsub : Icc v w ⊆ Icc r H := Icc_subset_Icc hrv (by dsimp [H]; linarith)
  have hc : ContinuousOn f (Icc v w) :=
    (show ContinuousOn f (Icc r H) from fun q hq => (hder q hq).continuousWithinAt).mono hsub
  have horb := s104b_orbit_of_termRegGen hterm R.admissible R.resulting α H hH.le
  have hint : IntegrableOn g (Icc v w) := by
    have hi := (fp81s21_g4_orbit_integrable horb hr hrv hvw (by dsimp [H]; linarith) x).1
    simpa [g, r26t3_U, r26t3_coeff] using hi
  have hft := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hvw hc
    (fun q hq => by
      have hq' : q ∈ Ioo r H := ⟨by linarith [hq.1], by dsimp [H]; linarith [hq.2]⟩
      exact ((hder q ⟨hq'.1.le, hq'.2.le⟩).hasDerivAt
        (Icc_mem_nhds hq'.1 hq'.2)).hasDerivWithinAt)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hvw).2 hint)
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_of_le hvw, ← integral_Icc_eq_integral_Ioc] at hft
  exact hft.symm

/-- Gradient Duhamel identity on a subinterval of any regular orbit. -/
theorem fp81s21_g4_orbit_gradient_duhamel
    {d : ℕ} {C : WholeCoeff d} {f : Euc d → ℝ} {T r v w : ℝ}
    (horb : S104nOrbit C f T) (hr : 0 ≤ r) (hrv : r ≤ v)
    (hvw : v ≤ w) (hwT : w ≤ T) (x : Euc d) :
    IntegrableOn (fun q => gradient (propagatorW C r q (generatorW C q f)) x) (Icc v w) ∧
    gradient (propagatorW C r w f) x - gradient (propagatorW C r v f) x =
      ∫ q in Icc v w, gradient (propagatorW C r q (generatorW C q f)) x := by
  let g : ℝ → Euc d := fun q => gradient (propagatorW C r q (generatorW C q f)) x
  have hirw : IntegrableOn g (Icc r w) :=
    (fp81s21_g4_orbit_integrable horb hr le_rfl (hrv.trans hvw) hwT x).2
  have hirv : IntegrableOn g (Icc r v) := hirw.mono_set (Icc_subset_Icc le_rfl hvw)
  have hivw : IntegrableOn g (Icc v w) := hirw.mono_set (Icc_subset_Icc hrv le_rfl)
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hrv).2 hirv)
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hvw).2 hivw)
  rw [intervalIntegral.integral_of_le hrv, intervalIntegral.integral_of_le hvw,
    intervalIntegral.integral_of_le (hrv.trans hvw), ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hsum
  refine ⟨hivw, ?_⟩
  apply PiLp.ext
  intro a
  have hw := HRS.MS.S104b.s104b_duhamel horb hr (hrv.trans hvw) hwT a x
  have hv := HRS.MS.S104b.s104b_duhamel horb hr hrv (hvw.trans hwT) a x
  have hevalrw := eval_integral_piLp (fun i => hirw.eval_piLp i) a
  have hevalrv := eval_integral_piLp (fun i => hirv.eval_piLp i) a
  have hevalvw := eval_integral_piLp (fun i => hivw.eval_piLp i) a
  have hsumA := congrArg (fun z : Euc d => z a) hsum
  simp only [PiLp.add_apply, hevalrw, hevalrv, hevalvw] at hsumA
  simp only [PiLp.sub_apply, hevalvw]
  change gradient (propagatorW C r w f) x a - gradient (propagatorW C r v f) x a = _
  dsimp [HRS.Whole.gradComp] at hw hv
  dsimp [g] at hsumA ⊢
  linarith [hw.2, hv.2]

/-- Physical gradient Duhamel identity for each oscillator mode. -/
theorem fp81s21_g4_gradient_duhamel_mode (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ α : MultiIndex p.d, ∀ r v w : ℝ, 0 ≤ r → r ≤ v → v ≤ w →
      ∀ x : Euc p.d,
        IntegrableOn (fun q => gradient (r26t3_U R r q
          (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x)
          (Icc v w) ∧
        gradient (r26t3_U R r w (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x -
          gradient (r26t3_U R r v (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x =
          ∫ q in Icc v w, gradient (r26t3_U R r q
            (generatorW (r26t3_coeff R) q (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) x := by
  obtain ⟨δ0, Co, co, hδ0, hhalf, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R α r v w hr hrv hvw x
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ hδle R.ρβ R.thermal
  have hw : 0 ≤ w := hr.trans (hrv.trans hvw)
  have horb := s104b_orbit_of_termRegGen hterm R.admissible R.resulting α w hw
  simpa [r26t3_U, r26t3_coeff] using
    fp81s21_g4_orbit_gradient_duhamel horb hr hrv hvw le_rfl x

#print axioms fp81s21_g4_gradient_duhamel_mode
#print axioms fp81s21_g4_orbit_gradient_duhamel
#print axioms fp81s21_g4_duhamel_mode
end HRS.Fp81.S21
end
