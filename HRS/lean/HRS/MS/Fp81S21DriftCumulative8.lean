import HRS.MS.Fp81S21DriftCumulative5
import HRS.MS.Fp81S21WindowSup47
import HRS.MS.Fp81S21MovingMeas
import HRS.MS.R2InterpAux96

/-! Jointly measurable versions of the physical orbit coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- For each observation time and oscillator mode, the actual moving drift
orbit has a jointly measurable sample/time version on its physical interval. -/
theorem fp81s21_moving_drift_orbit_joint_version
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (A : Particle R N) {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r c hH)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) H) (α : MultiIndex p.d) :
    ∃ G : ℝ × A.Ω → ℝ, Measurable G ∧
      ∀ᵐ ω ∂A.P, ∀ u ∈ Icc (0 : ℝ) t,
        G (u, ω) = r2QuadField p.s (r26t3_mu R u) A.P A.X u ω
          (propagatorW (r26t3_coeff R) u t (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) := by
  let S := Icc (0 : ℝ) t
  let ρ : S → Euc p.d → ℝ := fun u x => R.ρ u.1 x
  have hρ : Measurable (fun z : S × Euc p.d => ρ z.1 z.2) :=
    fp81s21_moving_density_joint_meas p R hδ hδh
  have hρ0 : ∀ u x, 0 ≤ ρ u x := by
    intro u x
    exact ((R.resulting.global H).density u.1 ⟨u.2.1, u.2.2.trans ht.2⟩).nonneg x
  obtain ⟨K, B, hK, hKe, hKb⟩ :=
    s102_kernel_pkg p.hs0 (s102_propagator_classical (hstd.hcls α t ht))
  let k : S → Euc p.d → Euc p.d → ℝ := fun u => K u.1
  have hk : Measurable (fun z : S × Euc p.d × Euc p.d => k z.1 z.2.1 z.2.2) :=
    hK.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨g, hg, hge⟩ := fp81s21_param_centered_pairEnergy_particle_modification
    A.P A.X (fun u => (A.strong H).adapted u) (A.strong H).cont
    (fun u : S => (u : ℝ)) measurable_subtype_coe ρ k hρ hρ0 hk
  obtain ⟨G, hG, hGe, -⟩ := fp81s21_param_measurable_zero_extension measurableSet_Icc g hg
  refine ⟨G, hG, ?_⟩
  filter_upwards [hge] with ω hω u hu
  let z : S := ⟨u, hu⟩
  rw [hGe z ω, hω z]
  simp only [k, z, ρ, r2QuadField, r26t3_mu, hKe u hu]

/-- Each scalar coordinate integral has an almost-everywhere measurable
sample section, including all admissible cumulative and observation times. -/
theorem fp81s21_moving_drift_orbit_integral_aemeasurable
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 < H)
    {N : ℕ} (A : Particle R N) {r : ℕ} {c : MultiIndex p.d → ℝ}
    (hstd : Fp81MovingStd (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H r c hH)
    (v t : ℝ) (hv : 0 ≤ v) (ht : t ∈ Icc (0 : ℝ) H) (α : MultiIndex p.d) :
    AEMeasurable (fun ω => ∫ u in Ioc (0 : ℝ) (min v t),
      r2QuadField p.s (r26t3_mu R u) A.P A.X u ω
        (propagatorW (r26t3_coeff R) u t (oscTestFun (wholeSpaceIndex p.d : ℝ) α))) A.P := by
  obtain ⟨G, hG, hGe⟩ := fp81s21_moving_drift_orbit_joint_version p R hδ hδh hH A hstd t ht α
  have hmeas : Measurable (fun ω => ∫ u in Ioc (0 : ℝ) (min v t), G (u, ω)) :=
    ((hG.comp measurable_swap).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (min v t)))).measurable
  apply hmeas.aemeasurable.congr
  filter_upwards [hGe] with ω hω
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  exact hω u ⟨hu.1.le, hu.2.trans (min_le_right _ _)⟩

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_orbit_joint_version
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_orbit_integral_aemeasurable
