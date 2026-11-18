import HRS.MS.Fp81S21WindowSup53

/-! Physical drift supremum on a shifted window. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

/-- Sixth-root lower-integral bound for the shifted-window quadratic drift.
No measurability of the path supremum is asserted. -/
theorem fp81s21_window_drift_sup_sixth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ H : ℝ, 0 < H → ∀ N : ℕ, 2 ≤ N →
      ∀ A : Particle R N, ∀ b : ℝ, 0 ≤ b → ∀ α : MultiIndex p.d,
      (∫⁻ ω, (⨆ t : Icc b (b + H), ENNReal.ofReal
        |∫ v in b..(t : ℝ), r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v t
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α))|) ^ (6 : ℝ) ∂A.P) ^
        (1 / 6 : ℝ) ≤ ENNReal.ofReal (C * (H + H ^ 2) * s104_b p.d α) := by
  obtain ⟨δa, hδa, hδah, hFTC⟩ := fp81s21_window_mode_quad_frozen_ftc p
  obtain ⟨δb, hδb, hδbh, hSlices⟩ := fp81s21_window_quad_slices_sixth_root p
  obtain ⟨δc, hδc, hδch, hKernel⟩ := fp81s21_window_terminal_kernel_envelopes p
  obtain ⟨δd, Co, co, hδd, hδdh, hco, hCommon⟩ := fp81s21_common_radius p
  let δ0 := min δa (min δb (min δc δd))
  have hδ0 : 0 < δ0 := lt_min hδa (lt_min hδb (lt_min hδc hδd))
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδah
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R
  have hδa' : δ ≤ δa := hδle.trans (min_le_left _ _)
  have hδb' : δ ≤ δb := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδc' : δ ≤ δc := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδd' : δ ≤ δd := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0h
  obtain ⟨C, hC, hMoment⟩ := hSlices δ hδ hδb' R
  obtain ⟨B, hB, hEn⟩ := hKernel δ hδ hδc' R
  obtain ⟨_, _, hTerm, _⟩ := hCommon δ hδ hδd' R.ρβ R.thermal
  refine ⟨C, hC, ?_⟩
  intro H hH N hN A b hb α
  let T : ℝ := b + H
  have hT : 0 < T := by dsimp [T]; linarith
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let W : WholeCoeff p.d := r26t3_coeff R
  have horb : S104nOrbit W φ T :=
    s104b_orbit_of_termRegGen hTerm R.admissible R.resulting α T hT.le
  have hdiag (v : ℝ) (hv : v ∈ Icc (0 : ℝ) T) : propagatorW W v v φ = φ :=
    (HRS.MS.Fcau.propagatorW_isClassical (horb.ex0 v hv)).terminal
  have hkernel : Measurable (fun z : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s (gradient φ) z.1 z.2) := by
    have h := (hEn 0 0 le_rfl le_rfl α).1
    have hd := hdiag 0 ⟨le_rfl, hT.le⟩
    change IsBoundedPairKernel p.s _ (commutatorKernel p.d p.s
      (gradient (propagatorW W 0 0 φ))) at h
    rw [hd] at h
    exact h.measurable
  obtain ⟨Q, hQ, hQe, hQzero⟩ :=
    fp81s21_baseline_quad_zero_extension p R hδ hδhalf hT A φ hkernel
  obtain ⟨K, hK, hKe, hKzero⟩ :=
    fp81s21_terminal_quad_zero_extension p R hδ hδhalf hT A φ horb
  let q : ℝ → A.Ω → ℝ := fun v ω => Q (v, ω)
  let k : ℝ × ℝ → A.Ω → ℝ := fun z ω => K (z, ω)
  let Z : ℝ → ℝ → A.Ω → ℝ := fun v t ω =>
    r2QuadField p.s (r26t3_mu R v) A.P A.X v ω (propagatorW W v t φ)
  let L : ℝ := C * s104_b p.d α
  have hL : 0 ≤ L := mul_nonneg hC (s104_b_nonneg α)
  have hq : Measurable (Function.uncurry q) := hQ
  have hk : Measurable (Function.uncurry k) := hK
  have hRep : ∀ᵐ ω ∂A.P, ∀ v t, b ≤ v → v ≤ t → t ≤ b + H →
      Z v t ω = q v ω + ∫ u in (0 : ℝ)..(t - v), k (v, v + u) ω := by
    filter_upwards [hQe, hKe] with ω hqω hkω v t hbv hvt htT
    have hv : 0 ≤ v := hb.trans hbv
    have hvT : v ≤ T := hvt.trans (by simpa [T] using htT)
    have ht' : t ≤ T := by simpa [T] using htT
    have hτ : t - v ∈ Icc (0 : ℝ) (T - v) := by constructor <;> linarith
    have hf := hFTC δ hδ hδa' R N hN A T v hv hvT α (t - v) hτ ω
    have he : (∫ u in (0 : ℝ)..(t - v), k (v, v + u) ω) =
        ∫ u in (0 : ℝ)..(t - v), r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW W v (v + u) (generatorW W (v + u) φ)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu' : u ∈ Icc (0 : ℝ) (t - v) := by
        simpa [uIcc_of_le (sub_nonneg.mpr hvt)] using hu
      exact hkω v (v + u) hv (by linarith [hu'.1]) (by linarith [hu'.2, ht'])
    rw [he]
    have hqeq : q v ω = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ :=
      hqω v ⟨hv, hvT⟩
    rw [hqeq]
    simpa only [Z, W, φ, add_sub_cancel] using hf
  have hqBound : ∀ v, (∫⁻ ω, ENNReal.ofReal |q v ω| ^ (6 : ℝ) ∂A.P) ^
      (1 / 6 : ℝ) ≤ ENNReal.ofReal L := by
    intro v
    by_cases hv : v ∈ Icc (0 : ℝ) T
    · have he : (fun ω => ENNReal.ofReal |q v ω| ^ (6 : ℝ)) =ᵐ[A.P]
          (fun ω => ENNReal.ofReal |r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ| ^ (6 : ℝ)) := by
        filter_upwards [hQe] with ω hω
        rw [show q v ω = _ from hω v hv]
      rw [lintegral_congr_ae he]
      have hm := (hMoment N hN A v v hv.1 le_rfl α).1
      rw [show propagatorW (r26t3_coeff R) v v (oscTestFun (wholeSpaceIndex p.d : ℝ) α) = φ from hdiag v hv] at hm
      exact hm
    · have hz : ∀ ω, q v ω = 0 := fun ω => hQzero (v, ω) hv
      simp [hz, L, hL]
  have hkBound : ∀ z, (∫⁻ ω, ENNReal.ofReal |k z ω| ^ (6 : ℝ) ∂A.P) ^
      (1 / 6 : ℝ) ≤ ENNReal.ofReal L := by
    intro z
    by_cases hz : 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ T
    · have he : (fun ω => ENNReal.ofReal |k z ω| ^ (6 : ℝ)) =ᵐ[A.P]
          (fun ω => ENNReal.ofReal |r2QuadField p.s (r26t3_mu R z.1) A.P A.X z.1 ω
            (propagatorW W z.1 z.2 (generatorW W z.2 φ))| ^ (6 : ℝ)) := by
        filter_upwards [hKe] with ω hω
        rw [show k z ω = _ from hω z.1 z.2 hz.1 hz.2.1 hz.2.2]
      rw [lintegral_congr_ae he]
      exact (hMoment N hN A z.1 z.2 hz.1 hz.2.1 α).2
    · have he : ∀ ω, k z ω = 0 := fun ω => hKzero (z, ω) hz
      simp [he, L, hL]
  have hResult := fp81s21_window_frozen_drift_sup_of_slices A.P b H L hH.le hL
    Z q k hq hk hRep hqBound hkBound
  have heq : L * (H + H ^ 2) = C * (H + H ^ 2) * s104_b p.d α := by dsimp [L]; ring
  simpa only [Z, W, φ, heq] using hResult

#print axioms fp81s21_window_drift_sup_sixth
end HRS.Fp81.S21
end
