import HRS.MS.Fp81S21ParticleWindowSup8
import HRS.MS.Fp81S21CenteredAdapter3
import HRS.MS.Fp81S21WindowSup18
import HRS.MS.Fp81S21WindowFeature9
import HRS.MS.Fp81S21ParticleSixthSlices

/-! Uniform bounds for the Bochner mean of a raw particle fluctuation window. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.R2WinErr

/-- The mean path of the raw particle fluctuation has a norm bound uniform in
its window, particle number, realization, and starting time. The scalar input
is the raw linear sixth-slice estimate `fp81s21_particle_sixth_slices`. -/
theorem fp81s21_particle_window_mean_norm_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ Cμ : ℝ, 0 ≤ Cμ ∧
        ∀ H : ℝ, 0 < H → ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∀ b : ℝ, 0 ≤ b →
          ‖∫ ω, flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b
              (Real.sqrt (N : ℝ)) A.X R.ρ ω ∂A.P‖ ≤ Cμ := by
  obtain ⟨δs, hδs, hδsh, hSlices⟩ := fp81s21_particle_sixth_slices p
  obtain ⟨δo, hδo, hδoh, hOrbit⟩ := fp81s21_moving_orbit_gradient_decay p
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  obtain ⟨Kφ, hKφ, htest⟩ := fp81s21_window_test_pos_envelope hd1
  let δ0 := min δs δo
  have hδ0 : 0 < δ0 := lt_min hδs hδo
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδsh
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R
  have hδs' : δ ≤ δs := hδle.trans (min_le_left _ _)
  have hδo' : δ ≤ δo := hδle.trans (min_le_right _ _)
  obtain ⟨Cs, hCs, hSlicesR⟩ := hSlices δ hδ hδs' R
  obtain ⟨_, _, _, _, hsum, _⟩ := hOrbit δ hδ hδo' R
  have hwsq : Summable fun α : MultiIndex p.d => (s104_b p.d α) ^ 2 :=
    HRS.MS.R2GenInit.s105_b_sq_summable hsum
  have hweight : 0 ≤ ∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2 :=
    tsum_nonneg fun α => sq_nonneg (s104_b p.d α)
  let Kμ : ℝ := Cs ^ (1 / 6 : ℝ) * Kφ
  have hKμ : 0 ≤ Kμ := by dsimp [Kμ]; positivity
  let Cμ : ℝ := Kμ * Real.sqrt (∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2)
  have hCμ : 0 ≤ Cμ := by dsimp [Cμ]; positivity
  refine ⟨Cμ, hCμ, ?_⟩
  intro H hH N hN A b hb
  letI : Nonempty (Icc (0 : ℝ) H) := ⟨⟨0, ⟨le_rfl, hH.le⟩⟩⟩
  let T : ℝ := b + H
  have hT : 0 < T := by dsimp [T]; linarith
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let η : A.Ω → OscPath p.d m H := flucPathW m H b
    (Real.sqrt (N : ℝ)) A.X R.ρ
  let ηfield : ℝ → A.Ω → OscDual p.d m := fun t ω =>
    Real.sqrt (N : ℝ) • OscDual.ofMeasureDiff m
      (HRS.Whole.empirical (A.X (Real.toNNReal t) ω))
      (HRS.Whole.withDensityReal (R.ρ t))
  let Mpath : OscPath p.d m H := ∫ ω, η ω ∂A.P
  have hNpos : 0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hm : (p.d : ℝ) < m := by
    dsimp [m, wholeSpaceIndex]
    push_cast
    nlinarith [show (0 : ℝ) ≤ p.d by positivity]
  have hstrong := A.strong T
  have hXm : ∀ t, Measurable (A.X t) := hstrong.adapted
  have hXc : ∀ᵐ ω ∂A.P, ∀ i, Continuous fun t : ℝ≥0 => A.X t ω i := hstrong.cont
  have hprob : ∀ t ∈ Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (R.ρ t) := by
    intro t ht
    exact (R.resulting.global T).density t ht
  have hweak : ∀ ψ : Euc p.d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * R.ρ r x) (Icc (0 : ℝ) T) := by
    intro ψ hψ hbd
    have hβprob : HRS.Whole.IsProbDensity R.ρβ := R.thermal.2.1
    have hβpos : ∀ x, 0 < R.ρβ x := HRS.Whole.S78.s78_thermal_pos R.thermal.2
    exact (HRS.Whole.s21p_rho_weak_cont hβprob hβpos R.resulting ψ hψ hbd).mono
      (fun t ht => ht.1)
  have hηcont : ∀ᵐ ω ∂A.P, ContinuousOn (fun t : ℝ => ηfield t ω) (Icc 0 T) := by
    filter_upwards [hXc] with ω hω
    exact HRS.MS.GenPath.s56_xi_cont_time hd1 hm (Real.sqrt (N : ℝ)) hNpos
      R.ρ hprob hweak (fun t => A.X (Real.toNNReal t) ω)
      (fun i => (hω i).comp continuous_real_toNNReal)
  have hηint : Integrable η A.P := by
    exact (fp81s21_particle_window_centered p R hN A hH hb).1
  have hηeval (τ : Icc (0 : ℝ) H) :
      (fun ω => OscPath.at' (η ω) τ) =ᵐ[A.P] ηfield (b + (τ : ℝ)) := by
    filter_upwards [hηcont] with ω hω
    have hmem : ∀ t : Icc (0 : ℝ) H, b + (t : ℝ) ∈ Icc (0 : ℝ) T := by
      intro t
      constructor
      · change 0 ≤ b + (t : ℝ)
        linarith [hb, t.2.1]
      · change b + (t : ℝ) ≤ b + H
        linarith [t.2.2]
    have hc : Continuous fun t : Icc (0 : ℝ) H => ηfield (b + (t : ℝ)) ω := by
      exact hω.comp_continuous (continuous_const.add continuous_subtype_val) hmem
    have hpath : η ω =
        (⟨fun t : Icc (0 : ℝ) H => ηfield (b + (t : ℝ)) ω, hc⟩ : OscPath p.d m H) := by
      change windowPathOf m H b (fun t => ηfield t ω) = _
      unfold windowPathOf
      exact dif_pos hc
    rw [hpath]
    rfl
  have hXmeas (u : ℝ) : Measurable (A.X (Real.toNNReal u)) := hXm _
  have hcoordBound (τ : Icc (0 : ℝ) H) (α : MultiIndex p.d) :
      |OscDual.coord (OscPath.at' Mpath τ) α| ≤ Kμ * s104_b p.d α := by
    let u : ℝ := b + (τ : ℝ)
    have hu : 0 ≤ u := by dsimp [u]; linarith [hb, τ.2.1]
    have hEval := fp81s21_pathIntegral_eval η
      (HRS.MS.R2Interp.s102_ell τ α) hηint
    have hEval' : OscDual.coord (OscPath.at' Mpath τ) α =
        ∫ ω, OscDual.coord (OscPath.at' (η ω) τ) α ∂A.P := by
      simpa only [HRS.MS.R2Interp.s102_ell_apply] using hEval
    let f : Euc p.d → ℝ := oscTestFun m α
    let μ : Measure (Euc p.d) := HRS.Whole.withDensityReal (R.ρ u)
    let Y : A.Ω → ℝ := fun ω => Real.sqrt (N : ℝ) *
      (HRS.Whole.pair (HRS.Whole.empirical (A.X (Real.toNNReal u) ω)) f -
        HRS.Whole.pair μ f)
    have hf : Measurable f := HRS.MS.GenPath.s56_oscTestFun_cont m α |>.measurable
    have hfb : ∀ x, |f x| ≤ Kφ * s104_b p.d α := by
      intro x
      have hx := htest α 0 (Nat.zero_le _) x
      simpa [f, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hx
    have hB : 0 ≤ Kφ * s104_b p.d α :=
      mul_nonneg hKφ (s104_b_nonneg α)
    have hSlice := hSlicesR N hN A u hu (Kφ * s104_b p.d α) hB
    have hRaw : SixthBound A.P Y (Cs * (Kφ * s104_b p.d α) ^ 6) := by
      simpa [Y, f, μ, HRS.MS.R26T3.r26t3_mu] using hSlice.2 f hf hfb
    have hYmeas : Measurable Y := by
      have hPair : Measurable (fun ω =>
          HRS.Whole.pair (HRS.Whole.empirical (A.X (Real.toNNReal u) ω)) f) :=
        (S45.s45_measurable_pair_empirical hN1 hf).comp (hXmeas u)
      exact measurable_const.mul (hPair.sub_const _)
    have hBudget : 0 ≤ Cs * (Kφ * s104_b p.d α) ^ 6 := by positivity
    have hLp := fp81s21_sixthBound_eLpNorm A.P Y
      (Cs * (Kφ * s104_b p.d α) ^ 6) hYmeas hBudget hRaw
    have hroot : (Cs * (Kφ * s104_b p.d α) ^ 6) ^ (1 / 6 : ℝ) =
        Kμ * s104_b p.d α := by
      rw [fp81s21_real_sixth_root_product hCs hKφ (s104_b_nonneg α)]
    have hLp' : eLpNorm Y (ENNReal.ofReal 6) A.P ≤
        ENNReal.ofReal (Kμ * s104_b p.d α) := by
      calc
        eLpNorm Y (ENNReal.ofReal 6) A.P ≤
            ENNReal.ofReal ((Cs * (Kφ * s104_b p.d α) ^ 6) ^ (1 / 6 : ℝ)) := hLp
        _ = ENNReal.ofReal (Kμ * s104_b p.d α) := by rw [hroot]
    have hYmem : MemLp Y (ENNReal.ofReal 6) A.P := by
      apply (integrable_norm_rpow_iff hYmeas.aestronglyMeasurable
        (by norm_num) (by norm_num)).1
      simpa [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6)] using hRaw.1
    have hYint : Integrable Y A.P := hYmem.integrable (by norm_num)
    have hMeanEnorm : ‖∫ ω, Y ω ∂A.P‖ₑ ≤ eLpNorm Y 1 A.P := by
      calc
        _ ≤ ∫⁻ ω, ‖Y ω‖ₑ ∂A.P := enorm_integral_le_lintegral_enorm Y
        _ = eLpNorm Y 1 A.P := by
          symm
          exact eLpNorm_one_eq_lintegral_enorm hYint.aestronglyMeasurable
    have hMeanAbs : |∫ ω, Y ω ∂A.P| ≤ Kμ * s104_b p.d α := by
      have hmono : eLpNorm Y 1 A.P ≤ eLpNorm Y (ENNReal.ofReal 6) A.P :=
        eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      have hEn : ‖∫ ω, Y ω ∂A.P‖ₑ ≤ ENNReal.ofReal (Kμ * s104_b p.d α) :=
        hMeanEnorm.trans (hmono.trans hLp')
      have hreal : ENNReal.ofReal |∫ ω, Y ω ∂A.P| ≤
          ENNReal.ofReal (Kμ * s104_b p.d α) := by
        simpa [Real.enorm_eq_ofReal_abs] using hEn
      have hKμB : 0 ≤ Kμ * s104_b p.d α := mul_nonneg hKμ (s104_b_nonneg α)
      exact (ENNReal.ofReal_le_ofReal_iff hKμB).1 hreal
    have hRawCoord (ω : A.Ω) : OscDual.coord (ηfield u ω) α = Y ω := by
      letI : IsProbabilityMeasure (HRS.Whole.empirical (A.X (Real.toNNReal u) ω)) :=
        HRS.Whole.empirical_isProbabilityMeasure hNpos _
      letI : IsProbabilityMeasure μ :=
        HRS.MS.Thm.cb_withDensityReal_isProb ((R.resulting.global u).density u ⟨hu, le_rfl⟩)
      change OscDual.coord (Real.sqrt (N : ℝ) •
        OscDual.ofMeasureDiff m (HRS.Whole.empirical (A.X (Real.toNNReal u) ω)) μ) α = Y ω
      rw [OscDual.coord_smul,
        HRS.MS.GenPath.s56_coord_ofMeasureDiff hm _ _ α]
      simp [Y, f, μ, HRS.Whole.pair]
    have hCoordIntegral : OscDual.coord (OscPath.at' Mpath τ) α =
        ∫ ω, Y ω ∂A.P := by
      calc
        _ = ∫ ω, OscDual.coord (OscPath.at' (η ω) τ) α ∂A.P := hEval'
        _ = ∫ ω, OscDual.coord (ηfield u ω) α ∂A.P :=
          integral_congr_ae ((hηeval τ).mono fun ω hω =>
            congrArg (fun z => OscDual.coord z α) hω)
        _ = ∫ ω, Y ω ∂A.P :=
          integral_congr_ae (Filter.Eventually.of_forall hRawCoord)
    rw [hCoordIntegral]
    exact hMeanAbs
  have hDualBound (τ : Icc (0 : ℝ) H) :
      ‖OscPath.at' Mpath τ‖ ≤ Cμ := by
    rw [OscDual.norm_eq_coord]
    have hTargetSum : Summable fun α : MultiIndex p.d =>
        (Kμ * s104_b p.d α) ^ 2 := by
      simpa [mul_pow] using hwsq.mul_left (Kμ ^ 2)
    have hterm (α : MultiIndex p.d) :
        (OscDual.coord (OscPath.at' Mpath τ) α) ^ 2 ≤ (Kμ * s104_b p.d α) ^ 2 := by
      have habs := hcoordBound τ α
      have hnonneg : 0 ≤ Kμ * s104_b p.d α :=
        mul_nonneg hKμ (s104_b_nonneg α)
      have hmul := mul_nonneg (sub_nonneg.mpr habs)
        (add_nonneg (abs_nonneg (OscDual.coord (OscPath.at' Mpath τ) α)) hnonneg)
      nlinarith [sq_abs (OscDual.coord (OscPath.at' Mpath τ) α)]
    have htsum := (OscDual.coord_sq_summable' (OscPath.at' Mpath τ)).tsum_le_tsum
      hterm hTargetSum
    have hsumEq : (∑' α : MultiIndex p.d, (Kμ * s104_b p.d α) ^ 2) =
        Kμ ^ 2 * (∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2) := by
      calc
        _ = ∑' α : MultiIndex p.d, Kμ ^ 2 * (s104_b p.d α) ^ 2 := by
          congr 1
          funext α
          ring
        _ = Kμ ^ 2 * (∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2) := tsum_mul_left
    have hsumNonneg : 0 ≤ ∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2 := hweight
    calc
      Real.sqrt (∑' α : MultiIndex p.d,
          (OscDual.coord (OscPath.at' Mpath τ) α) ^ 2) ≤
          Real.sqrt (∑' α : MultiIndex p.d, (Kμ * s104_b p.d α) ^ 2) :=
        Real.sqrt_le_sqrt htsum
      _ = Kμ * Real.sqrt (∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2) := by
        rw [hsumEq, Real.sqrt_mul (sq_nonneg Kμ), Real.sqrt_sq hKμ]
      _ = Cμ := rfl
  have hPathBound : ‖Mpath‖ ≤ Cμ := by
    rw [OscPath.norm_eq_iSup Mpath hH.le]
    exact ciSup_le fun τ => hDualBound τ
  simpa [η, Mpath, Cμ] using hPathBound

#print axioms HRS.Fp81.S21.fp81s21_particle_window_mean_norm_bound
end HRS.Fp81.S21
end
