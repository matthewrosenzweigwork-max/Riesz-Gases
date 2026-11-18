import HRS.MS.Fp81S21ParticleWindowSup10

/-! Packet 10i: identify the actual continuous particle window paths with the
physical-time suprema, then transfer both sixth-moment bounds to the path laws. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.R2WinErr

private theorem fp81s21_iSup_shift_window {b H : ℝ} (hH : 0 ≤ H)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Icc b (b + H))) :
    (⨆ τ : Icc (0 : ℝ) H, f (b + (τ : ℝ))) =
      ⨆ t : Icc b (b + H), f (t : ℝ) := by
  letI : Nonempty (Icc (0 : ℝ) H) := ⟨⟨0, ⟨le_rfl, hH⟩⟩⟩
  letI : Nonempty (Icc b (b + H)) := ⟨⟨b, ⟨le_rfl, by linarith⟩⟩⟩
  have hBdd : BddAbove (Set.range fun t : Icc b (b + H) => f (t : ℝ)) := by
    have hc : IsCompact ((fun t : ℝ => f t) '' Icc b (b + H)) :=
      isCompact_Icc.image_of_continuousOn hf
    have hrange : Set.range (fun t : Icc b (b + H) => f (t : ℝ)) =
        (fun t : ℝ => f t) '' Icc b (b + H) := by
      ext y
      simp only [Set.mem_range, Set.mem_image, Subtype.exists]
      tauto
    rw [hrange]
    exact hc.bddAbove
  have hBddShift : BddAbove (Set.range fun τ : Icc (0 : ℝ) H => f (b + (τ : ℝ))) := by
    apply hBdd.mono
    rintro y ⟨τ, rfl⟩
    refine ⟨⟨b + (τ : ℝ), ⟨by linarith [τ.2.1], by linarith [τ.2.2]⟩⟩, rfl⟩
  apply le_antisymm
  · refine ciSup_le fun τ => ?_
    let t : Icc b (b + H) := ⟨b + (τ : ℝ), ⟨by linarith [τ.2.1], by linarith [τ.2.2]⟩⟩
    have ht : (t : ℝ) = b + (τ : ℝ) := rfl
    rw [← ht]
    exact le_ciSup hBdd t
  · refine ciSup_le fun t => ?_
    let τ : Icc (0 : ℝ) H := ⟨(t : ℝ) - b, ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩
    have ht : b + (τ : ℝ) = (t : ℝ) := by dsimp [τ]; ring
    rw [← ht]
    exact le_ciSup hBddShift τ

/-- On one full-measure event, both actual window paths take the continuous
branch of `windowPathOf`; their path norms are the corresponding physical
suprema. These are the explicit `iSup` forms of the packet's `windowSup`. -/
theorem fp81s21_particle_window_path_norm_identities
    (p : Parameters) {δ H b : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N) (hH : 0 < H) (hb : 0 ≤ b) :
    (fun ω => ‖flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b
        (Real.sqrt (N : ℝ)) A.X R.ρ ω‖) =ᵐ[A.P]
      (fun ω => ⨆ t : Icc b (b + H),
        ‖fp81s21_particleEta p R A (t : ℝ) ω‖) ∧
    (fun ω => ‖zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b A.P A.X ω‖) =ᵐ[A.P]
      (fun ω => ⨆ t : Icc b (b + H),
        ‖fp81s21_particleZeta p R A (t : ℝ) ω‖) := by
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let η : A.Ω → OscPath p.d m H :=
    flucPathW m H b (Real.sqrt (N : ℝ)) A.X R.ρ
  let ζ : A.Ω → OscPath p.d m H := zetaPathW m H b A.P A.X
  let ηfield : ℝ → A.Ω → OscDual p.d m := fun t ω =>
    HRS.Whole.etaB m (A.X (Real.toNNReal t) ω)
      (HRS.Whole.withDensityReal (R.ρ t))
  let ζfield : ℝ → A.Ω → OscDual p.d m := fun t ω =>
    HRS.Whole.zetaB m (A.P.map (A.X (Real.toNNReal t)))
      (A.X (Real.toNNReal t) ω)
  have hNpos : 0 < N := by omega
  have hN1 : 1 ≤ N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hm : (p.d : ℝ) < m := by
    dsimp [m, wholeSpaceIndex]
    push_cast
    nlinarith [show (0 : ℝ) ≤ p.d by positivity]
  have hT : 0 < b + H := by linarith
  have hstrong := A.strong (b + H)
  have hXm : ∀ t, Measurable (A.X t) := hstrong.adapted
  have hXc : ∀ᵐ ω ∂A.P, ∀ i, Continuous fun t : ℝ≥0 => A.X t ω i := hstrong.cont
  have hprob : ∀ t ∈ Icc (0 : ℝ) (b + H), HRS.Whole.IsProbDensity (R.ρ t) := by
    intro t ht
    exact (R.resulting.global (b + H)).density t ht
  have hweak : ∀ ψ : Euc p.d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * R.ρ r x) (Icc (0 : ℝ) (b + H)) := by
    intro ψ hψ hbd
    have hβprob : HRS.Whole.IsProbDensity R.ρβ := R.thermal.2.1
    have hβpos : ∀ x, 0 < R.ρβ x := HRS.Whole.S78.s78_thermal_pos R.thermal.2
    exact (HRS.Whole.s21p_rho_weak_cont hβprob hβpos R.resulting ψ hψ hbd).mono
      (fun t ht => ht.1)
  have hηcont : ∀ᵐ ω ∂A.P,
      ContinuousOn (fun t : ℝ => ηfield t ω) (Icc 0 (b + H)) := by
    filter_upwards [hXc] with ω hω
    exact HRS.MS.GenPath.s56_xi_cont_time hd1 hm (Real.sqrt (N : ℝ)) hNpos
      R.ρ hprob hweak (fun t => A.X (Real.toNNReal t) ω)
      (fun i => (hω i).comp continuous_real_toNNReal)
  have hζcont : ∀ᵐ ω ∂A.P, Continuous (fun t : ℝ => ζfield t ω) :=
    HRS.Whole.s21e_zeta_cont_time hd1 hNpos hm A.P A.X hXm hXc
  have hηeval : ∀ᵐ ω ∂A.P, ∀ τ : Icc (0 : ℝ) H,
      OscPath.at' (η ω) τ = ηfield (b + (τ : ℝ)) ω := by
    filter_upwards [hηcont] with ω hω
    intro τ
    have hmem : ∀ t : Icc (0 : ℝ) H, b + (t : ℝ) ∈ Icc (0 : ℝ) (b + H) := by
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
  have hζeval : ∀ᵐ ω ∂A.P, ∀ τ : Icc (0 : ℝ) H,
      OscPath.at' (ζ ω) τ = ζfield (b + (τ : ℝ)) ω := by
    filter_upwards [hζcont] with ω hω
    intro τ
    have hc : Continuous fun t : Icc (0 : ℝ) H => ζfield (b + (t : ℝ)) ω :=
      hω.comp (continuous_const.add continuous_subtype_val)
    have hpath : ζ ω =
        (⟨fun t : Icc (0 : ℝ) H => ζfield (b + (t : ℝ)) ω, hc⟩ : OscPath p.d m H) := by
      change windowPathOf m H b (fun t => ζfield t ω) = _
      unfold windowPathOf
      exact dif_pos hc
    rw [hpath]
    rfl
  have hηnorm : ∀ᵐ ω ∂A.P,
      ‖η ω‖ = ⨆ t : Icc b (b + H), ‖ηfield (t : ℝ) ω‖ := by
    filter_upwards [hηeval, hηcont] with ω heval hω
    calc
      ‖η ω‖ = ⨆ τ : Icc (0 : ℝ) H, ‖OscPath.at' (η ω) τ‖ :=
        OscPath.norm_eq_iSup (η ω) hH.le
      _ = ⨆ τ : Icc (0 : ℝ) H, ‖ηfield (b + (τ : ℝ)) ω‖ := by
        apply iSup_congr
        intro τ
        rw [heval τ]
      _ = ⨆ t : Icc b (b + H), ‖ηfield (t : ℝ) ω‖ :=
        fp81s21_iSup_shift_window hH.le (fun t => ‖ηfield t ω‖)
          (hω.norm.mono fun t ht => ⟨by linarith [hb, ht.1], ht.2⟩)
  have hζnorm : ∀ᵐ ω ∂A.P,
      ‖ζ ω‖ = ⨆ t : Icc b (b + H), ‖ζfield (t : ℝ) ω‖ := by
    filter_upwards [hζeval, hζcont] with ω heval hω
    calc
      ‖ζ ω‖ = ⨆ τ : Icc (0 : ℝ) H, ‖OscPath.at' (ζ ω) τ‖ :=
        OscPath.norm_eq_iSup (ζ ω) hH.le
      _ = ⨆ τ : Icc (0 : ℝ) H, ‖ζfield (b + (τ : ℝ)) ω‖ := by
        apply iSup_congr
        intro τ
        rw [heval τ]
      _ = ⨆ t : Icc b (b + H), ‖ζfield (t : ℝ) ω‖ :=
        fp81s21_iSup_shift_window hH.le (fun t => ‖ζfield t ω‖)
          hω.continuousOn.norm
  constructor
  · filter_upwards [hηnorm] with ω hω
    simpa [η, ηfield, fp81s21_particleEta, m] using hω
  · filter_upwards [hζnorm] with ω hω
    simpa [ζ, ζfield, fp81s21_particleZeta, m] using hω

/-- The actual particle paths have explicit measurable modifications, namely
`AEMeasurable.mk` applied to their path-valued random variables. Consumers such
as `fp81_s21_lift_total'`, whose function arguments are required to be
`Measurable`, should use these modifications and the returned ae equalities. -/
theorem fp81s21_particle_window_path_measurable_modifications
    (p : Parameters) {δ H b : ℝ} (R : Trajectory p δ) {N : ℕ}
    (hN : 2 ≤ N) (A : Particle R N) (hH : 0 < H) (hb : 0 ≤ b) :
    ∃ ηm ζm : A.Ω → OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H,
      Measurable ηm ∧ Measurable ζm ∧
      (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b
        (Real.sqrt (N : ℝ)) A.X R.ρ) =ᵐ[A.P] ηm ∧
      (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b A.P A.X) =ᵐ[A.P] ζm := by
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let η : A.Ω → OscPath p.d m H :=
    flucPathW m H b (Real.sqrt (N : ℝ)) A.X R.ρ
  let ζ : A.Ω → OscPath p.d m H := zetaPathW m H b A.P A.X
  have hcenter := fp81s21_particle_window_centered p R hN A hH hb
  have hη : AEMeasurable η A.P := by
    simpa [η, m] using hcenter.1.aemeasurable
  let Mpath : OscPath p.d m H := ∫ ω, η ω ∂A.P
  have hζ : AEMeasurable ζ A.P := by
    have hrel : ζ =ᵐ[A.P] fun ω => η ω - Mpath := by
      simpa [ζ, η, Mpath, m] using hcenter.2
    exact (hη.sub_const Mpath).congr hrel.symm
  refine ⟨hη.mk η, hζ.mk ζ, hη.measurable_mk, hζ.measurable_mk, ?_, ?_⟩
  · simpa [η, m] using hη.ae_eq_mk
  · simpa [ζ, m] using hζ.ae_eq_mk

private theorem fp81s21_moment6_of_ae_path_norm
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E]
    (P : Measure Ω) (Y : Ω → E) (S : Ω → ℝ) (M : ℝ)
    (hY : AEMeasurable Y P)
    (hS : fp81s21_Moment6 P S M)
    (hSnonneg : ∀ ω, 0 ≤ S ω)
    (hNorm : (fun ω => ‖Y ω‖) =ᵐ[P] S) :
    fp81s21_Moment6 P Y M := by
  have hpow : (fun ω => ‖Y ω‖ ^ 6) =ᵐ[P]
      (fun ω => ‖S ω‖ ^ 6) := by
    filter_upwards [hNorm] with ω hω
    calc
      ‖Y ω‖ ^ 6 = S ω ^ 6 := by rw [hω]
      _ = ‖S ω‖ ^ 6 := by rw [Real.norm_eq_abs, abs_of_nonneg (hSnonneg ω)]
  refine ⟨hY, hS.2.1.congr hpow.symm, ?_⟩
  calc
    (∫ ω, ‖Y ω‖ ^ 6 ∂P) = ∫ ω, ‖S ω‖ ^ 6 ∂P := integral_congr_ae hpow
    _ ≤ M := hS.2.2

private theorem fp81s21_sup_moment_mono
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [MeasurableSpace E]
    (P : Measure Ω) (S : Ω → E)
    {M₁ M₂ : ℝ} (hM : M₁ ≤ M₂)
    (hS : fp81s21_Moment6 P S M₁) : fp81s21_Moment6 P S M₂ :=
  ⟨hS.1, hS.2.1, hS.2.2.trans hM⟩

/-- Combined centered and raw particle window supremum moments under the
packet-10 public contract name. -/
theorem fp81s21_particle_window_sup_sixth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ H : ℝ, 0 < H → ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∀ b : ℝ, 0 ≤ b →
          fp81s21_Moment6 A.P
            (fun ω => ⨆ t : Icc b (b + H),
              ‖fp81s21_particleEta p R A (t : ℝ) ω‖)
            ((C * ((1 + Real.sqrt H) ^ 3 +
              (Real.sqrt (N : ℝ))⁻¹ * (H + H ^ 2))) ^ 6) ∧
          fp81s21_Moment6 A.P
            (fun ω => ⨆ t : Icc b (b + H),
              ‖fp81s21_particleZeta p R A (t : ℝ) ω‖)
            ((C * ((1 + Real.sqrt H) ^ 3 +
              (Real.sqrt (N : ℝ))⁻¹ * (H + H ^ 2))) ^ 6) := by
  obtain ⟨δζ, hδζ, hδζh, hCentered⟩ := fp81s21_particle_window_sup_sixth_centered p
  obtain ⟨δη, hδη, hδηh, hRaw⟩ := fp81s21_particle_window_sup_raw_sixth p
  let δ0 := min δζ δη
  have hδ0 : 0 < δ0 := lt_min hδζ hδη
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδζh
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cζ, hCζ, hCenteredR⟩ :=
    hCentered δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨Cη, hCη, hRawR⟩ :=
    hRaw δ hδ (hδle.trans (min_le_right _ _)) R
  let C := Cζ + Cη
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro H hH N hN A b hb
  let q : ℝ := (Real.sqrt (N : ℝ))⁻¹
  let Q : ℝ := H + H ^ 2
  let B : ℝ := (1 + Real.sqrt H) ^ 3 + q * Q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCζle : Cζ ≤ C := by dsimp [C]; linarith [hCη]
  have hCηle : Cη ≤ C := by dsimp [C]; linarith [hCζ]
  have hBudgetζ :
      (Cζ * ((1 + Real.sqrt H) ^ 3 + q * Q)) ^ 6 ≤
        (C * ((1 + Real.sqrt H) ^ 3 + q * Q)) ^ 6 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hCζle hB
  have hBudgetη :
      (Cη * ((1 + Real.sqrt H) ^ 3 + q * Q)) ^ 6 ≤
        (C * ((1 + Real.sqrt H) ^ 3 + q * Q)) ^ 6 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right hCηle hB
  have hζ := hCenteredR H hH N hN A b hb
  have hη := hRawR H hH N hN A b hb
  refine ⟨fp81s21_sup_moment_mono A.P _ hBudgetη hη,
    fp81s21_sup_moment_mono A.P _ hBudgetζ hζ⟩

#print axioms HRS.Fp81.S21.fp81s21_particle_window_path_norm_identities
#print axioms HRS.Fp81.S21.fp81s21_particle_window_path_measurable_modifications
/-! The actual path-valued sixth moments used by the packet-10 lifting
consumer. `fp81s21_particle_window_path_measurable_modifications` supplies
measurable representatives for consumers that require actual `Measurable`
maps, including `fp81_s21_lift_total'`. -/
theorem fp81s21_particle_sixth_windows (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ H : ℝ, 0 < H →
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∀ b : ℝ, 0 ≤ b →
          fp81s21_Moment6 A.P
            (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b
              (Real.sqrt (N : ℝ)) A.X R.ρ) M ∧
          fp81s21_Moment6 A.P
            (zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b A.P A.X) M := by
  obtain ⟨δ0, hδ0, hδ0h, hCombined⟩ :=
    fp81s21_particle_window_sup_sixth p
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R H hH
  obtain ⟨C, hC, hCombinedR⟩ := hCombined δ hδ hδle R
  let M := (C * ((1 + Real.sqrt H) ^ 3 + H + H ^ 2)) ^ 6
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro N hN A b hb
  have hSup := hCombinedR H hH N hN A b hb
  have hN1 : 1 ≤ N := by omega
  have hN1R : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hsqrt : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hN1R
  have hq : (Real.sqrt (N : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hsqrt
  have hQ : 0 ≤ H + H ^ 2 := by positivity
  have hbudgetBase :
      (1 + Real.sqrt H) ^ 3 + (Real.sqrt (N : ℝ))⁻¹ * (H + H ^ 2) ≤
        (1 + Real.sqrt H) ^ 3 + H + H ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hq hQ]
  have hbudget :
      (C * ((1 + Real.sqrt H) ^ 3 +
        (Real.sqrt (N : ℝ))⁻¹ * (H + H ^ 2))) ^ 6 ≤ M := by
    dsimp [M]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_left hbudgetBase hC
  let η : A.Ω → OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H :=
    flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b
      (Real.sqrt (N : ℝ)) A.X R.ρ
  let ζ : A.Ω → OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H :=
    zetaPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b A.P A.X
  have hcenter := fp81s21_particle_window_centered p R hN A hH hb
  have hηmeas : AEMeasurable η A.P := by
    simpa [η] using hcenter.1.aemeasurable
  let Mpath : OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H :=
    ∫ ω, η ω ∂A.P
  have hζmeas : AEMeasurable ζ A.P := by
    have hrel : ζ =ᵐ[A.P] fun ω => η ω - Mpath := by
      simpa [ζ, η, Mpath] using hcenter.2
    exact (hηmeas.sub_const Mpath).congr hrel.symm
  obtain ⟨hηnorm, hζnorm⟩ :=
    fp81s21_particle_window_path_norm_identities p R hN A hH hb
  let Sη : A.Ω → ℝ := fun ω =>
    ⨆ t : Icc b (b + H), ‖fp81s21_particleEta p R A (t : ℝ) ω‖
  let Sζ : A.Ω → ℝ := fun ω =>
    ⨆ t : Icc b (b + H), ‖fp81s21_particleZeta p R A (t : ℝ) ω‖
  have hSη : ∀ ω, 0 ≤ Sη ω := by
    intro ω
    exact Real.iSup_nonneg fun t => norm_nonneg _
  have hSζ : ∀ ω, 0 ≤ Sζ ω := by
    intro ω
    exact Real.iSup_nonneg fun t => norm_nonneg _
  have hηPath := fp81s21_moment6_of_ae_path_norm
    A.P η Sη _ hηmeas hSup.1 hSη (by simpa [η, Sη] using hηnorm)
  have hζPath := fp81s21_moment6_of_ae_path_norm
    A.P ζ Sζ _ hζmeas hSup.2 hSζ (by simpa [ζ, Sζ] using hζnorm)
  exact ⟨fp81s21_sup_moment_mono A.P η hbudget hηPath,
    fp81s21_sup_moment_mono A.P ζ hbudget hζPath⟩

#print axioms HRS.Fp81.S21.fp81s21_particle_window_path_norm_identities
#print axioms HRS.Fp81.S21.fp81s21_particle_window_path_measurable_modifications
#print axioms HRS.Fp81.S21.fp81s21_particle_window_sup_sixth
#print axioms HRS.Fp81.S21.fp81s21_particle_sixth_windows
