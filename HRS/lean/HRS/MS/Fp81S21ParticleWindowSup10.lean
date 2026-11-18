import HRS.MS.Fp81S21ParticleWindowSup9
import HRS.MS.Fp81S21CenteredAdapter3
import HRS.MS.Fp81S21ShiftedMildAssembly2
import HRS.MS.Fp81S21WindowSupMeas3

/-! The raw particle window sixth moment follows from the centered estimate and
its uniformly bounded deterministic Bochner mean. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.R2WinErr

/-- The raw mean-field-centered particle fluctuation at a physical time. -/
def fp81s21_particleEta
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {N : ℕ}
    (A : Particle R N) (t : ℝ) (ω : A.Ω) :
    OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
  HRS.Whole.etaB (wholeSpaceIndex p.d : ℝ)
    (A.X t.toNNReal ω) (HRS.Whole.withDensityReal (R.ρ t))

/-- The raw physical window supremum has the same sixth-moment envelope as the
centered window, after adding the uniformly bounded path barycenter. -/
theorem fp81s21_particle_window_sup_raw_sixth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ H : ℝ, 0 < H → ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∀ b : ℝ, 0 ≤ b →
          fp81s21_Moment6 A.P
            (fun ω => ⨆ t : Icc b (b + H),
              ‖fp81s21_particleEta p R A t ω‖)
            ((C * ((1 + Real.sqrt H) ^ 3 +
              (Real.sqrt (N : ℝ))⁻¹ * (H + H ^ 2))) ^ 6) := by
  obtain ⟨δc, hδc, hδch, hCentered⟩ :=
    fp81s21_particle_window_sup_sixth_centered p
  obtain ⟨δm, hδm, hδmh, hMean⟩ :=
    fp81s21_particle_window_mean_norm_bound p
  let δ0 := min δc δm
  have hδ0 : 0 < δ0 := lt_min hδc hδm
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδch
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R
  have hδc' : δ ≤ δc := hδle.trans (min_le_left _ _)
  have hδm' : δ ≤ δm := hδle.trans (min_le_right _ _)
  obtain ⟨Cζ, hCζ, hCenteredR⟩ := hCentered δ hδ hδc' R
  obtain ⟨Cμ, hCμ, hMeanR⟩ := hMean δ hδ hδm' R
  let C : ℝ := Cζ + Cμ
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro H hH N hN A b hb
  have hbT : b ≤ b + H := by linarith
  letI : Nonempty (Icc b (b + H)) := ⟨⟨b, ⟨le_rfl, by linarith⟩⟩⟩
  have hT : 0 < b + H := by linarith
  have hZeta := hCenteredR H hH N hN A b hb
  have hMeanNorm :
      ‖∫ ω, flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H b
          (Real.sqrt (N : ℝ)) A.X R.ρ ω ∂A.P‖ ≤ Cμ :=
    hMeanR H hH N hN A b hb
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let ηpath : A.Ω → OscPath p.d m H :=
    flucPathW m H b (Real.sqrt (N : ℝ)) A.X R.ρ
  let ζpath : A.Ω → OscPath p.d m H := zetaPathW m H b A.P A.X
  let Mpath : OscPath p.d m H := ∫ ω, ηpath ω ∂A.P
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
  have hζcont : ∀ᵐ ω ∂A.P,
      Continuous (fun t : ℝ => ζfield t ω) :=
    HRS.Whole.s21e_zeta_cont_time hd1 hNpos hm A.P A.X hXm hXc
  have hηeval : ∀ᵐ ω ∂A.P, ∀ τ : Icc (0 : ℝ) H,
      OscPath.at' (ηpath ω) τ = ηfield (b + (τ : ℝ)) ω := by
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
    have hpath : ηpath ω =
        (⟨fun t : Icc (0 : ℝ) H => ηfield (b + (t : ℝ)) ω, hc⟩ : OscPath p.d m H) := by
      change windowPathOf m H b (fun t => ηfield t ω) = _
      unfold windowPathOf
      exact dif_pos hc
    rw [hpath]
    rfl
  have hζeval : ∀ᵐ ω ∂A.P, ∀ τ : Icc (0 : ℝ) H,
      OscPath.at' (ζpath ω) τ = ζfield (b + (τ : ℝ)) ω := by
    filter_upwards [hζcont] with ω hω
    intro τ
    have hc : Continuous fun t : Icc (0 : ℝ) H => ζfield (b + (t : ℝ)) ω :=
      hω.comp (continuous_const.add continuous_subtype_val)
    have hpath : ζpath ω =
        (⟨fun t : Icc (0 : ℝ) H => ζfield (b + (t : ℝ)) ω, hc⟩ : OscPath p.d m H) := by
      change windowPathOf m H b (fun t => ζfield t ω) = _
      unfold windowPathOf
      exact dif_pos hc
    rw [hpath]
    rfl
  have hCenterPath : ζpath =ᵐ[A.P] (fun ω => ηpath ω - Mpath) := by
    simpa [ζpath, ηpath, Mpath, m] using
      (fp81s21_particle_window_centered p R hN A hH hb).2
  have hRelation : ∀ᵐ ω ∂A.P, ∀ τ : Icc (0 : ℝ) H,
      fp81s21_particleEta p R A (b + (τ : ℝ)) ω =
        fp81s21_particleZeta p R A (b + (τ : ℝ)) ω + OscPath.at' Mpath τ := by
    filter_upwards [hCenterPath, hηeval, hζeval] with ω hcent heta hzet
    intro τ
    have hpathEval : OscPath.at' (ζpath ω) τ =
        OscPath.at' (ηpath ω) τ - OscPath.at' Mpath τ := by
      have h := congrArg (fun w : OscPath p.d m H => OscPath.at' w τ) (hcent)
      calc
        OscPath.at' (ζpath ω) τ = OscPath.at' (ηpath ω - Mpath) τ := h
        _ = OscPath.at' (ηpath ω) τ - OscPath.at' Mpath τ := rfl
    have hfieldEq : ζfield (b + (τ : ℝ)) ω =
        ηfield (b + (τ : ℝ)) ω - OscPath.at' Mpath τ := by
      calc
        _ = OscPath.at' (ζpath ω) τ := (hzet τ).symm
        _ = OscPath.at' (ηpath ω) τ - OscPath.at' Mpath τ := hpathEval
        _ = ηfield (b + (τ : ℝ)) ω - OscPath.at' Mpath τ := by rw [heta τ]
    have hsum : ηfield (b + (τ : ℝ)) ω =
        ζfield (b + (τ : ℝ)) ω + OscPath.at' Mpath τ := by
      calc
        _ = (ηfield (b + (τ : ℝ)) ω - OscPath.at' Mpath τ) + OscPath.at' Mpath τ :=
          (sub_add_cancel _ _).symm
        _ = ζfield (b + (τ : ℝ)) ω + OscPath.at' Mpath τ := by rw [← hfieldEq]
    simpa [fp81s21_particleEta, fp81s21_particleZeta, ηfield, ζfield] using hsum
  let Y : ℝ → A.Ω → ℝ := fun t ω =>
    ‖fp81s21_particleEta p R A t ω‖
  let Zsup : A.Ω → ℝ := fun ω =>
    ⨆ t : Icc b (b + H), ‖fp81s21_particleZeta p R A (t : ℝ) ω‖
  let Ysup : A.Ω → ℝ := fun ω => ⨆ t : Icc b (b + H), ‖Y t ω‖
  have hEtaMeas : ∀ t ∈ Icc b (b + H), AEMeasurable (Y t) A.P := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hb ht.1
    let μ : Measure (Euc p.d) := HRS.Whole.withDensityReal (R.ρ t)
    have hμprob : IsProbabilityMeasure μ :=
      HRS.MS.Thm.cb_withDensityReal_isProb
        ((R.resulting.global (b + H)).density t ⟨ht0, by linarith [ht.2]⟩)
    have hmapprob : IsProbabilityMeasure (A.P.map (A.X (Real.toNNReal t))) :=
      (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
    letI : IsProbabilityMeasure μ := hμprob
    letI : IsProbabilityMeasure (A.P.map (A.X (Real.toNNReal t))) := hmapprob
    have hζ : AEMeasurable (ζfield t) A.P :=
      (s102_zetaB_meas hm hNpos A.P A.X hXm t).aemeasurable
    let bias : OscDual p.d m := Real.sqrt (N : ℝ) •
      OscDual.ofMeasureDiff m (HRS.Whole.meanEmpirical (A.P.map (A.X (Real.toNNReal t)))) μ
    have hfield : ∀ ω, ηfield t ω = ζfield t ω + bias := by
      intro ω
      change HRS.Whole.etaB m (A.X (Real.toNNReal t) ω) μ = _
      exact fp81s21_etaField_eq_zeta_add_mean hm
        (A.P.map (A.X (Real.toNNReal t))) (A.X (Real.toNNReal t) ω) μ hN1
    have hη : AEMeasurable (ηfield t) A.P :=
      (hζ.add_const bias).congr (Filter.Eventually.of_forall fun ω => (hfield ω).symm)
    simpa [Y, ηfield, fp81s21_particleEta] using hη.norm
  have hYcont : ∀ᵐ ω ∂A.P,
      ContinuousOn (fun t => Y t ω) (Icc b (b + H)) := by
    filter_upwards [hηcont] with ω hω
    have hmem : Icc b (b + H) ⊆ Icc (0 : ℝ) (b + H) := by
      intro t ht
      exact ⟨(le_trans hb ht.1), ht.2⟩
    have hc := hω.mono hmem
    simpa [Y, fp81s21_particleEta, ηfield] using hc.norm
  obtain ⟨E, hEc, hEs, hEd, hYpath, hYmeas⟩ :=
    fp81s21_window_sup_measurable A.P Y b (b + H) hbT hEtaMeas hYcont
  have hZnonneg (ω : A.Ω) : 0 ≤ Zsup ω :=
    Real.iSup_nonneg fun t => norm_nonneg _
  have hYnonneg (ω : A.Ω) : 0 ≤ Ysup ω :=
    Real.iSup_nonneg fun t => norm_nonneg _
  have hSupDom : ∀ᵐ ω ∂A.P, Ysup ω ≤ Zsup ω + Cμ := by
    filter_upwards [hRelation, hζcont] with ω hrel hζc
    have hζcont' : ContinuousOn
        (fun t => fp81s21_particleZeta p R A t ω) (Icc b (b + H)) := by
      simpa [fp81s21_particleZeta, ζfield] using hζc.continuousOn
    have hBddZ : BddAbove (Set.range fun t : Icc b (b + H) =>
        ‖fp81s21_particleZeta p R A (t : ℝ) ω‖) := by
      have hc : IsCompact ((fun t : ℝ =>
          ‖fp81s21_particleZeta p R A t ω‖) '' Icc b (b + H)) :=
        isCompact_Icc.image_of_continuousOn hζcont'.norm
      have heq : Set.range (fun t : Icc b (b + H) =>
          ‖fp81s21_particleZeta p R A (t : ℝ) ω‖) =
          (fun t : ℝ => ‖fp81s21_particleZeta p R A t ω‖) '' Icc b (b + H) := by
        ext y
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨t, t.property, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, rfl⟩
      rw [heq]
      exact hc.bddAbove
    apply ciSup_le
    intro t
    let τ : Icc (0 : ℝ) H :=
      ⟨(t : ℝ) - b, ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩
    have hbt : b + (τ : ℝ) = (t : ℝ) := by
      dsimp [τ]
      ring
    have hpoint := hrel τ
    rw [hbt] at hpoint
    have hEvalNorm : ‖OscPath.at' Mpath ⟨(t : ℝ) - b,
        ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩‖ ≤ Cμ := by
      calc
        _ ≤ ‖Mpath‖ := ContinuousMap.norm_coe_le_norm Mpath _
        _ ≤ Cμ := by simpa [Mpath, ηpath, m] using hMeanNorm
    calc
      ‖Y (t : ℝ) ω‖ =
          ‖fp81s21_particleZeta p R A (t : ℝ) ω +
            OscPath.at' Mpath ⟨(t : ℝ) - b,
              ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩‖ := by
          simp only [Y]
          rw [← hpoint]
          simp only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ ‖fp81s21_particleZeta p R A (t : ℝ) ω‖ +
            ‖OscPath.at' Mpath ⟨(t : ℝ) - b,
              ⟨by linarith [t.2.1], by linarith [t.2.2]⟩⟩‖ := norm_add_le _ _
      _ ≤ Zsup ω + Cμ := add_le_add (le_ciSup hBddZ t) hEvalNorm
  have hDomEnorm : ∀ᵐ ω ∂A.P,
      ‖Ysup ω‖ₑ ≤ ‖Zsup ω + Cμ‖ₑ := by
    filter_upwards [hSupDom] with ω hω
    rw [Real.enorm_eq_ofReal (hYnonneg ω),
      Real.enorm_eq_ofReal (add_nonneg (hZnonneg ω) hCμ)]
    exact ENNReal.ofReal_le_ofReal hω
  let B : ℝ := (1 + Real.sqrt H) ^ 3
  let q : ℝ := (Real.sqrt (N : ℝ))⁻¹
  let Q : ℝ := H + H ^ 2
  let growth : ℝ := B + q * Q
  let Mζ : ℝ := Cζ * growth
  let Mtarget : ℝ := C * growth
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hgrowth : 1 ≤ growth := by
    have hs : 0 ≤ Real.sqrt H := Real.sqrt_nonneg _
    have hs2 : 0 ≤ (Real.sqrt H) ^ 2 := sq_nonneg _
    have hs3 : 0 ≤ (Real.sqrt H) ^ 3 := mul_nonneg hs2 hs
    have hqQ : 0 ≤ (Real.sqrt (N : ℝ))⁻¹ * (H + H ^ 2) := by positivity
    dsimp [growth, B, q, Q]
    nlinarith [hs, hs2, hs3, hqQ]
  have hMζ : 0 ≤ Mζ := by dsimp [Mζ, growth]; positivity
  have hMtarget : 0 ≤ Mtarget := by dsimp [Mtarget, growth]; positivity
  have htotal : Mζ + Cμ ≤ Mtarget := by
    dsimp [Mζ, Mtarget, C, growth]
    nlinarith [mul_nonneg hCμ (sub_nonneg.mpr hgrowth)]
  let Zsup' : A.Ω → ℝ := fun ω => Zsup ω
  have hZlp : eLpNorm' Zsup' 6 A.P ≤ ENNReal.ofReal Mζ := by
    exact fp81s21_moment6_eLpNorm'_bound A.P Zsup' Mζ hMζ (by
      simpa [Zsup', Zsup, fp81s21_particleZeta] using hZeta)
  have hConstLp : eLpNorm' (fun _ : A.Ω => Cμ) 6 A.P = ENNReal.ofReal Cμ := by
    rw [eLpNorm'_const_of_isProbabilityMeasure Cμ (by norm_num)]
    simp [Real.enorm_eq_ofReal hCμ]
  have hRawLp : eLpNorm' Ysup 6 A.P ≤ ENNReal.ofReal Mtarget := by
    have hmono := eLpNorm'_mono_enorm_ae (f := Ysup)
      (g := fun ω => Zsup' ω + Cμ) (by norm_num : (0 : ℝ) ≤ 6) hDomEnorm
    have htri := eLpNorm'_add_le (f := Zsup') (g := fun _ : A.Ω => Cμ)
      hZeta.1.aestronglyMeasurable aestronglyMeasurable_const
      (by norm_num : (1 : ℝ) ≤ 6)
    calc
      eLpNorm' Ysup 6 A.P ≤ eLpNorm' (fun ω => Zsup' ω + Cμ) 6 A.P := hmono
      _ ≤ eLpNorm' Zsup' 6 A.P + eLpNorm' (fun _ : A.Ω => Cμ) 6 A.P := htri
      _ ≤ ENNReal.ofReal Mζ + ENNReal.ofReal Cμ := add_le_add hZlp (le_of_eq hConstLp)
      _ = ENNReal.ofReal (Mζ + Cμ) := (ENNReal.ofReal_add hMζ hCμ).symm
      _ ≤ ENNReal.ofReal Mtarget := ENNReal.ofReal_le_ofReal htotal
  have hPathEq : ∀ᵐ ω ∂A.P,
      ENNReal.ofReal (Ysup ω) = ⨆ t : Icc b (b + H), ‖Y t ω‖ₑ := by
    filter_upwards [hYpath, hYcont] with ω hp hω
    have hdense := fp81s21_window_enorm_sup_dense
      hω hEs hEd
    calc
      ENNReal.ofReal (Ysup ω) =
          ENNReal.ofReal (⨆ t : Icc b (b + H), ‖Y t ω‖) := by
        congr 1
      _ = ⨆ d ∈ E, ‖Y d ω‖ₑ := hp.2
      _ = ⨆ t : Icc b (b + H), ‖Y t ω‖ₑ := hdense.symm
  have hIntegralEq :
      (∫⁻ ω, (⨆ t : Icc b (b + H), ‖Y t ω‖ₑ) ^ (6 : ℝ) ∂A.P) =
        ∫⁻ ω, ‖Ysup ω‖ₑ ^ (6 : ℝ) ∂A.P := by
    apply lintegral_congr_ae
    filter_upwards [hPathEq] with ω hω
    rw [← hω, Real.enorm_eq_ofReal (hYnonneg ω)]
  have hRoot :
      (∫⁻ ω, (⨆ t : Icc b (b + H), ‖Y t ω‖ₑ) ^ (6 : ℝ) ∂A.P) ^
          (1 / 6 : ℝ) ≤ ENNReal.ofReal Mtarget := by
    calc
      _ = (∫⁻ ω, ‖Ysup ω‖ₑ ^ (6 : ℝ) ∂A.P) ^ (1 / 6 : ℝ) := by rw [hIntegralEq]
      _ = eLpNorm' Ysup 6 A.P := by rw [eLpNorm'_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal Mtarget := hRawLp
  have hRawMoment := fp81s21_window_sup_moment6 A.P Y b (b + H) Mtarget
    hbT hMtarget hEtaMeas hYcont hRoot
  simpa [Y, fp81s21_particleEta, ηfield, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), Mtarget, C, B, q, Q, growth] using hRawMoment

#print axioms HRS.Fp81.S21.fp81s21_particleEta
#print axioms HRS.Fp81.S21.fp81s21_particle_window_sup_raw_sixth
end HRS.Fp81.S21
end
