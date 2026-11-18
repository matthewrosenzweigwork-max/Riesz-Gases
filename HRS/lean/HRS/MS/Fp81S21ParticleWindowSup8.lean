import HRS.MS.Fp81S21ParticleWindowSup7
import HRS.MS.Fp81S21PathMom2
import HRS.MS.Fp81S21NoisePath6
import HRS.MS.Fp81S21WindowOrbitDecay
import HRS.MS.Fp81S21WindowSupMeas6
import HRS.MS.Fp81S21DriftPrimitive9
import HRS.MS.Fp81S21Radius
import HRS.MS.Fp81S21MovingStd2
import HRS.MS.S21F_P00

/-! Uniform centered-particle sixth moments on shifted windows. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MS.R2WinErr HRS.MS.R2GenInit HRS.MP.RdRem

/-- The centered conjunct of the particle window sixth-moment estimate,
with all constants fixed before the horizon, particle number, law and start. -/
theorem fp81s21_particle_window_sup_sixth_centered (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, 0 < H → ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ b : ℝ, 0 ≤ b →
      fp81s21_Moment6 A.P
        (fun ω => ⨆ t : Icc b (b + H),
          ‖fp81s21_particleZeta p R A t ω‖)
        ((C * ((1 + Real.sqrt H) ^ 3 +
          (Real.sqrt (N : ℝ))⁻¹ * (H + H ^ 2))) ^ 6) := by
  obtain ⟨δw, hδw, hδwh, hWin⟩ := fp81s21_window_initial_drift_moment6 p
  obtain ⟨δd, hδd, hδdh, hDrift⟩ := fp81s21_window_mode_drift_constructed p
  obtain ⟨δm, hδm, hδmh, hMove⟩ := fp81s21_path_moving_inputs p
  obtain ⟨δn, hδn, hδnh, hNoise⟩ := fp81s21_noisePath p
  obtain ⟨δo, hδo, hδoh, hOrbit⟩ := fp81s21_moving_orbit_gradient_decay p
  obtain ⟨δc, _, _, hδc, hδch, _, hCommon⟩ := fp81s21_common_radius p
  let δ0 := min δw (min δd (min δm (min δn (min δo δc))))
  have hδ0 : 0 < δ0 := lt_min hδw (lt_min hδd (lt_min hδm (lt_min hδn (lt_min hδo hδc))))
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδwh
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R
  have hδw' : δ ≤ δw := hδle.trans (min_le_left _ _)
  have hδd' : δ ≤ δd := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδm' : δ ≤ δm := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδn' : δ ≤ δn := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδo' : δ ≤ δo := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδc' : δ ≤ δc := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  obtain ⟨CI, CD, hCI, hCD, hWindow⟩ := hWin δ hδ hδw' R
  obtain ⟨_, _, _, _, hDrift⟩ := hDrift δ hδ hδd' R
  obtain ⟨hMoveT, _⟩ := hMove δ hδ hδm' R
  obtain ⟨CM, hCM, hNoiseFor⟩ := hNoise δ hδ hδn' R
  obtain ⟨_, _, _, _, hsum, _⟩ := hOrbit δ hδ hδo' R
  obtain ⟨hClaims, _, hTerm, _⟩ := hCommon δ hδ hδc' R.ρβ R.thermal
  have hwsq : Summable fun α : MultiIndex p.d => (s104_b p.d α) ^ 2 :=
    HRS.MS.R2GenInit.s105_b_sq_summable hsum
  have hweight : 0 ≤ ∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2 :=
    tsum_nonneg fun α => sq_nonneg (s104_b p.d α)
  let S : ℝ := Real.sqrt (∑' α : MultiIndex p.d, (s104_b p.d α) ^ 2)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  let C : ℝ := S * (CI + CD) + CM
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro H hH N hN A b hb
  have hT : 0 < b + H := by linarith
  have hbT : b ≤ b + H := by linarith
  letI : Nonempty (Icc b (b + H)) := ⟨⟨b, ⟨le_rfl, by linarith⟩⟩⟩
  have hphys : Fp81MovingPhysicalInputs R hN A (b + H) :=
    (hMoveT (b + H) hT).2 N hN A
  obtain ⟨c0, hData⟩ := fp81s21_moving_s101data_of_common p R hT hClaims hTerm
  obtain ⟨F⟩ := HRS.MS.R26T3.r26t3_filtered_particle A
  obtain ⟨G, hG, hNoiseMatch⟩ := hNoiseFor H hH N hN A b hb F
  have hI : ∀ α : MultiIndex p.d,
      fp81s21_Moment6 A.P
        (fun ω => ⨆ t : Icc b (b + H),
          |fp81s21_shiftedModeInitial p R A α b t ω|)
        ((CI * (1 + H) * s104_b p.d α) ^ 6) := by
    intro α
    simpa [fp81s21_shiftedModeInitial] using (hWindow H hH N hN A b hb α).1
  have hD : ∀ α : MultiIndex p.d,
      fp81s21_Moment6 A.P
        (fun ω => ⨆ t : Icc b (b + H),
          |fp81s21_shiftedModeDrift p R A α b t ω|)
        ((CD * (H + H ^ 2) * s104_b p.d α) ^ 6) := by
    intro α
    simpa [fp81s21_shiftedModeDrift] using (hWindow H hH N hN A b hb α).2.1
  have hcert : ∀ᵐ ω ∂A.P, ∀ α : MultiIndex p.d,
      (∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ b + H →
        IntervalIntegrable
          (fun v => fp81s21_window_mode_source_field p R A α v t ω) volume a t) ∧
      ContinuousOn (fun t => fp81s21_shiftedModeDrift p R A α b t ω)
        (Icc b (b + H)) := by
    apply ae_all_iff.2
    intro α
    obtain ⟨_, _, Q, K, hQ, hK, hQe, hKe, hQi, hKi, hsource, hresult, _⟩ :=
      hDrift N hN A (b + H) hT α b hb (by linarith)
    filter_upwards [hsource, hresult] with ω hs hr
    exact ⟨hs, hr.2⟩
  have hres := fp81s21_particle_residual_window_sup_moment6
    p R hδ (hδle.trans hδ0h) hN A hH b hb F hphys G hG.1 hNoiseMatch hData
    CI CD hCI hCD hI hD hcert hwsq
  let q : ℝ := (Real.sqrt (N : ℝ))⁻¹
  let B : ℝ := (1 + Real.sqrt H) ^ 3
  let Q : ℝ := H + H ^ 2
  let Mres : ℝ := (CI * (1 + H) + q * CD * Q) * S
  let Mnoise : ℝ := CM * B
  let Mtarget : ℝ := C * (B + q * Q)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hB : 1 + H ≤ B := by
    dsimp [B]
    calc
      1 + H = 1 + (Real.sqrt H) ^ 2 := by rw [Real.sq_sqrt hH.le]
      _ ≤ (1 + Real.sqrt H) ^ 3 := by nlinarith [Real.sqrt_nonneg H]
  have hMres : 0 ≤ Mres := by dsimp [Mres]; positivity
  have hMnoise : 0 ≤ Mnoise := by dsimp [Mnoise]; positivity
  have hMtarget : 0 ≤ Mtarget := by dsimp [Mtarget]; positivity
  have hcoeffI : S * CI + CM ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hS hCD]
  have hcoeffD : S * CD ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg hS hCI, mul_nonneg hS hCD, hCM]
  have hresBound : Mres ≤ S * CI * B + S * CD * (q * Q) := by
    dsimp [Mres]
    calc
      (CI * (1 + H) + q * CD * Q) * S =
          (CI * (1 + H)) * S + (q * CD * Q) * S := by ring
      _ ≤ (CI * B) * S + (CD * (q * Q)) * S := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hB hCI) hS
          · exact mul_le_mul_of_nonneg_right (le_of_eq (by ring)) hS
      _ = S * CI * B + S * CD * (q * Q) := by ring
  have htotalBound : Mres + Mnoise ≤ Mtarget := by
    dsimp [Mnoise, Mtarget]
    calc
      Mres + CM * B ≤ (S * CI * B + S * CD * (q * Q)) + CM * B :=
        add_le_add hresBound le_rfl
      _ = (S * CI + CM) * B + (S * CD) * (q * Q) := by ring
      _ ≤ C * B + C * (q * Q) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hcoeffI hB0)
          (mul_le_mul_of_nonneg_right hcoeffD (mul_nonneg hq hQ0))
      _ = C * (B + q * Q) := by ring
  let L : ℝ → A.Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ) := fun t ω =>
    fp81s21_particleZeta p R A t ω -
      fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)
  let Rvar : A.Ω → ℝ := fun ω => ⨆ t : Icc b (b + H), ‖L t ω‖
  let Gnorm : A.Ω → ℝ := fun ω => ‖G ω‖
  have hR : fp81s21_Moment6 A.P Rvar (Mres ^ 6) := by
    simpa [Rvar, L, Mres, S, q, Q] using hres
  have hGnorm : fp81s21_Moment6 A.P Gnorm (Mnoise ^ 6) := by
    rcases hG with ⟨hm, hi, hbnd⟩
    have hmnorm : AEMeasurable Gnorm A.P := by
      exact continuous_norm.measurable.comp_aemeasurable hm
    have hpow : (fun ω => ‖Gnorm ω‖ ^ (6 : ℕ)) =ᵐ[A.P]
        (fun ω => ‖G ω‖ ^ (6 : ℕ)) := by
      filter_upwards with ω
      simp [Gnorm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (G ω))]
    refine ⟨hmnorm, hi.congr hpow.symm, ?_⟩
    calc
      (∫ ω, ‖Gnorm ω‖ ^ 6 ∂A.P) = ∫ ω, ‖G ω‖ ^ 6 ∂A.P := integral_congr_ae hpow
      _ ≤ (CM * (1 + Real.sqrt H) ^ 3) ^ 6 := hbnd
  have hRlp : eLpNorm' Rvar 6 A.P ≤ ENNReal.ofReal Mres :=
    fp81s21_moment6_eLpNorm'_bound A.P Rvar Mres hMres hR
  have hGlp : eLpNorm' Gnorm 6 A.P ≤ ENNReal.ofReal Mnoise :=
    fp81s21_moment6_eLpNorm'_bound A.P Gnorm Mnoise hMnoise hGnorm
  have hXmeas : ∀ t : ℝ≥0, Measurable (A.X t) :=
    (A.strong (b + H)).adapted
  have hNpos : 0 < N := by omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hmindex : (p.d : ℝ) < (wholeSpaceIndex p.d : ℝ) := by
    exact_mod_cast (show p.d < wholeSpaceIndex p.d by unfold wholeSpaceIndex; omega)
  have hZetaMeas (t : ℝ) : AEMeasurable
      (fun ω => fp81s21_particleZeta p R A t ω) A.P := by
    dsimp [fp81s21_particleZeta]
    exact (s102_zetaB_meas hmindex hNpos A.P A.X hXmeas t).aemeasurable
  have hZetaCont : ∀ᵐ ω ∂A.P,
      Continuous (fun t : ℝ => fp81s21_particleZeta p R A t ω) := by
    have h := HRS.Whole.s21e_zeta_cont_time hd1 hNpos hmindex
      A.P A.X hXmeas (A.strong (b + H)).cont
    filter_upwards [h] with ω hω
    simpa [fp81s21_particleZeta] using hω
  have hNoiseCont (ω : A.Ω) : Continuous (fun t : ℝ =>
      fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)) := by
    let cl : ℝ → Icc (0 : ℝ) H := fun t =>
      ⟨mrrClamp H (t - b), mrrClamp_mem hH.le (t - b)⟩
    have hcl : Continuous cl :=
      ((continuous_mrrClamp H).comp (continuous_id.sub continuous_const)).subtype_mk
        (fun t => mrrClamp_mem hH.le (t - b))
    have hEval : Continuous (fun u : Icc (0 : ℝ) H => OscPath.at' (G ω) u) :=
      (G ω).continuous
    change Continuous fun t : ℝ => OscPath.at' (G ω) (cl t)
    exact hEval.comp hcl
  let Y : ℝ → A.Ω → ℝ := fun t ω => ‖fp81s21_particleZeta p R A t ω‖
  have hZsupMeasData := fp81s21_window_sup_measurable A.P Y b (b + H) hbT
    (fun t ht => (hZetaMeas t).norm)
    (by
      filter_upwards [hZetaCont] with ω hω
      exact hω.norm.continuousOn)
  obtain ⟨E, hEc, hEs, hEd, hpath, hZsupMeas⟩ := hZsupMeasData
  let Zsup : A.Ω → ℝ := fun ω => ⨆ t : Icc b (b + H),
    ‖fp81s21_particleZeta p R A t ω‖
  have hZmeas : AEMeasurable Zsup A.P := by
    simpa [Zsup, Y, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hZsupMeas
  have hZnonneg (ω : A.Ω) : 0 ≤ Zsup ω := Real.iSup_nonneg fun t => norm_nonneg _
  have hRnonneg (ω : A.Ω) : 0 ≤ Rvar ω := Real.iSup_nonneg fun t => norm_nonneg _
  have hGnonneg (ω : A.Ω) : 0 ≤ Gnorm ω := norm_nonneg _
  have hSupDom : ∀ᵐ ω ∂A.P, Zsup ω ≤ Rvar ω + Gnorm ω := by
    filter_upwards [hZetaCont] with ω hζ
    have hζ' : Continuous (fun t : ℝ => fp81s21_particleZeta p R A t ω) := hζ
    have hLcont : ContinuousOn (fun t => L t ω) (Icc b (b + H)) :=
      (hζ'.sub (hNoiseCont ω)).continuousOn
    have hBddL : BddAbove (Set.range fun t : Icc b (b + H) => ‖L t ω‖) := by
      have hc : IsCompact ((fun t : ℝ => ‖L t ω‖) '' Icc b (b + H)) :=
        isCompact_Icc.image_of_continuousOn hLcont.norm
      have heq : Set.range (fun t : Icc b (b + H) => ‖L t ω‖) =
          (fun t : ℝ => ‖L t ω‖) '' Icc b (b + H) := by
        ext y
        constructor
        · rintro ⟨t, rfl⟩
          exact ⟨t, t.property, rfl⟩
        · rintro ⟨t, ht, rfl⟩
          exact ⟨⟨t, ht⟩, rfl⟩
      rw [heq]
      exact hc.bddAbove
    have hBddZ : BddAbove (Set.range fun t : Icc b (b + H) =>
        ‖fp81s21_particleZeta p R A t ω‖) := by
      have hc : IsCompact ((fun t : ℝ => ‖fp81s21_particleZeta p R A t ω‖) '' Icc b (b + H)) :=
        isCompact_Icc.image_of_continuousOn hζ'.continuousOn.norm
      have heq : Set.range (fun t : Icc b (b + H) =>
          ‖fp81s21_particleZeta p R A t ω‖) =
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
    have hEval : ‖fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)‖ ≤ Gnorm ω := by
      let τ : Icc (0 : ℝ) H :=
        ⟨mrrClamp H (t - b), mrrClamp_mem hH.le (t - b)⟩
      change ‖OscPath.at' (G ω) τ‖ ≤ ‖G ω‖
      exact ContinuousMap.norm_coe_le_norm (G ω) τ
    have hDec : fp81s21_particleZeta p R A t ω =
        L t ω + fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b) := by
      simp [L]
    calc
      ‖fp81s21_particleZeta p R A t ω‖ =
          ‖L t ω + fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)‖ := by rw [hDec]
      _ ≤ ‖L t ω‖ + ‖fp81s21_shiftedNoiseValue p R A hH.le G ω (t - b)‖ := norm_add_le _ _
      _ ≤ Rvar ω + Gnorm ω := add_le_add (le_ciSup hBddL t) hEval
  have hDomEnorm : ∀ᵐ ω ∂A.P, ‖Zsup ω‖ₑ ≤ ‖Rvar ω + Gnorm ω‖ₑ := by
    filter_upwards [hSupDom] with ω hω
    rw [Real.enorm_eq_ofReal (hZnonneg ω),
      Real.enorm_eq_ofReal (add_nonneg (hRnonneg ω) (hGnonneg ω))]
    exact ENNReal.ofReal_le_ofReal hω
  have hSumStrong : AEStronglyMeasurable (fun ω => Rvar ω + Gnorm ω) A.P :=
    hR.1.aestronglyMeasurable.add hGnorm.1.aestronglyMeasurable
  have hZlp : eLpNorm' Zsup 6 A.P ≤ ENNReal.ofReal Mtarget := by
    have hmono := eLpNorm'_mono_enorm_ae (f := Zsup) (g := fun ω => Rvar ω + Gnorm ω)
      (by norm_num : (0 : ℝ) ≤ 6) hDomEnorm
    have htri := eLpNorm'_add_le (f := Rvar) (g := Gnorm)
      hR.1.aestronglyMeasurable hGnorm.1.aestronglyMeasurable
      (by norm_num : (1 : ℝ) ≤ 6)
    calc
      eLpNorm' Zsup 6 A.P ≤ eLpNorm' (fun ω => Rvar ω + Gnorm ω) 6 A.P := hmono
      _ ≤ eLpNorm' Rvar 6 A.P + eLpNorm' Gnorm 6 A.P := htri
      _ ≤ ENNReal.ofReal Mres + ENNReal.ofReal Mnoise := add_le_add hRlp hGlp
      _ = ENNReal.ofReal (Mres + Mnoise) := (ENNReal.ofReal_add hMres hMnoise).symm
      _ ≤ ENNReal.ofReal Mtarget := ENNReal.ofReal_le_ofReal htotalBound
  have hPathEq : ∀ᵐ ω ∂A.P,
      ENNReal.ofReal (Zsup ω) = ⨆ t : Icc b (b + H), ‖Y t ω‖ₑ := by
    filter_upwards [hpath, hZetaCont] with ω hp hω
    have hdense := fp81s21_window_enorm_sup_dense
      (hω.continuousOn.norm) hEs hEd
    calc
      ENNReal.ofReal (Zsup ω) =
          ENNReal.ofReal (⨆ t : Icc b (b + H), ‖Y t ω‖) := by
        congr 1
        simp [Zsup, Y, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ = ⨆ d ∈ E, ‖Y d ω‖ₑ := hp.2
      _ = ⨆ t : Icc b (b + H), ‖Y t ω‖ₑ := hdense.symm
  have hIntegralEq :
      (∫⁻ ω, (⨆ t : Icc b (b + H), ‖Y t ω‖ₑ) ^ (6 : ℝ) ∂A.P) =
        ∫⁻ ω, ‖Zsup ω‖ₑ ^ (6 : ℝ) ∂A.P := by
    apply lintegral_congr_ae
    filter_upwards [hPathEq] with ω hω
    rw [← hω, Real.enorm_eq_ofReal (hZnonneg ω)]
  have hRoot :
      (∫⁻ ω, (⨆ t : Icc b (b + H), ‖Y t ω‖ₑ) ^ (6 : ℝ) ∂A.P) ^
        (1 / 6 : ℝ) ≤ ENNReal.ofReal Mtarget := by
    calc
      _ = (∫⁻ ω, ‖Zsup ω‖ₑ ^ (6 : ℝ) ∂A.P) ^ (1 / 6 : ℝ) := by rw [hIntegralEq]
      _ = eLpNorm' Zsup 6 A.P := by rw [eLpNorm'_eq_lintegral_enorm]
      _ ≤ ENNReal.ofReal Mtarget := hZlp
  have hYmeas : ∀ t ∈ Icc b (b + H), AEMeasurable (Y t) A.P := by
    intro t ht
    exact (hZetaMeas t).norm
  have hYcont : ∀ᵐ ω ∂A.P, ContinuousOn
      (fun t => Y t ω) (Icc b (b + H)) := by
    filter_upwards [hZetaCont] with ω hω
    simpa [Y] using hω.continuousOn.norm
  have hwindow := fp81s21_window_sup_moment6 A.P
    Y b (b + H) Mtarget hbT hMtarget
    hYmeas hYcont hRoot
  simpa [Y, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hwindow

#print axioms HRS.Fp81.S21.fp81s21_particle_window_sup_sixth_centered
end HRS.Fp81.S21
end
