import HRS.MS.Fp81S21ParticleWindowSup4

/-! Residual coordinate moments from the simultaneous shifted-mild identity. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole

/-- Initial and drift coordinate moments, together with the simultaneous mild
identity, control the sixth moment of the residual oscillator path supremum. -/
theorem fp81s21_residual_path_sup_moment6_of_shifted_mild
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (hd : 0 < d) (m b H : ℝ) (hH : 0 < H)
    (N : ℕ) (hN : 2 ≤ N)
    (L : ℝ → Ω → OscDual d m)
    (I D : MultiIndex d → ℝ → Ω → ℝ)
    (w : MultiIndex d → ℝ) (CI CD : ℝ)
    (hCI : 0 ≤ CI) (hCD : 0 ≤ CD)
    (hw : ∀ α : MultiIndex d, 0 ≤ w α)
    (hwsq : Summable fun α : MultiIndex d => w α ^ 2)
    (hI : ∀ α : MultiIndex d,
      fp81s21_Moment6 P (fun ω => ⨆ t : Icc b (b + H), |I α t ω|)
        ((CI * (1 + H) * w α) ^ 6))
    (hD : ∀ α : MultiIndex d,
      fp81s21_Moment6 P (fun ω => ⨆ t : Icc b (b + H), |D α t ω|)
        ((CD * (H + H ^ 2) * w α) ^ 6))
    (hmodeCont : ∀ α : MultiIndex d, ∀ᵐ ω ∂P,
      ContinuousOn (fun t => I α t ω) (Icc b (b + H)) ∧
      ContinuousOn (fun t => D α t ω) (Icc b (b + H)))
    (hcoord : ∀ᵐ ω ∂P, ∀ α : MultiIndex d, ∀ t ∈ Icc b (b + H),
      OscDual.coord (L t ω) α = I α t ω -
        (Real.sqrt (N : ℝ))⁻¹ * D α t ω)
    (hLmeas : ∀ t ∈ Icc b (b + H), AEMeasurable (L t) P)
    (hLcont : ∀ ω, ContinuousOn (fun t => L t ω) (Icc b (b + H))) :
    fp81s21_Moment6 P (fun ω => ⨆ t : Icc b (b + H), ‖L t ω‖)
      (((CI * (1 + H) + (Real.sqrt (N : ℝ))⁻¹ * CD * (H + H ^ 2)) *
        Real.sqrt (∑' α : MultiIndex d, w α ^ 2)) ^ 6) := by
  classical
  letI : Nonempty (Icc b (b + H)) := ⟨⟨b, ⟨le_rfl, by linarith⟩⟩⟩
  have hNpos : 0 < N := by omega
  have hsqrtN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by positivity)
  let c : ℝ := (Real.sqrt (N : ℝ))⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let K : ℝ := CI * (1 + H) + c * CD * (H + H ^ 2)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hweight := hw
  have hMode : ∀ α : MultiIndex d,
      fp81s21_Moment6 P (fun ω => ⨆ t : Icc b (b + H),
        |OscDual.coord (L t ω) α|) ((K * w α) ^ 6) := by
    intro α
    let U : Ω → ℝ := fun ω => ⨆ t : Icc b (b + H), |I α t ω|
    let V : Ω → ℝ := fun ω => ⨆ t : Icc b (b + H), |D α t ω|
    let S : Ω → ℝ := fun ω => ⨆ t : Icc b (b + H),
      |OscDual.coord (L t ω) α|
    let W : Ω → ℝ := fun ω => U ω + c * V ω
    have hMI : 0 ≤ CI * (1 + H) * w α :=
      mul_nonneg (mul_nonneg hCI (by linarith)) (hweight α)
    have hMD : 0 ≤ CD * (H + H ^ 2) * w α :=
      mul_nonneg (mul_nonneg hCD (by positivity)) (hweight α)
    have hUstrong : AEStronglyMeasurable U P := by
      exact (hI α).1.aestronglyMeasurable
    have hVstrong : AEStronglyMeasurable V P := by
      exact (hD α).1.aestronglyMeasurable
    have hMIbound : eLpNorm' U 6 P ≤ ENNReal.ofReal (CI * (1 + H) * w α) :=
      fp81s21_moment6_eLpNorm'_bound P U (CI * (1 + H) * w α) hMI
        (by simpa [U] using hI α)
    have hMDbound : eLpNorm' V 6 P ≤ ENNReal.ofReal (CD * (H + H ^ 2) * w α) :=
      fp81s21_moment6_eLpNorm'_bound P V (CD * (H + H ^ 2) * w α) hMD
        (by simpa [V] using hD α)
    have hUcont := hmodeCont α
    have hSupBound : ∀ᵐ ω ∂P, S ω ≤ W ω := by
      filter_upwards [hcoord, hUcont] with ω hω hcont
      have hBddU : BddAbove (Set.range fun t : Icc b (b + H) => |I α t ω|) := by
        have hcompact : IsCompact ((fun t : ℝ => |I α t ω|) '' Icc b (b + H)) :=
          isCompact_Icc.image_of_continuousOn hcont.1.abs
        convert hcompact.bddAbove using 1
        ext y
        simp only [Set.mem_range, Set.mem_image, Subtype.exists]
        tauto
      have hBddV : BddAbove (Set.range fun t : Icc b (b + H) => |D α t ω|) := by
        have hcompact : IsCompact ((fun t : ℝ => |D α t ω|) '' Icc b (b + H)) :=
          isCompact_Icc.image_of_continuousOn hcont.2.abs
        convert hcompact.bddAbove using 1
        ext y
        simp only [Set.mem_range, Set.mem_image, Subtype.exists]
        tauto
      apply ciSup_le
      intro t
      have hpt : |OscDual.coord (L t ω) α| = |I α t ω - c * D α t ω| :=
        congrArg abs (hω α t t.property)
      calc
        |OscDual.coord (L t ω) α| = |I α t ω - c * D α t ω| := hpt
        _ ≤ |I α t ω| + |c * D α t ω| := abs_sub _ _
        _ = |I α t ω| + c * |D α t ω| := by
          rw [abs_mul, abs_of_nonneg hc]
        _ ≤ U ω + c * V ω := add_le_add
          (le_ciSup hBddU t)
          (mul_le_mul_of_nonneg_left (le_ciSup hBddV t) hc)
    have hUnonneg (ω : Ω) : 0 ≤ U ω :=
      Real.iSup_nonneg fun t => abs_nonneg _
    have hVnonneg (ω : Ω) : 0 ≤ V ω :=
      Real.iSup_nonneg fun t => abs_nonneg _
    have hWnonneg (ω : Ω) : 0 ≤ W ω :=
      add_nonneg (hUnonneg ω) (mul_nonneg hc (hVnonneg ω))
    have hSnonneg (ω : Ω) : 0 ≤ S ω :=
      Real.iSup_nonneg fun t => abs_nonneg _
    have hEnormBound : ∀ᵐ ω ∂P, ‖S ω‖ₑ ≤ ‖W ω‖ₑ := by
      filter_upwards [hSupBound] with ω hω
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hSnonneg ω),
        Real.enorm_eq_ofReal_abs, abs_of_nonneg (hWnonneg ω)]
      exact ENNReal.ofReal_le_ofReal hω
    have hSstrong : AEStronglyMeasurable S P := by
      let Y : ℝ → Ω → ℝ := fun t ω => OscDual.coord (L t ω) α
      have hmY : ∀ t ∈ Icc b (b + H), AEMeasurable (Y t) P := by
        intro t ht
        exact ((HRS.MS.R2Interp.s102_coordCLM α).continuous.measurable.comp_aemeasurable
          (hLmeas t ht))
      have hcY : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Icc b (b + H)) := by
        filter_upwards with ω
        exact (HRS.MS.R2Interp.s102_coordCLM α).continuous.comp_continuousOn (hLcont ω)
      obtain ⟨_, _, _, _, _, hmeas⟩ :=
        fp81s21_window_sup_measurable P Y b (b + H) (by linarith) hmY hcY
      exact hmeas.aestronglyMeasurable.congr (Filter.Eventually.of_forall fun ω => by
        simp [S, Y, Real.norm_eq_abs])
    have hWstrong : AEStronglyMeasurable W P :=
      hUstrong.add (hVstrong.const_smul c)
    have hLpS : eLpNorm' S 6 P ≤ ENNReal.ofReal (K * w α) := by
      have hmono := eLpNorm'_mono_enorm_ae (f := S) (g := W)
        (by norm_num : (0 : ℝ) ≤ 6) hEnormBound
      have htri := eLpNorm'_add_le (f := U) (g := fun ω => c • V ω)
        hUstrong (hVstrong.const_smul c) (by norm_num : (1 : ℝ) ≤ 6)
      have hscaled : eLpNorm' (fun ω => c • V ω) 6 P ≤
          ENNReal.ofReal (c * (CD * (H + H ^ 2) * w α)) := by
        calc
          eLpNorm' (fun ω => c • V ω) 6 P =
              ‖c‖ₑ * eLpNorm' V 6 P := eLpNorm'_const_smul c (by norm_num)
          _ = ENNReal.ofReal c * eLpNorm' V 6 P := by
            rw [Real.enorm_eq_ofReal hc]
          _ ≤ ENNReal.ofReal c * ENNReal.ofReal (CD * (H + H ^ 2) * w α) :=
            mul_le_mul_of_nonneg_left hMDbound (by positivity : 0 ≤ ENNReal.ofReal c)
          _ = ENNReal.ofReal (c * (CD * (H + H ^ 2) * w α)) :=
            (ENNReal.ofReal_mul hc).symm
      have hsum : eLpNorm' S 6 P ≤
          ENNReal.ofReal (CI * (1 + H) * w α) +
            ENNReal.ofReal (c * (CD * (H + H ^ 2) * w α)) :=
        hmono.trans (htri.trans (add_le_add hMIbound hscaled))
      have hcoeff : CI * (1 + H) * w α +
          c * (CD * (H + H ^ 2) * w α) = K * w α := by
        dsimp [K]
        ring
      calc
        eLpNorm' S 6 P ≤
            ENNReal.ofReal (CI * (1 + H) * w α) +
              ENNReal.ofReal (c * (CD * (H + H ^ 2) * w α)) := hsum
        _ = ENNReal.ofReal (K * w α) := by
          rw [← ENNReal.ofReal_add hMI (mul_nonneg hc hMD), hcoeff]
    let Y : ℝ → Ω → ℝ := fun t ω => OscDual.coord (L t ω) α
    have hmY : ∀ t ∈ Icc b (b + H), AEMeasurable (Y t) P := by
      intro t ht
      exact ((HRS.MS.R2Interp.s102_coordCLM α).continuous.measurable.comp_aemeasurable
        (hLmeas t ht))
    have hcY : ∀ᵐ ω ∂P, ContinuousOn (fun t => Y t ω) (Icc b (b + H)) := by
      filter_upwards with ω
      exact (HRS.MS.R2Interp.s102_coordCLM α).continuous.comp_continuousOn (hLcont ω)
    obtain ⟨E, hEc, hEs, hEd, hpath, _⟩ :=
      fp81s21_window_sup_measurable P Y b (b + H) (by linarith) hmY hcY
    have hSupEq : ∀ᵐ ω ∂P,
        ENNReal.ofReal (S ω) = ⨆ t : Icc b (b + H), ‖Y t ω‖ₑ := by
      filter_upwards [hpath, hcY] with ω hp hω
      have hdense := fp81s21_window_enorm_sup_dense hω hEs hEd
      calc
        ENNReal.ofReal (S ω) =
            ENNReal.ofReal (⨆ t : Icc b (b + H), ‖Y t ω‖) := by
          
          simp [S, Y, Real.norm_eq_abs]
        _ = ⨆ t ∈ E, ‖Y t ω‖ₑ := hp.2
        _ = ⨆ t : Icc b (b + H), ‖Y t ω‖ₑ := hdense.symm
    have hIntegralEq :
        (∫⁻ ω, (⨆ t : Icc b (b + H), ‖Y t ω‖ₑ) ^ (6 : ℝ) ∂P) =
          ∫⁻ ω, ‖S ω‖ₑ ^ (6 : ℝ) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hSupEq] with ω hω
      rw [← hω, Real.enorm_eq_ofReal (hSnonneg ω)]
    have hRoot :
        (∫⁻ ω, (⨆ t : Icc b (b + H), ‖Y t ω‖ₑ) ^ (6 : ℝ) ∂P) ^
            (1 / 6 : ℝ) ≤ ENNReal.ofReal (K * w α) := by
      calc
        _ = (∫⁻ ω, ‖S ω‖ₑ ^ (6 : ℝ) ∂P) ^ (1 / 6 : ℝ) := by rw [hIntegralEq]
        _ = eLpNorm' S 6 P := by
          rw [eLpNorm'_eq_lintegral_enorm]
        _ ≤ ENNReal.ofReal (K * w α) := hLpS
    have hKweight : 0 ≤ K * w α := mul_nonneg hK (hweight α)
    have hwindow := fp81s21_window_sup_moment6 P Y b (b + H) (K * w α)
      (by linarith) hKweight hmY hcY hRoot
    simpa [Y, S, Real.norm_eq_abs] using hwindow
  exact fp81s21_oscDual_path_sup_moment6_of_mode_moments P hd m b (b + H) K (by linarith)
    L w hK hweight hwsq hLmeas hLcont hMode

#print axioms HRS.Fp81.S21.fp81s21_residual_path_sup_moment6_of_shifted_mild
end HRS.Fp81.S21
end
