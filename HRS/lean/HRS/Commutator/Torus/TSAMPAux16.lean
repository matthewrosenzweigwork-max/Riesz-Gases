import HRS.Commutator.Torus.TSAMPAux15

/-!
# T-SAMP helpers, part 16: `vhi_Lp_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tsamp_norm_le_sum (f : Torus d → Euc d) (x : Torus d) :
    ‖f x‖ ≤ ∑ j, ‖f x j‖ := by
  have := Whole.cmxHLS_norm_toLp_le (d := d) (fun j => f x j)
  simpa using this

/-- `‖f‖_p ≤ ∑_j ‖f_j‖_p` for a vector field (`1 ≤ p`). -/
lemma tsamp_eLpNorm_vec_le {f : Torus d → Euc d}
    (hn : AEStronglyMeasurable (fun x => ‖f x‖) volume)
    (hj : ∀ j, AEStronglyMeasurable (fun x => f x j) volume) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (fun x => ‖f x‖) p volume ≤ ∑ j, eLpNorm (fun x => f x j) p volume := by
  have h1 : eLpNorm (fun x => ‖f x‖) p volume ≤ eLpNorm (fun x => ∑ j, ‖f x j‖) p volume := by
    refine eLpNorm_mono_ae hn (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)]
    exact tsamp_norm_le_sum f x
  refine h1.trans ?_
  have := eLpNorm_sum_le (μ := (volume : Measure (Torus d))) (s := Finset.univ)
    (f := fun j x => ‖f x j‖) hp
  have e : (fun x => ∑ j, ‖f x j‖) = ∑ j, fun x => ‖f x j‖ := by
    funext x; simp
  rw [e]
  refine this.trans (Finset.sum_le_sum fun j _ => le_of_eq ?_)
  exact eLpNorm_norm _ (hj j)

theorem tsamp_vhi_Lp_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (L : ℝ) (w : Torus d → Euc d)
      (F : ℝ), 0 ≤ F → 0 ≤ L → IsLipschitzVF L v → IsFracDeriv (Whole.alphaE d s) v w →
      eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (Whole.p1E d s)) volume ≤ ENNReal.ofReal F →
      ∃ W : Torus d → Euc d,
        (∀ i, IsBesselRepT η (Whole.alphaE d s) (fun x => PgtT η v x i) (fun x => W x i)) ∧
        eLpNorm (fun x => ‖W x‖) (ENNReal.ofReal (Whole.p1E d s)) volume +
            eLpNorm (fun x => ‖PgtT η v x‖) (ENNReal.ofReal (Whole.p1E d s)) volume ≤
          ENNReal.ofReal (C * η ^ (Whole.alphaE d s) * F) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 < Whole.alphaE d s := by unfold Whole.alphaE; linarith
  have hαd : Whole.alphaE d s < d := by unfold Whole.alphaE; linarith
  have hp1 : 1 < Whole.p1E d s := by
    unfold Whole.p1E; rw [one_lt_div (by linarith)]; linarith
  obtain ⟨CL, hCL, hKα⟩ := tsamp_Kalpha_torus hd hα hαd
  obtain ⟨CB, hCB, hkb⟩ := tsamp_bessel_torus hd (Whole.alphaE d s) hα
  obtain ⟨B, C₁, C₂, hB, hC₁, hC₂, hker⟩ := tsamp_psi_kernel (d := d) hd1
  refine ⟨d * ((1 + C₁ + CB) + CL), by positivity, ?_⟩
  intro η hη hη1 v L w F hF hL hLip hrep hnorm
  set P : ℝ≥0∞ := ENNReal.ofReal (Whole.p1E d s) with hP
  have hP1 : (1 : ℝ≥0∞) ≤ P := ENNReal.one_le_ofReal.2 hp1.le
  obtain ⟨w', hw'm, hw'le, hrep'⟩ := tsamp_reduce_w hα hrep
  have hw'n : eLpNorm (fun x => ‖w' x‖) P volume ≤ ENNReal.ofReal F :=
    (eLpNorm_mono_ae hw'm.norm.aestronglyMeasurable
      (hw'le.mono fun x hx => by simpa using hx)).trans hnorm
  have hwjm : ∀ i, Measurable fun x => w' x i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp hw'm
  have hwjn : ∀ i, eLpNorm (fun x => w' x i) P volume ≤ ENNReal.ofReal F := fun i =>
    (eLpNorm_mono_ae (hwjm i).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa using PiLp.norm_apply_le (w' x) i)).trans hw'n
  have hwji : ∀ i, Integrable fun x => w' x i := fun i =>
    (memLp_iff.2 (lt_of_le_of_lt (hwjn i) ENNReal.ofReal_lt_top)).integrable hP1
  obtain ⟨Kα, hKαm, hKαi, hKαc, hKαL⟩ := hKα η hη hη1
  obtain ⟨kb, hkbm, hkbi, hkbc, hkbL⟩ := hkb η hη hη1
  obtain ⟨hKint, hKb, hK1, hKcoef, -⟩ := hker η hη hη1
  set Kη : Torus d → ℝ := perio (Whole.psiL (d := d) η⁻¹) with hKη
  have hKm : Measurable Kη := by
    obtain ⟨hc, -⟩ := text_psiL_props (d := d) η⁻¹ (inv_pos.2 hη)
    exact tpos_perio_measurable hc.measurable
  set Wj : Fin d → Torus d → ℝ := fun i => tsampWf (η ^ Whole.alphaE d s) Kη kb (fun x => w' x i) with hWj
  set W : Torus d → Euc d := fun x => (WithLp.toLp 2 (fun i => Wj i x) : Euc d) with hW
  have hWjm : ∀ i, AEStronglyMeasurable (Wj i) volume := by
    intro i
    have h1 := tsamp_aesm_conv (E := ℝ) hKm (hwjm i)
    have h2 := tsamp_aesm_conv (E := ℝ) hkbm (hwjm i)
    exact (((hwjm i).aestronglyMeasurable.sub h1).add h2).const_mul _
  have hvint : Integrable v := tsamp_integrable_of_lip hL hLip
  have hPgtc : Continuous (PgtT η v) := by
    obtain ⟨C, hC, hb⟩ := tsamp_vhi_bounded_core (d := d) hd1
    exact (hb η hη hη1 v L hL hLip).1
  refine ⟨W, ?_, ?_⟩
  · -- Bessel representation
    intro i k
    have hWi : (fun x => W x i) = Wj i := by funext x; simp [hW]
    rw [hWi]
    show Torus.fcoef (tsampWf (η ^ Whole.alphaE d s) Kη kb (fun x => w' x i)) k = _
    rw [tsamp_Wf_fcoef hKint hkbi (hwji i), tsamp_fcoef_Pgt hd1 hη hη1 hL hLip i k, hKcoef k, hkbc k]
    have := tsamp_bessel_alg (d := d) hη hα k (Torus.fcoef (fun x => v x i) k)
      (Torus.fcoef (fun x => w' x i) k) (by
        have := hrep' i k
        simpa [Whole.alphaE] using this)
    exact this
  · -- norms
    have hKαL' : ∫ y, ‖Kα y‖ ≤ CL * η ^ Whole.alphaE d s := by simpa using hKαL
    have hK1' : ∫ y, ‖Kη y‖ ≤ C₁ := by simpa using hK1
    have hkbL' : ∫ y, ‖kb y‖ ≤ CB := by simpa using hkbL
    have hηα : 0 < η ^ Whole.alphaE d s := Real.rpow_pos_of_pos hη _
    have hFo : ENNReal.ofReal F = ENNReal.ofReal F := rfl
    -- the `W` part
    have hWvec : AEStronglyMeasurable W volume :=
      ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 fun i => (hWjm i).aemeasurable)).aestronglyMeasurable
    have hWterm : ∀ i, eLpNorm (fun x => W x i) P volume ≤
        ENNReal.ofReal (η ^ Whole.alphaE d s * (1 + C₁ + CB) * F) := by
      intro i
      have hWi : (fun x => W x i) = Wj i := by funext x; simp [hW]
      rw [hWi]
      have h1 := tsamp_Wf_norm hKint hKm hkbi hkbm (hwjm i) hp1 (η ^ Whole.alphaE d s)
      refine h1.trans ?_
      rw [abs_of_pos hηα]
      have hfi := hwjn i
      have a1 : ENNReal.ofReal (∫ y, ‖Kη y‖) ≤ ENNReal.ofReal C₁ := ENNReal.ofReal_le_ofReal hK1'
      have a2 : ENNReal.ofReal (∫ y, ‖kb y‖) ≤ ENNReal.ofReal CB := ENNReal.ofReal_le_ofReal hkbL'
      calc ENNReal.ofReal (η ^ Whole.alphaE d s) *
            (eLpNorm (fun x => w' x i) P volume +
              ENNReal.ofReal (∫ y, ‖Kη y‖) * eLpNorm (fun x => w' x i) P volume +
              ENNReal.ofReal (∫ y, ‖kb y‖) * eLpNorm (fun x => w' x i) P volume)
          ≤ ENNReal.ofReal (η ^ Whole.alphaE d s) *
            (ENNReal.ofReal F + ENNReal.ofReal C₁ * ENNReal.ofReal F + ENNReal.ofReal CB * ENNReal.ofReal F) := by
            gcongr
        _ = ENNReal.ofReal (η ^ Whole.alphaE d s * (1 + C₁ + CB) * F) := by
            rw [← ENNReal.ofReal_mul hC₁.le, ← ENNReal.ofReal_mul hCB.le,
              ← ENNReal.ofReal_add hF (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hηα.le]
            congr 1
            ring
    have hWsum : eLpNorm (fun x => ‖W x‖) P volume ≤
        ENNReal.ofReal (d * (η ^ Whole.alphaE d s * (1 + C₁ + CB) * F)) := by
      refine (tsamp_eLpNorm_vec_le hWvec.norm (fun i => ?_) hP1).trans ?_
      · have : (fun x => W x i) = Wj i := by funext x; simp [hW]
        rw [this]; exact hWjm i
      · calc ∑ i, eLpNorm (fun x => W x i) P volume
            ≤ ∑ i : Fin d, ENNReal.ofReal (η ^ Whole.alphaE d s * (1 + C₁ + CB) * F) :=
              Finset.sum_le_sum fun i _ => hWterm i
          _ = ENNReal.ofReal (d * (η ^ Whole.alphaE d s * (1 + C₁ + CB) * F)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
    have hPterm : ∀ i, eLpNorm (fun x => PgtT η v x i) P volume ≤
        ENNReal.ofReal (CL * η ^ Whole.alphaE d s * F) := by
      intro i
      have hA : Integrable (tsampConv Kα (fun x => w' x i)) := by
        rw [tsamp_conv_real]; exact text_integrable_conv hKαi (hwji i)
      have hPi : Integrable (fun x => PgtT η v x i) :=
        ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hPgtc).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hae : (fun x => PgtT η v x i) =ᵐ[volume] tsampConv Kα (fun x => w' x i) := by
        have := text_ae_eq_zero_of_fcoef
          (g := fun x => PgtT η v x i - tsampConv Kα (fun x => w' x i) x) (hPi.sub hA) (fun k => by
          rw [text_fcoef_sub hPi hA, tsamp_fcoef_Pgt hd1 hη hη1 hL hLip i k, tsamp_conv_real,
            text_fcoef_conv hKαi (hwji i), hKαc k, hrep' i k]
          by_cases hk : k = 0
          · have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext j; simp [Lattice.toEuc]
            have hc : Whole.chi (η • Lattice.toEuc (0 : Lattice d)) = 1 := by
              rw [h0, smul_zero]; exact Whole.cmxFB_chi_one (by simp)
            subst hk
            rw [hc]; simp
          · have hten : 0 < 2 * Real.pi * Lattice.enorm k := by
              have := HRS.one_le_enorm k hk
              positivity
            simp only [hk, if_false]
            have h3 : (2 * Real.pi * Lattice.enorm k) ^ (-Whole.alphaE d s) *
                (2 * Real.pi * Lattice.enorm k) ^ (Whole.alphaE d s) = 1 := by
              rw [← Real.rpow_add hten]; simp
            have h4 : ((((1 - Whole.chi (η • Lattice.toEuc k)) *
                (2 * Real.pi * Lattice.enorm k) ^ (-Whole.alphaE d s) : ℝ)) : ℂ) *
                (((2 * Real.pi * Lattice.enorm k) ^ (Whole.alphaE d s) : ℝ) : ℂ) =
                (((1 - Whole.chi (η • Lattice.toEuc k) : ℝ)) : ℂ) := by
              rw [← Complex.ofReal_mul]
              congr 1
              calc (1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * Lattice.enorm k) ^ (-Whole.alphaE d s) *
                    (2 * Real.pi * Lattice.enorm k) ^ (Whole.alphaE d s)
                  = (1 - Whole.chi (η • Lattice.toEuc k)) * ((2 * Real.pi * Lattice.enorm k) ^ (-Whole.alphaE d s) *
                    (2 * Real.pi * Lattice.enorm k) ^ (Whole.alphaE d s)) := by ring
                _ = _ := by rw [h3, mul_one]
            push_cast at h4 ⊢
            linear_combination (-(Torus.fcoef (fun x => v x i) k)) * h4)
        filter_upwards [this] with x hx
        simpa [sub_eq_zero] using hx
      rw [eLpNorm_congr_ae hae]
      refine (tsamp_conv_eLpNorm_le hKαi hKαm (hwjm i) hp1).trans ?_
      calc ENNReal.ofReal (∫ y, ‖Kα y‖) * eLpNorm (fun x => w' x i) P volume
          ≤ ENNReal.ofReal (CL * η ^ Whole.alphaE d s) * ENNReal.ofReal F :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal hKαL') (hwjn i)
        _ = ENNReal.ofReal (CL * η ^ Whole.alphaE d s * F) :=
            (ENNReal.ofReal_mul (by positivity)).symm
    have hPsum : eLpNorm (fun x => ‖PgtT η v x‖) P volume ≤
        ENNReal.ofReal (d * (CL * η ^ Whole.alphaE d s * F)) := by
      refine (tsamp_eLpNorm_vec_le hPgtc.norm.aestronglyMeasurable (fun i =>
        ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hPgtc).aestronglyMeasurable) hP1).trans ?_
      calc ∑ i, eLpNorm (fun x => PgtT η v x i) P volume
          ≤ ∑ i : Fin d, ENNReal.ofReal (CL * η ^ Whole.alphaE d s * F) :=
            Finset.sum_le_sum fun i _ => hPterm i
        _ = ENNReal.ofReal (d * (CL * η ^ Whole.alphaE d s * F)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
              ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]
    refine (add_le_add hWsum hPsum).trans (le_of_eq ?_)
    have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring

end HRS.Commutator.TorusNote
