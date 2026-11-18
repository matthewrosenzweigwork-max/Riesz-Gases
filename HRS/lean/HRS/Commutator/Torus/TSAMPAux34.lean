import HRS.Commutator.Torus.TSAMPAux33

/-!
# T-SAMP helpers, part 34: `usample_T` (assembly)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tsamp_p2E_gt (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) : 1 < Whole.p2E d s := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  unfold Whole.p2E
  rw [one_lt_div (by linarith)]
  linarith

theorem tsamp_usample_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ u : Torus d → Euc d, Continuous u →
      MemLp (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume →
      (∀ i (k : Lattice d), 2 < η * Lattice.enorm k → Torus.fcoef (fun x => u x i) k = 0) →
      ∃ U : Torus d → Euc d,
        (∀ i, IsBesselRepT η (Whole.alphaE d s) (fun x => u x i) (fun x => U x i)) ∧
        eLpNorm (fun x => ‖U x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ≤
          ENNReal.ofReal C * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume ∧
        cellSupNorm η (Whole.p2E d s) u ≤
          ENNReal.ofReal (C * η ^ (-(d : ℝ) / Whole.p2E d s)) *
            eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal (Whole.p2E d s)) volume := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hp1 := tsamp_p2E_gt hd hs0 hsd
  set p : ℝ := Whole.p2E d s with hp
  have hp0 : 0 < p := by linarith
  set q : ℝ := p.conjExponent with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq1 : 1 < q := hpq.symm.lt
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1.le
  have hα : 0 < Whole.alphaE d s := by
    unfold Whole.alphaE
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨B, Cm, hB, hCm, hpsi⟩ := tsamp_psi_profile hd1
  obtain ⟨CB, hCB, hBr⟩ := tsamp_Br_torus hd1 (Whole.alphaE d s)
  obtain ⟨Cs, hCs, hprofs⟩ := tsamp_profile_sampling hd1 hpq (a := 0) (γ := 0)
    (C := B * 2 ^ d) (Cm := Cm / 2) le_rfl (by simp; positivity) (by positivity) (by positivity)
  refine ⟨d * (CB + Cs), by positivity, ?_⟩
  intro η hη hη1 u hu hmem hsupp
  have hη' : 0 < η / 2 := by positivity
  have hη'1 : η / 2 ≤ 1 := by linarith
  set K : Torus d → ℝ := perio (Whole.psiL (d := d) (η / 2)⁻¹) with hK
  have hKm : Measurable K := (tkr_perio_psi_continuous (inv_pos.2 hη')).measurable
  have hum : Measurable u := hu.measurable
  have huim : ∀ i, Continuous fun x => u x i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hu
  have hunorm : ∀ i x, |u x i| ≤ ‖u x‖ := fun i x => by
    simpa using PiLp.norm_apply_le (u x) i
  have hunn : eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume < ⊤ := hmem
  have huin : ∀ i, eLpNorm (fun x => u x i) (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := fun i =>
    eLpNorm_mono_ae (huim i).aestronglyMeasurable (Eventually.of_forall fun x => by
      simpa using hunorm i x)
  -- the Bessel kernel
  obtain ⟨Φ, hΦm, hΦi, hΦc, hΦL⟩ := hBr η hη hη1
  set Ui : Fin d → Torus d → ℝ := fun i => tsampConv Φ (fun x => u x i) with hUi
  set U : Torus d → Euc d := fun x => (WithLp.toLp 2 (fun i => Ui i x) : Euc d) with hU
  have hUim : ∀ i, AEStronglyMeasurable (Ui i) volume := fun i =>
    tsamp_aesm_conv (E := ℝ) hΦm (huim i).measurable
  have hui : ∀ i, Integrable fun x => u x i := fun i =>
    (huim i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro i k
    have hUi' : (fun x => U x i) = Ui i := by funext x; simp [hU]
    rw [hUi']
    show Torus.fcoef (tsampConv Φ (fun x => u x i)) k = _
    rw [tsamp_conv_real, text_fcoef_conv hΦi (hui i), hΦc k]
    by_cases h : 2 < η * Lattice.enorm k
    · rw [hsupp i k h]; simp
    · have hc : Whole.chi ((3 : ℝ)⁻¹ • (η • Lattice.toEuc k)) = 1 := by
        apply Whole.cmxFB_chi_one
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hη,
          abs_of_pos (by norm_num : (0 : ℝ) < 3⁻¹)]
        unfold Lattice.enorm at h
        push Not at h
        nlinarith
      have hn : ‖η • Lattice.toEuc k‖ ^ 2 = η ^ 2 * Lattice.enorm k ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη, mul_pow]; rfl
      have key : 1 + 4 * Real.pi ^ 2 * (η ^ 2 * Lattice.enorm k ^ 2) =
          1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 := by ring
      rw [hc, hn, key, mul_one]
  · -- `L^p` bound for `U`
    have hUvec : AEStronglyMeasurable U volume :=
      ((MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.comp_aemeasurable
        (aemeasurable_pi_iff.2 fun i => (hUim i).aemeasurable)).aestronglyMeasurable
    refine (tsamp_eLpNorm_vec_le hUvec.norm (fun i => ?_) hP1).trans ?_
    · have : (fun x => U x i) = Ui i := by funext x; simp [hU]
      rw [this]; exact hUim i
    · calc ∑ i, eLpNorm (fun x => U x i) (ENNReal.ofReal p) volume
          ≤ ∑ i : Fin d, ENNReal.ofReal CB * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hUi' : (fun x => U x i) = Ui i := by funext x; simp [hU]
            rw [hUi']
            refine (tsamp_conv_eLpNorm_le hΦi hΦm (huim i).measurable hp1).trans ?_
            have : ENNReal.ofReal (∫ y, ‖Φ y‖) ≤ ENNReal.ofReal CB :=
              ENNReal.ofReal_le_ofReal (by simpa using hΦL)
            exact mul_le_mul' this (huin i)
        _ ≤ ENNReal.ofReal (d * (CB + Cs)) * eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
              ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            nlinarith
  · -- sampling
    have e1 : (0 : ℝ) - d + ((d + 1 : ℕ) : ℝ) = 1 := by push_cast; ring
    have e0 : (0 : ℝ) - d - 0 = -(d : ℝ) := by ring
    obtain ⟨hnear0, hfar0⟩ := hpsi (η / 2) hη' hη'1
    have hnear : ∀ x : Torus d, x ≠ 0 → KernelGrad.tdist x 0 ≤ η →
        |K x| ≤ B * 2 ^ d * η ^ ((0 : ℝ) - d - 0) * KernelGrad.tdist x 0 ^ (0 : ℝ) := by
      intro x hx _
      have h1 := hnear0 x hx
      rw [Real.rpow_zero, mul_one, e0]
      have e : (η / 2) ^ (-(d : ℝ)) = 2 ^ d * η ^ (-(d : ℝ)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_neg hη.le, Real.div_rpow hη.le (by norm_num),
          Real.rpow_natCast, Real.rpow_natCast, inv_div, div_eq_mul_inv]
      rw [e] at h1
      linarith
    have hfar : ∀ x : Torus d, η ≤ KernelGrad.tdist x 0 →
        |K x| ≤ Cm / 2 * η ^ ((0 : ℝ) - d + ((d + 1 : ℕ) : ℝ)) *
          KernelGrad.tdist x 0 ^ (-((d + 1 : ℕ) : ℝ)) := by
      intro x hx
      have h1 := hfar0 x (by linarith)
      rw [e1, Real.rpow_one] at h1 ⊢
      linarith
    have hE : ∀ i, (∫⁻ y, ‖u y i‖ₑ ^ p) ^ (1 / p) =
        eLpNorm (fun x => u x i) (ENNReal.ofReal p) volume := by
      intro i
      rw [eLpNorm_eq_lintegral_rpow_enorm (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hp0.le]
      exact (huim i).aestronglyMeasurable
    have hKc : Continuous K := tkr_perio_psi_continuous (inv_pos.2 hη')
    refine (tsamp_cellSup_vec hp1 u (B := ENNReal.ofReal (Cs * η ^ ((0 : ℝ) - d / p)) *
      eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume) (fun i => ?_)).trans ?_
    · refine (hprofs η hη hη1 K hKm hnear hfar (fun y => ‖u y i‖ₑ) (fun x => ‖u x i‖ₑ)
        (huim i).measurable.enorm (fun x => ?_)).trans ?_
      · have hr := tsamp_repro_everywhere hd1 hη hη1 (huim i) (hsupp i) x
        rw [hr]
        refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
        refine lintegral_congr fun y => ?_
        rw [enorm_mul, Real.enorm_eq_ofReal_abs]
      · rw [hE i]
        exact mul_le_mul' le_rfl (huin i)
    · have e2 : (0 : ℝ) - d / p = -(d : ℝ) / p := by ring
      rw [e2]
      calc (d : ℝ≥0∞) * (ENNReal.ofReal (Cs * η ^ (-(d : ℝ) / p)) *
            eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume)
          = ENNReal.ofReal (d * (Cs * η ^ (-(d : ℝ) / p))) *
            eLpNorm (fun x => ‖u x‖) (ENNReal.ofReal p) volume := by
            rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg d)]
        _ ≤ _ := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            have ht : 0 ≤ η ^ (-(d : ℝ) / p) := Real.rpow_nonneg hη.le _
            nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hCB.le) ht]

end HRS.Commutator.TorusNote
