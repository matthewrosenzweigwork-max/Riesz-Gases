import HRS.Commutator.Torus.TSAMPAux29

/-!
# T-SAMP helpers, part 30: `vhi_cell_sampling_T` (assembly)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s : ℝ}

lemma tsamp_alpha_p1 (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    0 < Whole.alphaE d s ∧ Whole.alphaE d s < d ∧ 1 < Whole.p1E d s ∧
      (d : ℝ) < Whole.alphaE d s * Whole.p1E d s ∧ Whole.alphaE d s - d / Whole.p1E d s = 1 := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hq2 : 0 < (d : ℝ) - s - 2 := by linarith
  have e : Whole.alphaE d s * Whole.p1E d s = d + 2 * d / ((d : ℝ) - s - 2) := by
    unfold Whole.alphaE Whole.p1E; field_simp; ring
  refine ⟨by unfold Whole.alphaE; linarith, by unfold Whole.alphaE; linarith, ?_, ?_, ?_⟩
  · unfold Whole.p1E; rw [one_lt_div hq2]; linarith
  · rw [e]; have : 0 < 2 * (d : ℝ) / ((d : ℝ) - s - 2) := by positivity
    linarith
  · unfold Whole.alphaE Whole.p1E; field_simp; ring

theorem tsamp_vhi_cell_core (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (L : ℝ) (w : Torus d → Euc d)
      (F : ℝ), 0 ≤ F → 0 ≤ L → IsLipschitzVF L v → IsFracDeriv (Whole.alphaE d s) v w →
      eLpNorm (fun x => ‖w x‖) (ENNReal.ofReal (Whole.p1E d s)) volume ≤ ENNReal.ofReal F →
        cellSupNorm η (Whole.p1E d s) (PgtT η v) ≤ ENNReal.ofReal (C * η * F) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hα, hαd, hp1, hαp, hαdp⟩ := tsamp_alpha_p1 hd hs0 hsd
  set p : ℝ := Whole.p1E d s with hp
  have hp0 : 0 < p := by linarith
  set q : ℝ := p.conjExponent with hqdef
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hq1 : 1 < q := hpq.symm.lt
  have hqp : q * (p - 1) = p := by
    have : p - 1 ≠ 0 := by linarith
    rw [hqdef, Real.conjExponent]; field_simp
  have haq : -(d : ℝ) < (Whole.alphaE d s - d) * q := by
    have h : ((Whole.alphaE d s - d) * q + d) * (p - 1) = Whole.alphaE d s * p - d := by
      linear_combination (Whole.alphaE d s - d) * hqp
    have h2 : 0 < ((Whole.alphaE d s - d) * q + d) * (p - 1) := by rw [h]; linarith
    have h3 : 0 < (Whole.alphaE d s - d) * q + d := by
      by_contra hneg
      push Not at hneg
      nlinarith [mul_nonneg (neg_nonneg.2 hneg) (by linarith : (0 : ℝ) ≤ p - 1)]
    linarith
  obtain ⟨Kt, hKm, hKi, hFT, C₀, hC₀, hnear, Cf, hCf, hfar⟩ :=
    tsamp_Kalpha_data hd1 (Whole.alphaE d s) hα hαd
  obtain ⟨C, hC, Cm, hCm, hmain⟩ := tsamp_gk hd1 (Whole.alphaE d s - d) (Whole.alphaE d s)
    (by linarith) (by linarith) hα.le hKm hKi hC₀ hnear Cf hCf hfar
  obtain ⟨Cs, hCs, hprof⟩ := tsamp_profile_sampling hd1 hpq (a := Whole.alphaE d s - d)
    (γ := Whole.alphaE d s) (C := C) (Cm := Cm (d + 1)) (by linarith) haq hC.le (hCm _).le
  refine ⟨d * Cs, by positivity, ?_⟩
  intro η hη hη1 v L w F hF hL hLip hrep hnorm
  have hP1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1.le
  obtain ⟨w', hw'm, hw'le, hrep'⟩ := tsamp_reduce_w hα hrep
  have hw'n : eLpNorm (fun x => ‖w' x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F :=
    (eLpNorm_mono_ae hw'm.norm.aestronglyMeasurable
      (hw'le.mono fun x hx => by simpa using hx)).trans hnorm
  have hwjm : ∀ i, Measurable fun x => w' x i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp hw'm
  have hwjn : ∀ i, eLpNorm (fun x => w' x i) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal F := fun i =>
    (eLpNorm_mono_ae (hwjm i).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        simpa using PiLp.norm_apply_le (w' x) i)).trans hw'n
  have hwjmem : ∀ i, MemLp (fun x => w' x i) (ENNReal.ofReal p) volume := fun i =>
    memLp_iff.2 (lt_of_le_of_lt (hwjn i) ENNReal.ofReal_lt_top)
  have hwji : ∀ i, Integrable fun x => w' x i := fun i => (hwjmem i).integrable hP1
  obtain ⟨hKint, hcoef, hnear', hfar', -⟩ := hmain η hη hη1
  set Kα : Torus d → ℝ := perio (textKeta Kt (Whole.alphaE d s) η) with hKα
  have hKαm : Measurable Kα := tpos_perio_measurable (text_Keta_measurable hKm _ η)
  have hKαc : ∀ k : Lattice d, Torus.fcoef Kα k = ((if k = 0 then 0 else
      (1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * Lattice.enorm k) ^ (-Whole.alphaE d s) : ℝ) : ℂ) := by
    intro k
    rw [hcoef k, hFT, text_symbol_scale hα.ne' hη k]
  have hKαL : MemLp Kα (ENNReal.ofReal q) volume :=
    tsamp_memLp_profile hd1 hq1 haq hC.le (hCm _).le hη hKαm hnear' (hfar' (d + 1))
  have hPgtc : Continuous (PgtT η v) := by
    obtain ⟨C', hC', hb⟩ := tsamp_vhi_bounded_core (d := d) hd1
    exact (hb η hη hη1 v L hL hLip).1
  have hbd : ∀ i : Fin d, (∑ j : Fin d → Fin (nCells η),
      (⨆ x ∈ cellT (nCells η) j, ‖PgtT η v x i‖ₑ) ^ p) ^ (1 / p) ≤
        ENNReal.ofReal (Cs * η) * ENNReal.ofReal F := by
    intro i
    have hae := tsamp_Pgt_ae_conv hd1 hη hη1 hKint hKαc hL hLip hwji hrep' i
    have hcA : Continuous (fun x => ∫ y, Kα (x - y) * w' y i) :=
      tsamp_continuous_conv hpq hKαL (hwjmem i)
    have hid : ∀ x, PgtT η v x i = ∫ y, Kα (x - y) * w' y i := by
      have hc1 : Continuous fun x => PgtT η v x i :=
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hPgtc
      have hae' : (fun x => PgtT η v x i) =ᵐ[volume] fun x => ∫ y, Kα (x - y) * w' y i := by
        refine hae.trans (Eventually.of_forall fun x => ?_)
        simp [tsampConv]
      exact fun x => congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Torus d)) hc1 hcA).1 hae') x
    have hu : ∀ x, ‖PgtT η v x i‖ₑ ≤ ∫⁻ y, ENNReal.ofReal |Kα (x - y)| * ‖w' y i‖ₑ := by
      intro x
      rw [hid x]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun y => ?_
      rw [enorm_mul, Real.enorm_eq_ofReal_abs]
    have h1 := hprof η hη hη1 Kα hKαm hnear' (hfar' (d + 1)) (fun y => ‖w' y i‖ₑ) (fun x => ‖PgtT η v x i‖ₑ)
      (hwjm i).enorm hu
    refine h1.trans ?_
    have hgp : (∫⁻ y, ‖w' y i‖ₑ ^ p) ^ (1 / p) = eLpNorm (fun x => w' x i) (ENNReal.ofReal p) volume := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
        (hwjm i).aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
    rw [hgp, hαdp] at *
    rw [Real.rpow_one]
    exact mul_le_mul' le_rfl (hwjn i)
  have hvec := tsamp_cellSup_vec (η := η) hp1 (PgtT η v) hbd
  refine hvec.trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end HRS.Commutator.TorusNote
