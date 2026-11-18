import HRS.MC.E213U10M
import HRS.MC.S7FCF5JB
import HRS.MC.S7FCD5B
import HRS.MC.S7UCD5

/-!
# Packet e213u10, part N: almost-sure facts about the particle windows

* `u10_bq_ae_eq`, `u10_cD_ae_eq`: the `L²` representative of `toL2 (F (b+·))` is a.e. `F` on `[b,b+L]`;
* `u10_pathAt_toPath`: evaluation of `toPath` at a point;
* `u10_B_memLp_ae`: a.s. the window of the centred quadratic field `ℬ_N` is in `L²([0,L];E_r)` (so `toL2` is not junk).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

theorem u10_bq_ae_eq (b L : ℝ) (F : ℝ → NegSobolev d (rLvl d))
    (hF : MemLp (fun t => F (b + t)) 2 (volume.restrict (Set.Icc (0 : ℝ) L))) :
    ∀ᵐ v ∂(volume.restrict (Set.Icc b (b + L))),
      u10_bq b L (toL2 (rLvl d) L (fun t => F (b + t))) v = F v := by
  have h1 : ((toL2 (rLvl d) L (fun t => F (b + t)) : L2Path d (rLvl d) L) : ℝ → NegSobolev d (rLvl d)) =ᵐ[
      volume.restrict (Set.Icc (0 : ℝ) L)] fun t => F (b + t) := by
    unfold toL2
    rw [dif_pos hF]
    exact MemLp.coeFn_toLp hF
  have h2 := (u10_translate_hmp b L).quasiMeasurePreserving.ae_eq_comp h1
  filter_upwards [h2] with v hv
  have e : b + (v - b) = v := by ring
  have := hv
  simp only [Function.comp, e] at this
  exact this

theorem u10_cD_ae_eq (hE : EdgeworthHyp S β₀ m) (T a b L : ℝ) (hH : a + T ≤ b + L)
    (F : ℝ → NegSobolev d (rLvl d))
    (hF : MemLp (fun t => F (b + t)) 2 (volume.restrict (Set.Icc (0 : ℝ) L))) (c : ℝ → NegSobolev d m)
    (hc : ∀ v, c v = if b ≤ v then NegSobolev.embed m (F v) else 0) :
    ∀ᵐ v ∂(volume : Measure ℝ), v ∈ Set.Icc (0 : ℝ) (a + T) →
      c v = u10_cD b L m (toL2 (rLvl d) L (fun t => F (b + t))) v := by
  have h := (ae_restrict_iff' measurableSet_Icc).1 (u10_bq_ae_eq b L F hF)
  filter_upwards [h] with v hv hvm
  rw [hc v]
  unfold u10_cD nearCoef
  by_cases hbv : b ≤ v
  · have h1 := hv ⟨hbv, hvm.2.trans hH⟩
    simp only [if_pos hbv, h1]
  · simp only [if_neg hbv]

theorem u10_pathAt_toPath {Ω : Type} (r T : ℝ) (Y : ℝ → Ω → NegSobolev d r) (ω : Ω)
    (h : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pathAt (toPath r T Y ω) t = Y t ω := by
  rw [u10_pathAt_eq _ ⟨t, ht⟩]
  exact HRS.MC.Sec7.S7FCD5B.S7FCD5B_toPath_apply r T Y ω h ⟨t, ht⟩

theorem u10_B_memLp_ae (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (b L : ℝ) (hb : 0 ≤ b) (hL : 0 < L)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hprep : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X) :
    ∀ᵐ ω ∂P, MemLp (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (b + t) ω) 2
      (volume.restrict (Set.Icc (0 : ℝ) L)) := by
  obtain ⟨C0, hC0⟩ := HRS.MC.Sec7.S7FCF5F.fcf5_F6a_B_section_moment_proof R r hr 3 (by norm_num)
  have hS := hprep.solution L
  obtain ⟨Fp, hFp, N0, hN0m, hN0, hkey⟩ :=
    HRS.MC.Sec7.S7FCF5J.S7FCF5J_joint_modif R r b L hL hb P X hS.adapted hS.cont
  set μL : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) L) with hμL
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) L, ∫⁻ ω, ‖Fp t ω‖ₑ ^ (3 : ℝ) ∂P ≤ ENNReal.ofReal C0 := by
    intro t ht
    have h1 : ∫⁻ ω, ‖Fp t ω‖ₑ ^ (3 : ℝ) ∂P =
        ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (b + t) ω‖ₑ ^ (3 : ℝ) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
      rw [hkey ω hω t ht]
    rw [h1]
    exact hC0 N hN P X₀ W X hprep (b + t) (add_nonneg hb ht.1)
  have hf : Measurable fun p : Ω × ℝ => ‖Fp p.2 p.1‖ₑ ^ (3 : ℝ) :=
    (hFp.comp measurable_swap).enorm.pow_const _
  have hTon : ∫⁻ ω, ∫⁻ t, ‖Fp t ω‖ₑ ^ (3 : ℝ) ∂μL ∂P = ∫⁻ t, ∫⁻ ω, ‖Fp t ω‖ₑ ^ (3 : ℝ) ∂P ∂μL :=
    lintegral_lintegral_swap hf.aemeasurable
  have hle : ∫⁻ t, ∫⁻ ω, ‖Fp t ω‖ₑ ^ (3 : ℝ) ∂P ∂μL ≤ ENNReal.ofReal C0 * ENNReal.ofReal L := by
    calc ∫⁻ t, ∫⁻ ω, ‖Fp t ω‖ₑ ^ (3 : ℝ) ∂P ∂μL ≤ ∫⁻ _t, ENNReal.ofReal C0 ∂μL := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact hbd t ht
      _ = ENNReal.ofReal C0 * ENNReal.ofReal L := by
          rw [lintegral_const, hμL, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hne : ∫⁻ ω, ∫⁻ t, ‖Fp t ω‖ₑ ^ (3 : ℝ) ∂μL ∂P ≠ ⊤ := by
    rw [hTon]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hle
  have hmeas : AEMeasurable (fun ω => ∫⁻ t, ‖Fp t ω‖ₑ ^ (3 : ℝ) ∂μL) P :=
    (hf.lintegral_prod_right').aemeasurable
  have hae := ae_lt_top' hmeas hne
  filter_upwards [hae, measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω1 hω2
  have hsm : AEStronglyMeasurable (fun t => Fp t ω) μL :=
    (hFp.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have h3 : MemLp (fun t => Fp t ω) 3 μL := by
    have hlt : eLpNorm (fun t => Fp t ω) 3 μL < ⊤ := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top hsm]
      simp only [ENNReal.toReal_ofNat]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hω1.ne
    exact hlt
  have : IsFiniteMeasure μL := ⟨by rw [hμL, Measure.restrict_apply_univ]; simp⟩
  have h2 : MemLp (fun t => Fp t ω) 2 μL := h3.mono_exponent (by norm_num)
  refine h2.ae_eq ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hkey ω hω2 t ht

end HRS.MC.E213U10

end
