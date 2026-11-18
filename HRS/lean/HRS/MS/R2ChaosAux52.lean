import HRS.MS.R2ChaosTie
import HRS.MS.R2PolyTie

/-!
# HRS.MS.R2ChaosAux52 -- S9.6 (P1): polynomial-envelope kernels lie in `L^q(μ⊗μ)` for `q s < d`

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_exists_eps (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ ε : ℝ, 0 < ε ∧ (2 + ε) * s < d := by
  have h2 : 0 < (d : ℝ) - 2 * s := by linarith
  refine ⟨((d : ℝ) - 2 * s) / (2 * s + 1), by positivity, ?_⟩
  have : (2 + ((d : ℝ) - 2 * s) / (2 * s + 1)) * s = 2 * s + ((d : ℝ) - 2 * s) * (s / (2 * s + 1)) := by
    field_simp
  rw [this]
  have h3 : s / (2 * s + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  nlinarith

theorem s94_exists_holder {s q : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hqs : q * s < d) :
    ∃ p : ℝ, 1 < p ∧ q * p * s < d := by
  rcases hs0.eq_or_lt with h0 | hpos
  · refine ⟨2, by norm_num, ?_⟩
    have hd0 : (0 : ℝ) < d := by rw [← h0] at hqs; simpa using hqs
    rw [← h0]; simpa using hd0
  · refine ⟨(1 + (d : ℝ) / (q * s)) / 2, ?_, ?_⟩
    · have : 1 < (d : ℝ) / (q * s) := by rw [lt_div_iff₀ (by positivity)]; linarith
      linarith
    · have : q * ((1 + (d : ℝ) / (q * s)) / 2) * s = (q * s + d) / 2 := by field_simp
      rw [this]; linarith

theorem s94_add_rpow_le {a b e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) :
    (a + b) ^ e ≤ 2 ^ e * (a ^ e + b ^ e) := by
  have h1 : a + b ≤ 2 * max a b := by linarith [le_max_left a b, le_max_right a b]
  calc (a + b) ^ e ≤ (2 * max a b) ^ e := Real.rpow_le_rpow (by positivity) h1 he
    _ = 2 ^ e * max a b ^ e := Real.mul_rpow (by norm_num) (le_max_of_le_left ha)
    _ ≤ 2 ^ e * (a ^ e + b ^ e) := by
        gcongr
        rcases le_total a b with h | h
        · rw [max_eq_right h]; linarith [Real.rpow_nonneg ha e]
        · rw [max_eq_left h]; linarith [Real.rpow_nonneg hb e]

section PolyLq

variable {s M L C₀ c₀ : ℝ} {ρ : Euc d → ℝ}

theorem s94_moment_rpow (hρ : Whole.IsProbDensity ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) {a : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, ∫⁻ y, ENNReal.ofReal (jbracket y ^ a) ∂(Whole.withDensityReal ρ) ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.R2Poly.s95_moment d C₀ c₀ hG.1 (Pw := a / 2) (by positivity)
  refine ⟨C, le_trans (le_of_eq ?_) (hC ρ hρ hG.2)⟩
  refine lintegral_congr fun y => ?_
  congr 1
  have hb : 0 ≤ jbracket y := by linarith [HRS.MS.R2Poly.s95_one_le_jb y]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
  congr 1; push_cast; ring

theorem s94_lintegral_fst (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {φ : Euc d → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ z : Euc d × Euc d, φ z.1 ∂(μ.prod μ) = ∫⁻ x, φ x ∂μ := by
  rw [← lintegral_map hφ measurable_fst, Measure.map_fst_prod]
  simp

theorem s94_lintegral_snd (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {φ : Euc d → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ z : Euc d × Euc d, φ z.2 ∂(μ.prod μ) = ∫⁻ x, φ x ∂μ := by
  rw [← lintegral_map hφ measurable_snd, Measure.map_snd_prod]
  simp

theorem s94_poly_memLp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hρ : IsRound2Density d s M L ρ)
    (hG : HasR2GaussianUpper C₀ c₀ ρ) {Pw B : ℝ} (hPw : 0 ≤ Pw) (hB : 0 ≤ B) {g : Euc d → Euc d → ℝ}
    (hg : IsR2PolyPairKernel s Pw B g) {q : ℝ} (hq : 1 ≤ q) (hqs : q * s < d) :
    MemLp (fun z : Euc d × Euc d => g z.1 z.2) (ENNReal.ofReal q)
      ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ)) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  set μ := Whole.withDensityReal ρ with hμ
  set ν := μ.prod μ with hν
  have hq0 : 0 < q := by linarith
  obtain ⟨p, hp1, hpqs⟩ := s94_exists_holder hs0 hq0 hqs
  have hHC : (Real.conjExponent p).HolderConjugate p := (Real.HolderConjugate.conjExponent hp1).symm
  have hp'0 : 0 < Real.conjExponent p := hHC.pos
  have hp0 : 0 < p := by linarith
  set e := Pw * q with he
  have he0 : 0 ≤ e := mul_nonneg hPw hq0.le
  have hjb0 : ∀ x : Euc d, 0 < jbracket x := fun x => zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)
  have hVm : Measurable fun z : Euc d × Euc d => ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.add
      ((HRS.MS.Wr.wr3_measurable_rieszWeight (d := d) s).comp (measurable_fst.sub measurable_snd))).pow_const q)
  have hVfin : ∫⁻ z : Euc d × Euc d, ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ (q * p)) ∂ν ≠ ⊤ := by
    have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
    exact HRS.Whole.U1.u1_lintegral_prod_Vs (volume : Measure (Euc d)) hs0 (by positivity)
      (by rw [hfr]; exact hpqs) μ (HRS.Whole.U1.u1_le_smul hρ.bdd)
  -- polynomial moment
  obtain ⟨Cm, hCm⟩ := s94_moment_rpow (d := d) hρ.prob hG (a := e * Real.conjExponent p) (by positivity)
  have hfm : ∀ x : Euc d, Measurable fun x : Euc d => ENNReal.ofReal (jbracket x ^ e) := fun _ =>
    ENNReal.measurable_ofReal.comp (HRS.MS.R2Poly.s95_jb_meas.pow_const e)
  have hmomfin : ∫⁻ x, ENNReal.ofReal (jbracket x ^ (e * Real.conjExponent p)) ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCm
  have hpowp : ∀ x : Euc d, ENNReal.ofReal (jbracket x ^ e) ^ Real.conjExponent p =
      ENNReal.ofReal (jbracket x ^ (e * Real.conjExponent p)) := fun x => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (hjb0 x).le _) hp'0.le,
      ← Real.rpow_mul (hjb0 x).le]
  have hVp : ∀ z : Euc d × Euc d, ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q) ^ p =
      ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ (q * p)) := fun z => by
    have hW := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (z.1 - z.2)
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (by linarith) _) hp0.le,
      ← Real.rpow_mul (by linarith)]
  -- Hölder for both weights
  have hH1 : ∫⁻ z : Euc d × Euc d, ENNReal.ofReal (jbracket z.1 ^ e) *
      ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q) ∂ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.lintegral_mul_le_Lp_mul_Lq ν hHC
      (f := fun z : Euc d × Euc d => ENNReal.ofReal (jbracket z.1 ^ e))
      (g := fun z : Euc d × Euc d => ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q))
      (((hfm 0).comp measurable_fst).aemeasurable) hVm.aemeasurable)
    beta_reduce
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_)
    · simp_rw [hpowp]
      have h := s94_lintegral_fst μ (φ := fun x : Euc d => ENNReal.ofReal (jbracket x ^ (e * Real.conjExponent p)))
        (ENNReal.measurable_ofReal.comp (HRS.MS.R2Poly.s95_jb_meas.pow_const _))
      rw [hν] at *
      rw [h]; exact hmomfin
    · simp_rw [hVp]; exact hVfin
  have hH2 : ∫⁻ z : Euc d × Euc d, ENNReal.ofReal (jbracket z.2 ^ e) *
      ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q) ∂ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.lintegral_mul_le_Lp_mul_Lq ν hHC
      (f := fun z : Euc d × Euc d => ENNReal.ofReal (jbracket z.2 ^ e))
      (g := fun z : Euc d × Euc d => ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q))
      (((hfm 0).comp measurable_snd).aemeasurable) hVm.aemeasurable)
    beta_reduce
    refine ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_)
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_)
    · simp_rw [hpowp]
      have h := s94_lintegral_snd μ (φ := fun x : Euc d => ENNReal.ofReal (jbracket x ^ (e * Real.conjExponent p)))
        (ENNReal.measurable_ofReal.comp (HRS.MS.R2Poly.s95_jb_meas.pow_const _))
      rw [hν] at *
      rw [h]; exact hmomfin
    · simp_rw [hVp]; exact hVfin
  -- pointwise domination
  set K : ℝ := B ^ q * 2 ^ e with hK
  have hpt : ∀ᵐ z ∂ν, ‖g z.1 z.2‖ₑ ^ q ≤ ENNReal.ofReal K *
      (ENNReal.ofReal (jbracket z.1 ^ e) * ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q) +
        ENNReal.ofReal (jbracket z.2 ^ e) * ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q)) := by
    filter_upwards [s94_ae_offdiag hd hρ] with z hz
    have hW := HRS.MS.Wr.wr3_rieszWeight_nonneg (d := d) s (z.1 - z.2)
    have hb := hg.bound z.1 z.2 hz
    have ha1 := hjb0 z.1
    have ha2 := hjb0 z.2
    have hV0 : 0 ≤ 1 + rieszWeight s (z.1 - z.2) := by linarith
    have h1 : |g z.1 z.2| ^ q ≤ K * (jbracket z.1 ^ e + jbracket z.2 ^ e) * (1 + rieszWeight s (z.1 - z.2)) ^ q := by
      calc |g z.1 z.2| ^ q ≤ (B * (jbracket z.1 + jbracket z.2) ^ Pw * (1 + rieszWeight s (z.1 - z.2))) ^ q :=
            Real.rpow_le_rpow (abs_nonneg _) hb hq0.le
        _ = B ^ q * (jbracket z.1 + jbracket z.2) ^ e * (1 + rieszWeight s (z.1 - z.2)) ^ q := by
            rw [Real.mul_rpow (by positivity) hV0, Real.mul_rpow hB (Real.rpow_nonneg (by positivity) _),
              ← Real.rpow_mul (by positivity)]
        _ ≤ B ^ q * (2 ^ e * (jbracket z.1 ^ e + jbracket z.2 ^ e)) * (1 + rieszWeight s (z.1 - z.2)) ^ q := by
            gcongr
            exact s94_add_rpow_le ha1.le ha2.le he0
        _ = _ := by rw [hK]; ring
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hq0.le]
    refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
    have hKn : 0 ≤ K := by rw [hK]; positivity
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_add (Real.rpow_nonneg ha1.le _) (Real.rpow_nonneg ha2.le _)]
    ring
  have hgm : AEStronglyMeasurable (fun z : Euc d × Euc d => g z.1 z.2) ν := hg.measurable.aestronglyMeasurable
  have hint : ∫⁻ z : Euc d × Euc d, ‖g z.1 z.2‖ₑ ^ q ∂ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hpt)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left
      (f := fun z : Euc d × Euc d => ENNReal.ofReal (jbracket z.1 ^ e) *
        ENNReal.ofReal ((1 + rieszWeight s (z.1 - z.2)) ^ q))
      ((((hfm 0).comp measurable_fst).mul hVm))]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hH1, hH2⟩)
  show eLpNorm _ (ENNReal.ofReal q) ν < ⊤
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hq0).ne' ENNReal.ofReal_ne_top hgm,
    ENNReal.toReal_ofReal hq0.le]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hint

end PolyLq

end HRS.MS.R2Chaos
