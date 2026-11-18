import HRS.Commutator.Whole.Defs

/-!
# Integrability of the energy and commutator integrands (packet CMX-APPROX, helpers)

Helpers carry the prefix `cmxSA_`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma cmxSA_finrank : Module.finrank ℝ (Euc d) = d := by simp [Euc]

/-- Abstract Tonelli bound: if `‖k x y‖ ≤ m (x-y) + A + W x + W y` with `sup_a ∫ m(a-y)|ρ| ≤ B`. -/
lemma cmxSA_inner_bound {k : Euc d → Euc d → ℝ} (ρ : Euc d → ℝ) (hρm : Measurable ρ)
    (m W : Euc d → ℝ) (hm : Measurable m) (hm0 : ∀ z, 0 ≤ m z) (hW : Measurable W)
    (hW0 : ∀ x, 0 ≤ W x) (A : ℝ) (hA : 0 ≤ A)
    (B : ℝ≥0∞) (hconv : ∀ a, ∫⁻ y, ‖m (a - y)‖ₑ * ‖ρ y‖ₑ ≤ B)
    (hbound : ∀ x y, ‖k x y‖ ≤ m (x - y) + A + W x + W y) (x : Euc d) :
    ∫⁻ y, ‖k x y‖ₑ * ‖ρ y‖ₑ ≤ B + (ENNReal.ofReal A + ENNReal.ofReal (W x)) * (∫⁻ y, ‖ρ y‖ₑ) +
      (∫⁻ y, ENNReal.ofReal (W y) * ‖ρ y‖ₑ) := by
  have h1 : ∀ y, ‖k x y‖ₑ * ‖ρ y‖ₑ ≤ ‖m (x - y)‖ₑ * ‖ρ y‖ₑ + (ENNReal.ofReal A +
      ENNReal.ofReal (W x)) * ‖ρ y‖ₑ + ENNReal.ofReal (W y) * ‖ρ y‖ₑ := by
    intro y
    have : ‖k x y‖ₑ ≤ ‖m (x - y)‖ₑ + (ENNReal.ofReal A + ENNReal.ofReal (W x)) +
        ENNReal.ofReal (W y) := by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hm0 _)]
      refine le_trans (ENNReal.ofReal_le_ofReal (hbound x y)) ?_
      rw [ENNReal.ofReal_add (by linarith [hm0 (x - y), hW0 x]) (hW0 y),
        ENNReal.ofReal_add (by linarith [hm0 (x - y)]) (hW0 x),
        ENNReal.ofReal_add (hm0 _) hA]
      apply le_of_eq; ring
    calc ‖k x y‖ₑ * ‖ρ y‖ₑ ≤ (‖m (x - y)‖ₑ + (ENNReal.ofReal A + ENNReal.ofReal (W x)) +
        ENNReal.ofReal (W y)) * ‖ρ y‖ₑ := by gcongr
      _ = _ := by ring
  calc ∫⁻ y, ‖k x y‖ₑ * ‖ρ y‖ₑ
      ≤ ∫⁻ y, (‖m (x - y)‖ₑ * ‖ρ y‖ₑ + (ENNReal.ofReal A + ENNReal.ofReal (W x)) * ‖ρ y‖ₑ +
        ENNReal.ofReal (W y) * ‖ρ y‖ₑ) := lintegral_mono h1
    _ = (∫⁻ y, ‖m (x - y)‖ₑ * ‖ρ y‖ₑ) + (ENNReal.ofReal A + ENNReal.ofReal (W x)) *
          (∫⁻ y, ‖ρ y‖ₑ) + (∫⁻ y, ENNReal.ofReal (W y) * ‖ρ y‖ₑ) := by
      rw [lintegral_add_left, lintegral_add_left, lintegral_const_mul]
      · exact hρm.enorm
      · exact (hm.comp (measurable_const.sub measurable_id)).enorm.mul hρm.enorm
      · exact ((hm.comp (measurable_const.sub measurable_id)).enorm.mul hρm.enorm).add
          (hρm.enorm.const_mul _)
    _ ≤ _ := by gcongr; exact hconv x

lemma cmxSA_core_integrable {k : Euc d → Euc d → ℝ}
    (hk : Measurable (fun q : Euc d × Euc d => k q.1 q.2)) (ρ : Euc d → ℝ)
    (hρm : Measurable ρ) (hρ1 : Integrable ρ)
    (m W : Euc d → ℝ) (hm : Measurable m) (hm0 : ∀ z, 0 ≤ m z) (hW : Measurable W)
    (hW0 : ∀ x, 0 ≤ W x) (hWρ : Integrable (fun x => W x * ρ x)) (A : ℝ) (hA : 0 ≤ A)
    (B : ℝ≥0∞) (hB : B < ⊤) (hconv : ∀ a, ∫⁻ y, ‖m (a - y)‖ₑ * ‖ρ y‖ₑ ≤ B)
    (hbound : ∀ x y, ‖k x y‖ ≤ m (x - y) + A + W x + W y) :
    (∀ a, Integrable (fun y => k a y * ρ y)) ∧
      Integrable (fun q : Euc d × Euc d => k q.1 q.2 * ρ q.1 * ρ q.2) := by
  have hI1 : ∫⁻ y, ‖ρ y‖ₑ < ⊤ := hρ1.hasFiniteIntegral
  have hI2 : ∫⁻ y, ENNReal.ofReal (W y) * ‖ρ y‖ₑ < ⊤ := by
    have := hWρ.hasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine lintegral_congr fun y => ?_
    rw [enorm_mul, Real.enorm_eq_ofReal (hW0 y)]
  have inner := cmxSA_inner_bound (k := k) ρ hρm m W hm hm0 hW hW0 A hA B hconv hbound
  have hk1 : ∀ a, Measurable (fun y => k a y) := fun a =>
    hk.comp (measurable_const.prodMk measurable_id)
  refine ⟨fun a => ⟨((hk1 a).mul hρm).aestronglyMeasurable, ?_⟩, ?_⟩
  · refine lt_of_le_of_lt ?_ (show B + (ENNReal.ofReal A + ENNReal.ofReal (W a)) *
      (∫⁻ y, ‖ρ y‖ₑ) + (∫⁻ y, ENNReal.ofReal (W y) * ‖ρ y‖ₑ) < ⊤ from ?_)
    · refine le_trans (le_of_eq ?_) (inner a)
      refine lintegral_congr fun y => ?_
      rw [enorm_mul]
    · refine ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hB, ENNReal.mul_lt_top
        (ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩) hI1⟩, hI2⟩
  · refine ⟨?_, ?_⟩
    · exact (((hk.mul (hρm.comp measurable_fst)).mul (hρm.comp measurable_snd))).aestronglyMeasurable
    · unfold HasFiniteIntegral
      have hmeas : Measurable (fun q : Euc d × Euc d => ‖k q.1 q.2 * ρ q.1 * ρ q.2‖ₑ) :=
        (((hk.mul (hρm.comp measurable_fst)).mul (hρm.comp measurable_snd))).enorm
      rw [Measure.volume_eq_prod, lintegral_prod _ hmeas.aemeasurable]
      set C0 : ℝ≥0∞ := B + ENNReal.ofReal A * (∫⁻ y, ‖ρ y‖ₑ) +
        (∫⁻ y, ENNReal.ofReal (W y) * ‖ρ y‖ₑ) with hC0
      have hC0t : C0 < ⊤ := ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨hB,
        ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI1⟩, hI2⟩
      have step : ∀ x, ∫⁻ y, ‖k x y * ρ x * ρ y‖ₑ ≤
          ‖ρ x‖ₑ * (C0 + (∫⁻ y, ‖ρ y‖ₑ) * ENNReal.ofReal (W x)) := by
        intro x
        have e : ∀ y, ‖k x y * ρ x * ρ y‖ₑ = ‖ρ x‖ₑ * (‖k x y‖ₑ * ‖ρ y‖ₑ) := by
          intro y; rw [enorm_mul, enorm_mul]; ring
        simp_rw [e]
        have hmx : Measurable (fun y => ‖k x y‖ₑ * ‖ρ y‖ₑ) := ((hk1 x).enorm).mul hρm.enorm
        rw [lintegral_const_mul _ hmx]
        gcongr
        refine le_trans (inner x) (le_of_eq ?_)
        rw [hC0, add_mul]; ring
      refine lt_of_le_of_lt (lintegral_mono step) ?_
      have : ∫⁻ x, ‖ρ x‖ₑ * (C0 + (∫⁻ y, ‖ρ y‖ₑ) * ENNReal.ofReal (W x)) =
          C0 * (∫⁻ x, ‖ρ x‖ₑ) + (∫⁻ y, ‖ρ y‖ₑ) * (∫⁻ x, ENNReal.ofReal (W x) * ‖ρ x‖ₑ) := by
        have e2 : ∀ x, ‖ρ x‖ₑ * (C0 + (∫⁻ y, ‖ρ y‖ₑ) * ENNReal.ofReal (W x)) =
            C0 * ‖ρ x‖ₑ + (∫⁻ y, ‖ρ y‖ₑ) * (ENNReal.ofReal (W x) * ‖ρ x‖ₑ) := by
          intro x; ring
        simp_rw [e2]
        have hmw : Measurable (fun x => ENNReal.ofReal (W x) * ‖ρ x‖ₑ) :=
          (hW.ennreal_ofReal).mul hρm.enorm
        rw [lintegral_add_left (hρm.enorm.const_mul _), lintegral_const_mul _ hρm.enorm,
          lintegral_const_mul _ hmw]
      rw [this]
      exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top hC0t hI1, ENNReal.mul_lt_top hI1 hI2⟩

/-- The local singular majorant `‖z‖^{-σ} 1_{‖z‖<1}`. -/
def cmxSA_m (σ : ℝ) (z : Euc d) : ℝ := if ‖z‖ < 1 then ‖z‖ ^ (-σ) else 0

lemma cmxSA_m_nonneg (σ : ℝ) (z : Euc d) : 0 ≤ cmxSA_m σ z := by
  unfold cmxSA_m; split_ifs
  · exact Real.rpow_nonneg (norm_nonneg _) _
  · exact le_rfl

lemma cmxSA_m_measurable (σ : ℝ) : Measurable (cmxSA_m σ : Euc d → ℝ) :=
  Measurable.ite (measurableSet_lt measurable_norm measurable_const)
    (measurable_norm.pow_const _) measurable_const

lemma cmxSA_m_memLp (hd : 1 ≤ d) {σ qr : ℝ} (hσ : 0 ≤ σ) (hq : 1 ≤ qr) (hσq : σ * qr < d) :
    MemLp (cmxSA_m σ : Euc d → ℝ) (ENNReal.ofReal qr) volume := by
  have hq0 : 0 < qr := by linarith
  rw [← integrable_norm_rpow_iff (cmxSA_m_measurable σ).aestronglyMeasurable
    (by simp [hq0]) (by simp), ENNReal.toReal_ofReal hq0.le]
  have h1 : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-(σ * qr))) (ball (0 : Euc d) 1) volume := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := σ * qr) ?_ ?_ ?_ ?_
    · rw [cmxSA_finrank]; exact hd
    · rw [cmxSA_finrank]; exact hσq
    · exact Filter.Eventually.of_forall fun z => by
        rw [one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    · exact (measurable_norm.pow_const _).aestronglyMeasurable
  have h2 : (fun z : Euc d => ‖cmxSA_m σ z‖ ^ qr) =
      (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-(σ * qr))) := by
    funext z
    unfold cmxSA_m
    by_cases hz : ‖z‖ < 1
    · rw [if_pos hz, Set.indicator_of_mem (by simpa using hz),
        Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        ← Real.rpow_mul (norm_nonneg _)]
      congr 1; ring
    · rw [if_neg hz, Set.indicator_of_notMem (by simpa using hz)]
      simp [Real.zero_rpow hq0.ne']
  rw [h2, integrable_indicator_iff measurableSet_ball]
  exact h1

lemma cmxSA_exponents (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) :
    1 < p ∧ ∃ qr σ : ℝ, 1 ≤ qr ∧ s ≤ σ ∧ 0 < σ ∧ σ * qr < d ∧
      (ENNReal.ofReal qr)⁻¹ + p⁻¹ = 1 := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) - s := by linarith
  have hdpos : (0 : ℝ) < d := by linarith
  have h1 : (1 : ℝ) ≤ (d : ℝ) / (d - s) := by
    rw [le_div_iff₀ hd0]; linarith
  have hp1 : 1 < p := lt_of_le_of_lt (by simpa using ENNReal.ofReal_le_ofReal h1) hp
  refine ⟨hp1, ?_⟩
  have hp0 : p ≠ 0 := by intro h; rw [h] at hp1; simp at hp1
  have hpinv : p⁻¹ < ENNReal.ofReal (((d : ℝ) - s) / d) := by
    have := ENNReal.inv_lt_inv.2 hp
    rw [← ENNReal.ofReal_inv_of_pos (by positivity)] at this
    simpa [inv_div] using this
  set t : ℝ := (p⁻¹).toReal with ht
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have htlt : t < ((d : ℝ) - s) / d :=
    ENNReal.toReal_lt_of_lt_ofReal hpinv
  have hpinvne : p⁻¹ ≠ ⊤ := by simpa using hp0
  have hpt : p⁻¹ = ENNReal.ofReal t := by rw [ht, ENNReal.ofReal_toReal hpinvne]
  have hkey : s < d * (1 - t) := by
    have := (lt_div_iff₀ hdpos).1 htlt
    nlinarith
  have h1t : 0 < 1 - t := by
    have : 0 ≤ s := hs0
    nlinarith
  refine ⟨1 / (1 - t), (s + d * (1 - t)) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h1t]; linarith
  · linarith
  · linarith
  · rw [div_mul_div_comm, div_lt_iff₀ (by positivity)]
    nlinarith
  · rw [hpt, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv,
      ← ENNReal.ofReal_add h1t.le ht0]
    simp

lemma cmxSA_conv_bound (hd : 1 ≤ d) {σ qr : ℝ} (hσ : 0 ≤ σ) (hq : 1 ≤ qr) (hσq : σ * qr < d)
    (p : ℝ≥0∞) (hpq : (ENNReal.ofReal qr)⁻¹ + p⁻¹ = 1) (ρ : Euc d → ℝ)
    (hρ : MemLp ρ p volume) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ a : Euc d, ∫⁻ y, ‖cmxSA_m σ (a - y)‖ₑ * ‖ρ y‖ₑ ≤ B := by
  haveI : ENNReal.HolderTriple (ENNReal.ofReal qr) p 1 := ⟨by simpa using hpq⟩
  have hm := cmxSA_m_memLp hd hσ hq hσq
  refine ⟨eLpNorm (cmxSA_m σ : Euc d → ℝ) (ENNReal.ofReal qr) volume * eLpNorm ρ p volume,
    ENNReal.mul_lt_top hm.eLpNorm_lt_top hρ.eLpNorm_lt_top, fun a => ?_⟩
  have hmeas : AEStronglyMeasurable (fun y => cmxSA_m σ (a - y)) volume :=
    ((cmxSA_m_measurable σ).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have h1 := eLpNorm_smul_le_mul_eLpNorm (p := ENNReal.ofReal qr) (q := p) (r := 1)
    hmeas hρ.aestronglyMeasurable (μ := volume)
  have h2 : eLpNorm (fun y => cmxSA_m σ (a - y)) (ENNReal.ofReal qr) volume =
      eLpNorm (cmxSA_m σ : Euc d → ℝ) (ENNReal.ofReal qr) volume := by
    have := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal qr)
      (cmxSA_m_measurable σ).aestronglyMeasurable (Measure.measurePreserving_sub_left volume a)
    exact this
  rw [h2, eLpNorm_one_eq_lintegral_enorm (hmeas.smul hρ.aestronglyMeasurable)] at h1
  refine le_trans (le_of_eq ?_) h1
  refine lintegral_congr fun y => ?_
  simp [enorm_mul]

/-! ### Kernel bounds -/

lemma cmxSA_kern_measurable (s : ℝ) : Measurable (kern s : Euc d → ℝ) := by
  unfold kern
  by_cases h : s = 0
  · simp only [h, if_true]
    exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [h, if_false]
    exact (measurable_norm.pow_const _).const_mul _

lemma cmxSA_kernGrad_measurable (s : ℝ) : Measurable (kernGrad s : Euc d → Euc d) := by
  unfold kernGrad
  exact ((measurable_norm.pow_const _).neg).smul measurable_id

lemma cmxSA_commKer_measurable (s : ℝ) {v : Euc d → Euc d} (hv : Measurable v) :
    Measurable (fun q : Euc d × Euc d => commKer (kernGrad s) v q.1 q.2) := by
  unfold commKer
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  exact ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).inner
    ((cmxSA_kernGrad_measurable s).comp (measurable_fst.sub measurable_snd))

/-- the logarithmic weight (`0` unless `s = 0`) -/
def cmxSA_W (s : ℝ) (x : Euc d) : ℝ := if s = 0 then Real.log (2 + ‖x‖) else 0

lemma cmxSA_W_nonneg (s : ℝ) (x : Euc d) : 0 ≤ cmxSA_W s x := by
  unfold cmxSA_W; split_ifs
  · exact Real.log_nonneg (by linarith [norm_nonneg x])
  · exact le_rfl

lemma cmxSA_W_measurable (s : ℝ) : Measurable (cmxSA_W s : Euc d → ℝ) := by
  unfold cmxSA_W
  by_cases h : s = 0
  · simp only [h, if_true]
    exact Real.measurable_log.comp (measurable_const.add measurable_norm)
  · simp only [h, if_false]; exact measurable_const

lemma cmxSA_kern_near (hs0 : 0 ≤ s) {σ : ℝ} (hσ : 0 < σ) (hsσ : s ≤ σ) (z : Euc d)
    (hz : ‖z‖ < 1) : ‖kern s z‖ ≤ (s⁻¹ + σ⁻¹) * ‖z‖ ^ (-σ) := by
  have hs1 : 0 ≤ s⁻¹ := inv_nonneg.2 hs0
  have hσ1 : 0 < σ⁻¹ := inv_pos.2 hσ
  by_cases hz0 : z = 0
  · subst hz0
    have h0 : (0 : ℝ) ^ (-σ) = 0 := Real.zero_rpow (by linarith)
    by_cases hs : s = 0
    · subst hs; simp [kern, h0]
    · have : (0 : ℝ) ^ (-s) = 0 := Real.zero_rpow (by intro h; apply hs; linarith)
      simp [kern, hs, this, h0]
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hp0 : 0 < ‖z‖ ^ (-σ) := Real.rpow_pos_of_pos hn _
    by_cases hs : s = 0
    · subst hs
      simp only [kern, if_true, norm_neg, Real.norm_eq_abs]
      have h1 : Real.log ‖z‖⁻¹ ≤ (‖z‖⁻¹) ^ σ / σ := Real.log_le_rpow_div (by positivity) hσ
      rw [Real.log_inv, Real.inv_rpow hn.le, ← Real.rpow_neg hn.le] at h1
      rw [abs_of_nonpos (Real.log_nonpos hn.le hz.le), inv_zero, zero_add]
      calc -Real.log ‖z‖ ≤ ‖z‖ ^ (-σ) / σ := h1
        _ = σ⁻¹ * ‖z‖ ^ (-σ) := by rw [div_eq_inv_mul, mul_comm]
    · simp only [kern, hs, if_false, Real.norm_eq_abs]
      have hp1 : 0 < ‖z‖ ^ (-s) := Real.rpow_pos_of_pos hn _
      rw [abs_of_nonneg (by positivity)]
      have : ‖z‖ ^ (-s) ≤ ‖z‖ ^ (-σ) :=
        Real.rpow_le_rpow_of_exponent_ge hn hz.le (by linarith)
      calc s⁻¹ * ‖z‖ ^ (-s) ≤ s⁻¹ * ‖z‖ ^ (-σ) := by gcongr
        _ ≤ (s⁻¹ + σ⁻¹) * ‖z‖ ^ (-σ) := by nlinarith

lemma cmxSA_kern_far (hs0 : 0 ≤ s) (z : Euc d) (hz : 1 ≤ ‖z‖) :
    (s ≠ 0 → ‖kern s z‖ ≤ s⁻¹) ∧ (s = 0 → ‖kern s z‖ = Real.log ‖z‖) := by
  have hn : 0 < ‖z‖ := by linarith
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · simp only [kern, hs, if_false, Real.norm_eq_abs]
    have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    have h1 : ‖z‖ ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
    have h2 : 0 < ‖z‖ ^ (-s) := Real.rpow_pos_of_pos hn _
    rw [abs_of_nonneg (by positivity)]
    calc s⁻¹ * ‖z‖ ^ (-s) ≤ s⁻¹ * 1 := by gcongr
      _ = s⁻¹ := mul_one _
  · subst hs
    simp only [kern, if_true, norm_neg, Real.norm_eq_abs]
    exact abs_of_nonneg (Real.log_nonneg hz)

lemma cmxSA_kern_bound (hs0 : 0 ≤ s) {σ : ℝ} (hσ : 0 < σ) (hsσ : s ≤ σ) (x y : Euc d) :
    ‖kern s (x - y)‖ ≤ (s⁻¹ + σ⁻¹) * cmxSA_m σ (x - y) + s⁻¹ + cmxSA_W s x + cmxSA_W s y := by
  have hW1 := cmxSA_W_nonneg s x
  have hW2 := cmxSA_W_nonneg s y
  have hm0 := cmxSA_m_nonneg σ (x - y)
  have hs1 : 0 ≤ s⁻¹ := inv_nonneg.2 hs0
  have hσ1 : 0 < σ⁻¹ := inv_pos.2 hσ
  by_cases hz1 : ‖x - y‖ < 1
  · have hm : cmxSA_m σ (x - y) = ‖x - y‖ ^ (-σ) := by unfold cmxSA_m; rw [if_pos hz1]
    rw [hm]
    have := cmxSA_kern_near hs0 hσ hsσ (x - y) hz1
    linarith
  · have hz : 1 ≤ ‖x - y‖ := not_lt.1 hz1
    have hm : cmxSA_m σ (x - y) = 0 := by unfold cmxSA_m; rw [if_neg hz1]
    rw [hm, mul_zero, zero_add]
    obtain ⟨h1, h2⟩ := cmxSA_kern_far hs0 (x - y) hz
    by_cases hs : s = 0
    · rw [h2 hs]
      simp only [cmxSA_W, hs, if_true, inv_zero, zero_add]
      have hn : 0 < ‖x - y‖ := by linarith
      have e1 : ‖x - y‖ ≤ (2 + ‖x‖) * (2 + ‖y‖) := by
        have := norm_sub_le x y
        nlinarith [norm_nonneg x, norm_nonneg y]
      calc Real.log ‖x - y‖ ≤ Real.log ((2 + ‖x‖) * (2 + ‖y‖)) := Real.log_le_log hn e1
        _ = Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) := by
          rw [Real.log_mul (by positivity) (by positivity)]
    · have := h1 hs
      linarith

lemma cmxSA_comm_bound (hs0 : 0 ≤ s) {σ : ℝ} (hσ : 0 < σ) (hsσ : s ≤ σ) {L : ℝ≥0}
    {v : Euc d → Euc d} (hv : LipschitzWith L v) (x y : Euc d) :
    ‖commKer (kernGrad s) v x y‖ ≤ (L : ℝ) * cmxSA_m σ (x - y) + L := by
  have hm0 := cmxSA_m_nonneg σ (x - y)
  have hL : (0 : ℝ) ≤ L := L.coe_nonneg
  unfold commKer
  by_cases hxy : x = y
  · rw [if_pos hxy]; simp only [norm_zero]; positivity
  · rw [if_neg hxy]
    have hn : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
    set r := ‖x - y‖ with hr
    have h1 : ‖inner ℝ (v x - v y) (kernGrad s (x - y))‖ ≤ ‖v x - v y‖ * ‖kernGrad s (x - y)‖ :=
      norm_inner_le_norm _ _
    have h2 : ‖v x - v y‖ ≤ L * r := by
      have := hv.dist_le_mul x y
      rwa [dist_eq_norm, dist_eq_norm] at this
    have h3 : ‖kernGrad s (x - y)‖ = r ^ (-(s + 2)) * r := by
      unfold kernGrad
      rw [norm_smul, norm_neg, Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
    have h4 : r * (r ^ (-(s + 2)) * r) = r ^ (-s) := by
      have : r ^ (-s) = r ^ (-(s + 2)) * r ^ (2 : ℝ) := by
        rw [← Real.rpow_add hn]; congr 1; ring
      rw [this, Real.rpow_two]; ring
    have h5 : ‖inner ℝ (v x - v y) (kernGrad s (x - y))‖ ≤ L * r ^ (-s) := by
      calc _ ≤ ‖v x - v y‖ * ‖kernGrad s (x - y)‖ := h1
        _ ≤ (L * r) * ‖kernGrad s (x - y)‖ := by gcongr
        _ = L * (r * (r ^ (-(s + 2)) * r)) := by rw [h3]; ring
        _ = L * r ^ (-s) := by rw [h4]
    refine h5.trans ?_
    by_cases hz1 : r < 1
    · have hm : cmxSA_m σ (x - y) = r ^ (-σ) := by unfold cmxSA_m; rw [if_pos hz1]
      rw [hm]
      have : r ^ (-s) ≤ r ^ (-σ) := Real.rpow_le_rpow_of_exponent_ge hn hz1.le (by linarith)
      nlinarith
    · have hm : cmxSA_m σ (x - y) = 0 := by unfold cmxSA_m; rw [if_neg hz1]
      rw [hm, mul_zero, zero_add]
      have : r ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (not_lt.1 hz1) (by linarith)
      nlinarith

/-! ### Integrability for measurable `ρ` -/

lemma cmxSA_core_m {k : Euc d → Euc d → ℝ}
    (hk : Measurable (fun q : Euc d × Euc d => k q.1 q.2)) (ρ : Euc d → ℝ)
    (hρm : Measurable ρ) (hρ1 : Integrable ρ) (W : Euc d → ℝ) (hW : Measurable W)
    (hW0 : ∀ x, 0 ≤ W x) (hWρ : Integrable (fun x => W x * ρ x)) (A c σ : ℝ) (hA : 0 ≤ A)
    (hc : 0 ≤ c) (B : ℝ≥0∞) (hB : B < ⊤)
    (hconv : ∀ a : Euc d, ∫⁻ y, ‖cmxSA_m σ (a - y)‖ₑ * ‖ρ y‖ₑ ≤ B)
    (hbound : ∀ x y, ‖k x y‖ ≤ c * cmxSA_m σ (x - y) + A + W x + W y) :
    (∀ a, Integrable (fun y => k a y * ρ y)) ∧
      Integrable (fun q : Euc d × Euc d => k q.1 q.2 * ρ q.1 * ρ q.2) := by
  refine cmxSA_core_integrable hk ρ hρm hρ1 (fun z => c * cmxSA_m σ z) W
    ((cmxSA_m_measurable σ).const_mul c) (fun z => mul_nonneg hc (cmxSA_m_nonneg σ z)) hW hW0 hWρ A hA
    (ENNReal.ofReal c * B) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB) ?_ hbound
  intro a
  have : ∀ y, ‖c * cmxSA_m σ (a - y)‖ₑ * ‖ρ y‖ₑ =
      ENNReal.ofReal c * (‖cmxSA_m σ (a - y)‖ₑ * ‖ρ y‖ₑ) := by
    intro y
    rw [enorm_mul, Real.enorm_eq_ofReal hc]; ring
  simp_rw [this]
  have hmx : Measurable (fun y => ‖cmxSA_m σ (a - y)‖ₑ * ‖ρ y‖ₑ) :=
    (((cmxSA_m_measurable σ).comp (measurable_const.sub measurable_id)).enorm).mul hρm.enorm
  rw [lintegral_const_mul _ hmx]
  gcongr
  exact hconv a

lemma cmxSA_energy_all_meas (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Euc d → ℝ) (hρm : Measurable ρ)
    (h1 : Integrable ρ) (hpρ : MemLp ρ p volume)
    (hW : Integrable (fun x => cmxSA_W s x * ρ x)) :
    (∀ a, Integrable (fun y => kern s (a - y) * ρ y)) ∧
      Integrable (fun q : Euc d × Euc d => kern s (q.1 - q.2) * ρ q.1 * ρ q.2) := by
  obtain ⟨-, qr, σ, hq, hsσ, hσ0, hσq, hpq⟩ := cmxSA_exponents hd hs0 hsd p hp
  obtain ⟨B, hB, hconv⟩ := cmxSA_conv_bound (by omega) hσ0.le hq hσq p hpq ρ hpρ
  have hs1 : 0 ≤ s⁻¹ := inv_nonneg.2 hs0
  exact cmxSA_core_m (k := fun x y => kern s (x - y))
    ((cmxSA_kern_measurable s).comp (measurable_fst.sub measurable_snd)) ρ hρm h1
    (cmxSA_W s) (cmxSA_W_measurable s) (cmxSA_W_nonneg s) hW s⁻¹ (s⁻¹ + σ⁻¹) σ hs1
    (by positivity) B hB hconv (fun x y => cmxSA_kern_bound hs0 hσ0 hsσ x y)

lemma cmxSA_energy_integrable_meas (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Euc d → ℝ) (hρm : Measurable ρ)
    (h1 : Integrable ρ) (hpρ : MemLp ρ p volume)
    (hW : Integrable (fun x => cmxSA_W s x * ρ x)) {N : ℕ} (X : Fin N → Euc d) :
    EnergyIntegrable s X ρ := by
  have := cmxSA_energy_all_meas hd hs0 hsd p hp ρ hρm h1 hpρ hW
  exact ⟨fun i => this.1 (X i), this.2⟩

lemma cmxSA_comm_integrable_meas (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Euc d → ℝ) (hρm : Measurable ρ)
    (h1 : Integrable ρ) (hpρ : MemLp ρ p volume) {v : Euc d → Euc d} {L : ℝ≥0}
    (hv : LipschitzWith L v) {N : ℕ} (X : Fin N → Euc d) :
    CommIntegrable s X ρ v := by
  obtain ⟨-, qr, σ, hq, hsσ, hσ0, hσq, hpq⟩ := cmxSA_exponents hd hs0 hsd p hp
  obtain ⟨B, hB, hconv⟩ := cmxSA_conv_bound (by omega) hσ0.le hq hσq p hpq ρ hpρ
  have := cmxSA_core_m (k := commKer (kernGrad s) v)
    (cmxSA_commKer_measurable s hv.continuous.measurable) ρ hρm h1
    (fun _ => 0) measurable_const (fun _ => le_rfl) (by simpa using integrable_zero _ _ _)
    L L σ L.coe_nonneg L.coe_nonneg B hB hconv
    (fun x y => by simpa using cmxSA_comm_bound hs0 hσ0 hsσ hv x y)
  exact ⟨fun i => this.1 (X i), this.2⟩

/-! ### Independence of the a.e. representative -/

lemma cmxSA_pairGen_congr {N : ℕ} (k : Euc d → Euc d → ℝ) (X : Fin N → Euc d)
    {ρ ρ' : Euc d → ℝ} (h : ρ =ᵐ[volume] ρ') : pairGen k X ρ = pairGen k X ρ' := by
  unfold pairGen
  have e1 : ∀ i, ∫ y, k (X i) y * ρ y = ∫ y, k (X i) y * ρ' y := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hy]
  have e2 : ∫ x, ∫ y, k x y * ρ x * ρ y = ∫ x, ∫ y, k x y * ρ' x * ρ' y := by
    refine integral_congr_ae ?_
    filter_upwards [h] with x hx
    refine integral_congr_ae ?_
    filter_upwards [h] with y hy
    rw [hx, hy]
  simp_rw [e1, e2]

lemma cmxSA_pairIntegrable_congr {N : ℕ} {k : Euc d → Euc d → ℝ} {X : Fin N → Euc d}
    {ρ ρ' : Euc d → ℝ} (h : ρ =ᵐ[volume] ρ') (hk : PairIntegrable k X ρ) :
    PairIntegrable k X ρ' := by
  refine ⟨fun i => (hk.1 i).congr ?_, hk.2.congr ?_⟩
  · filter_upwards [h] with y hy
    rw [hy]
  · have h1 : ∀ᵐ q : Euc d × Euc d ∂(volume.prod volume), ρ q.1 = ρ' q.1 :=
      Measure.quasiMeasurePreserving_fst.ae h
    have h2 : ∀ᵐ q : Euc d × Euc d ∂(volume.prod volume), ρ q.2 = ρ' q.2 :=
      Measure.quasiMeasurePreserving_snd.ae h
    filter_upwards [h1, h2] with q hq1 hq2
    rw [hq1, hq2]

/-! ### The logarithmic moment -/

lemma cmxSA_log_le (y₀ x : Euc d) :
    Real.log (2 + ‖x‖) ≤ (Real.log (3 + ‖y₀‖) + Real.log (2 + ‖y₀‖) + Real.log 2) +
      ‖kern 0 (x - y₀)‖ := by
  have hb := norm_nonneg y₀
  have hl3 : 0 ≤ Real.log (3 + ‖y₀‖) := Real.log_nonneg (by linarith)
  have hl2 : 0 ≤ Real.log (2 + ‖y₀‖) := Real.log_nonneg (by linarith)
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hk0 : 0 ≤ ‖kern 0 (x - y₀)‖ := norm_nonneg _
  have hx : ‖x‖ ≤ ‖y₀‖ + ‖x - y₀‖ := by
    have := norm_le_insert' x y₀
    linarith
  by_cases hu : ‖x - y₀‖ < 1
  · have : Real.log (2 + ‖x‖) ≤ Real.log (3 + ‖y₀‖) :=
      Real.log_le_log (by positivity) (by linarith)
    linarith
  · have hu1 : 1 ≤ ‖x - y₀‖ := not_lt.1 hu
    obtain ⟨-, h2⟩ := cmxSA_kern_far (le_refl (0 : ℝ)) (x - y₀) hu1
    rw [h2 rfl]
    have hn : 0 < ‖x - y₀‖ := by linarith
    have e1 : 2 + ‖x‖ ≤ (2 + ‖y₀‖) * (2 * ‖x - y₀‖) := by nlinarith
    calc Real.log (2 + ‖x‖) ≤ Real.log ((2 + ‖y₀‖) * (2 * ‖x - y₀‖)) :=
          Real.log_le_log (by positivity) e1
      _ = Real.log (2 + ‖y₀‖) + Real.log 2 + Real.log ‖x - y₀‖ := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hn.ne']
          ring
      _ ≤ _ := by linarith

lemma cmxSA_logMoment (ρ : Euc d → ℝ) (hρm : Measurable ρ) (h1 : Integrable ρ)
    (hlog : LogIntegrable ρ) : Integrable (fun x => cmxSA_W 0 x * ρ x) := by
  by_cases hρ0 : ρ =ᵐ[volume] 0
  · refine (integrable_zero (Euc d) ℝ volume).congr ?_
    filter_upwards [hρ0] with x hx
    simp [hx]
  · have hfreq : ∃ᶠ y in ae volume, ρ y ≠ 0 := by
      intro hcon
      apply hρ0
      filter_upwards [hcon] with y hy
      simpa using hy
    obtain ⟨y₀, hy0, hgood⟩ := (hfreq.and_eventually hlog.prod_left_ae).exists
    have hI : Integrable (fun x : Euc d => kern 0 (x - y₀) * ρ x) := by
      have := hgood.div_const (ρ y₀)
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only
      field_simp
    set C₀ := Real.log (3 + ‖y₀‖) + Real.log (2 + ‖y₀‖) + Real.log 2 with hC₀
    refine Integrable.mono' ((h1.norm.const_mul C₀).add hI.norm)
      (((cmxSA_W_measurable 0).mul hρm).aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [cmxSA_W, if_true, norm_mul, Pi.add_apply]
    have hl : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    rw [Real.norm_of_nonneg hl]
    calc Real.log (2 + ‖x‖) * ‖ρ x‖ ≤ (C₀ + ‖kern 0 (x - y₀)‖) * ‖ρ x‖ :=
          by gcongr; exact cmxSA_log_le y₀ x
      _ = _ := by ring

lemma cmxSA_logIntegrable_congr {ρ ρ' : Euc d → ℝ} (h : ρ =ᵐ[volume] ρ') (hk : LogIntegrable ρ) :
    LogIntegrable ρ' := by
  refine Integrable.congr hk ?_
  have h1 : ∀ᵐ q : Euc d × Euc d ∂(volume.prod volume), ρ q.1 = ρ' q.1 :=
    Measure.quasiMeasurePreserving_fst.ae h
  have h2 : ∀ᵐ q : Euc d × Euc d ∂(volume.prod volume), ρ q.2 = ρ' q.2 :=
    Measure.quasiMeasurePreserving_snd.ae h
  filter_upwards [h1, h2] with q hq1 hq2
  rw [hq1, hq2]

/-- `integrable_of_Lp` (the statement of `Assembly.integrable_of_Lp`). -/
theorem cmxSA_integrable_of_Lp (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (p : ℝ≥0∞)
    (hp : ENNReal.ofReal ((d : ℝ) / (d - s)) < p) (ρ : Euc d → ℝ) (h1 : Integrable ρ)
    (hpρ : MemLp ρ p volume) (hlog : s = 0 → LogIntegrable ρ) (v : Euc d → Euc d) (L : ℝ≥0)
    (hv : LipschitzWith L v) {N : ℕ} (X : Fin N → Euc d) :
    EnergyIntegrable s X ρ ∧ CommIntegrable s X ρ v := by
  set ρ' : Euc d → ℝ := hpρ.aestronglyMeasurable.mk ρ with hρ'
  have hae : ρ =ᵐ[volume] ρ' := hpρ.aestronglyMeasurable.ae_eq_mk
  have hmeas : Measurable ρ' := hpρ.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have h1' : Integrable ρ' := h1.congr hae
  have hp' : MemLp ρ' p volume := hpρ.ae_eq hae
  have hW : Integrable (fun x => cmxSA_W s x * ρ' x) := by
    by_cases hs : s = 0
    · subst hs
      exact cmxSA_logMoment ρ' hmeas h1' (cmxSA_logIntegrable_congr hae (hlog rfl))
    · simp only [cmxSA_W, hs, if_false, zero_mul]
      exact integrable_zero _ _ _
  exact ⟨cmxSA_pairIntegrable_congr hae.symm
      (cmxSA_energy_integrable_meas hd hs0 hsd p hp ρ' hmeas h1' hp' hW X),
    cmxSA_pairIntegrable_congr hae.symm
      (cmxSA_comm_integrable_meas hd hs0 hsd p hp ρ' hmeas h1' hp' hv X)⟩

end HRS.Commutator.Whole
