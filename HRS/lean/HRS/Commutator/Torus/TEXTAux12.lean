import HRS.Commutator.Torus.TEXTAux11

/-!
# T-EXT-A helpers, part 12: `hls_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma text_fcoef_add {u v : Torus d → ℝ} (hu : Integrable u) (hv : Integrable v) (k : Lattice d) :
    Torus.fcoef (fun x => u x + v x) k = Torus.fcoef u k + Torus.fcoef v k := by
  have hc : Continuous (fun x : Torus d => Torus.mode (-k) x) := Torus.continuous_mode (-k)
  have h1 : ∀ w : Torus d → ℝ, Integrable w →
      Integrable (fun x => Torus.mode (-k) x * ((w x : ℝ) : ℂ)) := fun w hw =>
    hw.ofReal.bdd_mul hc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => (Torus.norm_mode (-k) x).le)
  unfold Torus.fcoef
  rw [← integral_add (h1 u hu) (h1 v hv)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  push_cast; ring

lemma text_mk_zero : (Torus.mk (0 : Euc d)) = 0 := by
  funext i; simp [Torus.mk]

lemma text_tdist_pos {z : Torus d} (hz : z ≠ 0) : 0 < KernelGrad.tdist z 0 := by
  rw [KernelGrad.tdist_zero_right]
  refine norm_pos_iff.2 fun h0 => hz ?_
  rw [← KernelGrad.mk_centeredRep z, h0, text_mk_zero]

theorem text_hls_main (hd : 1 ≤ d) (σ : ℝ) (p q : ℝ≥0∞) (hp : 1 < p) (hpq : p < q) (hq : q < ⊤)
    (hσ : 0 < σ) (hrel : q⁻¹ = p⁻¹ - ENNReal.ofReal (σ / d)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Torus d → ℝ, MemLp f p volume → Torus.fcoef f 0 = 0 →
      ∃ h : Torus d → ℝ, MemLp h q volume ∧ Torus.fcoef h 0 = 0 ∧
        (∀ k : Lattice d, k ≠ 0 → Torus.fcoef h k =
          (((2 * Real.pi * Lattice.enorm k) ^ (-σ) : ℝ) : ℂ) * Torus.fcoef f k) ∧
        eLpNorm h q volume ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  classical
  obtain ⟨hp1, hpq1, hrel1, hσd⟩ := text_exps hd p q hp hpq hq hσ hrel
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨CK, hCK, Cm, hCm, hker⟩ := text_mult_kernel_main hd σ hσ hσd
  obtain ⟨K, hKint, hKcoef, hKnear, hKfar⟩ := hker 1 one_pos le_rfl
  -- a global bound for `K`
  set q₂ : ℝ := ((d : ℝ) / 2) ^ (σ - d) with hq₂
  have hq₂pos : 0 < q₂ := Real.rpow_pos_of_pos (by positivity) _
  have hKb : ∀ z : Torus d, z ≠ 0 →
      |K z| ≤ (CK + Cm 0 / q₂) * KernelGrad.tdist z 0 ^ (σ - d) := by
    intro z hz
    have ht := text_tdist_pos hz
    have hrp : 0 ≤ KernelGrad.tdist z 0 ^ (σ - d) := by positivity
    have hCm0 := hCm 0
    by_cases h1 : KernelGrad.tdist z 0 ≤ 1
    · have := hKnear z hz h1
      have h2 : 0 ≤ Cm 0 / q₂ := by positivity
      nlinarith
    · push Not at h1
      have h3 := hKfar 0 z h1.le
      simp only [Nat.cast_zero, add_zero, Real.one_rpow, mul_one, neg_zero, Real.rpow_zero] at h3
      have hc := KernelGrad.tdist_zero_right z
      have hcle : KernelGrad.tdist z 0 ≤ d / 2 := by
        rw [hc]
        exact text_cRep_norm_le _ (KernelGrad.abs_centeredRep_le z)
      have h4 : q₂ ≤ KernelGrad.tdist z 0 ^ (σ - d) :=
        Real.rpow_le_rpow_of_nonpos ht hcle (by linarith)
      have h5 : Cm 0 ≤ (Cm 0 / q₂) * KernelGrad.tdist z 0 ^ (σ - d) := by
        calc Cm 0 = (Cm 0 / q₂) * q₂ := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left h4 (by positivity)
      have h6 : 0 ≤ CK * KernelGrad.tdist z 0 ^ (σ - d) := by positivity
      nlinarith
  -- the low-frequency polynomial
  let pk : Lattice d → ℝ := fun k =>
    if k = 0 then 0 else Whole.chi (Lattice.toEuc k) * (2 * Real.pi * Lattice.enorm k) ^ (-σ)
  have hS : ∀ k, pk k ≠ 0 → k ∈ (tpos_finite_norm_le (d := d) 2).toFinset := by
    intro k hk
    rw [Set.Finite.mem_toFinset]
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    push Not at hlt
    apply hk
    simp only [pk]
    rw [Whole.cmxFB_chi_zero hlt.le]
    simp
  have hev : ∀ k, pk (-k) = pk k := by
    intro k
    have : Lattice.toEuc (-k) = -Lattice.toEuc k := by ext i; simp [Lattice.toEuc]
    by_cases hk : k = 0
    · subst hk; simp
    · have hk' : -k ≠ 0 := neg_ne_zero.2 hk
      simp only [pk, hk, hk', if_false, this, Whole.cmxFB_chi_neg, Lattice.enorm, norm_neg]
  obtain ⟨P, hPc, hPcoef⟩ := text_trigpoly pk _ hS hev
  obtain ⟨B₀, hB₀⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hPc.continuousOn
  set B : ℝ := max B₀ 0 with hB
  have hPb : ∀ x, |P x| ≤ B := fun x => by
    have := hB₀ x (Set.mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  have hPint : Integrable P :=
    hPc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨Cc, hCc, hconv⟩ := text_conv_Lq hd p q hp hpq hq hσ hrel
  have hCm0 := hCm 0
  refine ⟨Cc * (CK + Cm 0 / q₂) + B + 1, by positivity, fun f hf hf0 => ?_⟩
  have hf1 : Integrable f := hf.integrable hp.le
  obtain ⟨hm1, hn1⟩ := hconv K f (CK + Cm 0 / q₂) (by positivity) hKint hKb hf
  have hi1 : Integrable (textConv K f) := text_integrable_conv hKint hf1
  have hi2 : Integrable (textConv P f) := text_integrable_conv hPint hf1
  have hcoef : ∀ k : Lattice d, Torus.fcoef (fun x => textConv K f x + textConv P f x) k =
      (((if k = 0 then 0 else (2 * Real.pi * Lattice.enorm k) ^ (-σ) : ℝ)) : ℂ) *
        Torus.fcoef f k := by
    intro k
    rw [text_fcoef_add hi1 hi2, text_fcoef_conv hKint hf1, text_fcoef_conv hPint hf1, hKcoef k,
      hPcoef k, ← add_mul, ← Complex.ofReal_add]
    congr 2
    by_cases hk : k = 0
    · simp [pk, hk]
    · simp only [pk, hk, if_false, one_smul]; ring
  -- bound for the low-frequency part
  have hh2 : eLpNorm (textConv P f) q volume ≤ ENNReal.ofReal B * eLpNorm f p volume := by
    have hb : ∀ x, ‖textConv P f x‖ ≤ B * ∫ y, ‖f y‖ := by
      intro x
      unfold textConv
      calc ‖∫ y, P (x - y) * f y‖ ≤ ∫ y, B * ‖f y‖ := by
            refine norm_integral_le_of_norm_le (hf1.norm.const_mul B)
              (Filter.Eventually.of_forall fun y => ?_)
            rw [norm_mul, Real.norm_eq_abs]
            exact mul_le_mul_of_nonneg_right (hPb _) (norm_nonneg _)
        _ = B * ∫ y, ‖f y‖ := integral_const_mul _ _
    have h1 := eLpNorm_le_of_ae_bound (p := q) (μ := (volume : Measure (Torus d)))
      hi2.aestronglyMeasurable (Filter.Eventually.of_forall hb)
    simp only [measure_univ, ENNReal.one_rpow, one_mul] at h1
    refine h1.trans ?_
    rw [ENNReal.ofReal_mul hB0, ofReal_integral_norm_eq_lintegral_enorm hf1,
      ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
    exact mul_le_mul' le_rfl (eLpNorm_le_eLpNorm_of_exponent_le hp.le)
  have hbound : eLpNorm (fun x => textConv K f x + textConv P f x) q volume ≤
      ENNReal.ofReal (Cc * (CK + Cm 0 / q₂) + B + 1) * eLpNorm f p volume := by
    calc eLpNorm (fun x => textConv K f x + textConv P f x) q volume
        ≤ eLpNorm (textConv K f) q volume + eLpNorm (textConv P f) q volume :=
          eLpNorm_add_le (f := textConv K f) (g := textConv P f) (hp.trans hpq).le
      _ ≤ ENNReal.ofReal (Cc * (CK + Cm 0 / q₂)) * eLpNorm f p volume +
            ENNReal.ofReal B * eLpNorm f p volume := add_le_add hn1 hh2
      _ = ENNReal.ofReal (Cc * (CK + Cm 0 / q₂) + B) * eLpNorm f p volume := by
          rw [← add_mul, ENNReal.ofReal_add (by positivity) hB0]
      _ ≤ ENNReal.ofReal (Cc * (CK + Cm 0 / q₂) + B + 1) * eLpNorm f p volume := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
  refine ⟨fun x => textConv K f x + textConv P f x, ?_, ?_, ?_, hbound⟩
  · exact memLp_iff.2 (lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      hf.eLpNorm_lt_top))
  · rw [hcoef 0]; simp
  · intro k hk
    rw [hcoef k]; simp [hk]

end HRS.Commutator.TorusNote
