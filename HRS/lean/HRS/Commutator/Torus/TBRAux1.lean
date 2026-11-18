import HRS.Commutator.Torus.Defs
import HRS.Energy.Commutator.AbsConv
import HRS.Energy.Commutator.SliceAux
import HRS.Energy.Commutator.RenormStjKernel
import HRS.Energy.Modulated

/-!
# Torus helpers for `L^p` integrability (packet T-APPROX, file 1 of 2)

Kernel bounds on `𝕋^d` by the dominating function `tbrG a z = tdist(z,0)^{-a} + 1`, the membership
`tbrG a ∈ L^q` for `a q < d`, and the `L^r × L^{r'}` Hölder estimates (translation invariance, Tonelli).
Names carry the prefix `tbr_`; the namespace is `HRS.Commutator.TorusNote`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Exponent of the dominating function: `a = s` if `s > 0`, `a = ε` if `s = 0`. -/
def tbrA (s ε : ℝ) : ℝ := if s = 0 then ε else s

/-- The dominating function `z ↦ tdist(z,0)^{-a} + 1` on `𝕋^d`. -/
def tbrG (a : ℝ) (z : Torus d) : ℝ := KernelGrad.tdist z 0 ^ (-a) + 1

theorem tbr_G_measurable (a : ℝ) : Measurable (tbrG (d := d) a) :=
  ((CoercAux.continuous_tdist_zero.measurable).pow_const _).add_const 1

theorem tbr_G_one_le (a : ℝ) (z : Torus d) : 1 ≤ tbrG (d := d) a z := by
  unfold tbrG
  have := Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) (-a)
  linarith

/-- `t^{-s} ≤ t^{-a} + 1` when `s = 0` or `a = s`. -/
theorem tbr_rpow_le {s a : ℝ} (hsa : s = 0 ∨ a = s) {t : ℝ} (ht : 0 < t) :
    t ^ (-s) ≤ t ^ (-a) + 1 := by
  have hpos := Real.rpow_nonneg ht.le (-a)
  rcases hsa with h | h
  · subst h
    simp only [neg_zero, Real.rpow_zero]
    linarith
  · subst h
    linarith

/-- The scale function `selfScale d s (tdist z 0)` is dominated by `C · tbrG a`. -/
theorem tbr_selfScale_le (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a : ℝ} (ha : 0 ≤ a)
    (hsa : s = 0 ∨ a = s) (hs0a : s = 0 → 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Torus d, z ≠ 0 →
      |selfScale d s (KernelGrad.tdist z 0)| ≤ C * tbrG a z := by
  by_cases h0 : s = 0
  · have ha0 : 0 < a := hs0a h0
    have hlog : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
    refine ⟨1 / a + Real.log d, by positivity, fun z hz => ?_⟩
    have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
    have htd : KernelGrad.tdist z 0 ≤ d := SliceAux.tdist_le_dim z
    set t := KernelGrad.tdist z 0 with htdef
    have hX := Real.rpow_nonneg ht.le (-a)
    unfold selfScale tbrG
    rw [if_pos h0, ← htdef, abs_neg]
    rcases le_total t 1 with ht1 | ht1
    · -- `|log t| ≤ a⁻¹ t^{-a}` for `t ≤ 1`
      have h1 := Real.abs_log_mul_self_rpow_lt t a ht ht1 ha0
      have key : Real.log t = (Real.log t * t ^ a) * t ^ (-a) := by
        rw [mul_assoc, ← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero, mul_one]
      have hA : |Real.log t| ≤ 1 / a * t ^ (-a) := by
        calc |Real.log t| = |Real.log t * t ^ a| * t ^ (-a) := by
              conv_lhs => rw [key]
              rw [abs_mul, abs_of_nonneg hX]
          _ ≤ 1 / a * t ^ (-a) := mul_le_mul_of_nonneg_right h1.le hX
      have hC : 1 / a * t ^ (-a) ≤ (1 / a + Real.log d) * (t ^ (-a) + 1) := by
        have h2 : 0 ≤ 1 / a := by positivity
        nlinarith [mul_nonneg hlog (by linarith : (0 : ℝ) ≤ t ^ (-a) + 1)]
      exact hA.trans hC
    · -- `|log t| = log t ≤ log d` for `1 ≤ t ≤ d`
      have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
      rw [abs_of_nonneg hlt]
      have h3 : Real.log t ≤ Real.log d := Real.log_le_log ht htd
      have h2 : 0 ≤ 1 / a := by positivity
      nlinarith [mul_nonneg hlog hX, mul_nonneg h2 (by linarith : (0 : ℝ) ≤ t ^ (-a) + 1)]
  · have hsa' : a = s := hsa.resolve_left h0
    refine ⟨1, zero_le_one, fun z hz => ?_⟩
    have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
    unfold selfScale tbrG
    rw [if_neg h0, one_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _), hsa']
    linarith

/-- The energy kernel `periodicRiesz d s` is dominated by `C · tbrG a` off the origin. -/
theorem tbr_periodicRiesz_le (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a : ℝ} (ha : 0 ≤ a)
    (hsa : s = 0 ∨ a = s) (hs0a : s = 0 → 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Torus d, z ≠ 0 → |periodicRiesz d s z| ≤ C * tbrG a z := by
  obtain ⟨C₁, hC₁, hup⟩ := HRS.Commutator.Stj.periodicRiesz_upper (d := d) (by omega) hs0 hsd
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) (by omega) hs0 hsd
  obtain ⟨C₂, hC₂, hsc⟩ := tbr_selfScale_le hd hs0 hsd ha hsa hs0a
  refine ⟨C₂ + |C₁| + |B|, by positivity, fun z hz => ?_⟩
  have hG1 := tbr_G_one_le (d := d) a z
  have h1 := hup z hz
  have h2 := hB z
  have h3 := hsc z hz
  have hsa1 := le_abs_self (selfScale d s (KernelGrad.tdist z 0))
  have hC1a := le_abs_self C₁
  have hC1b := neg_abs_le C₁
  have hBa := le_abs_self B
  have hBb := neg_abs_le B
  have hG0 : 0 ≤ tbrG a z := by linarith
  have e1 : |C₁| ≤ |C₁| * tbrG a z := le_mul_of_one_le_right (abs_nonneg _) hG1
  have e2 : |B| ≤ |B| * tbrG a z := le_mul_of_one_le_right (abs_nonneg _) hG1
  have e3 : (C₂ + |C₁| + |B|) * tbrG a z = C₂ * tbrG a z + |C₁| * tbrG a z + |B| * tbrG a z := by ring
  rw [abs_le, e3]
  have hb0 : 0 ≤ |B| * tbrG a z := mul_nonneg (abs_nonneg _) hG0
  have hc0 : 0 ≤ |C₁| * tbrG a z := mul_nonneg (abs_nonneg _) hG0
  have hC2G : 0 ≤ C₂ * tbrG a z := mul_nonneg hC₂ hG0
  constructor
  · linarith
  · linarith

/-- The commutator kernel is dominated by `C · tbrG a (x - y)` off the diagonal. -/
theorem tbr_commKernel_le (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a : ℝ}
    (hsa : s = 0 ∨ a = s) {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Torus d, x ≠ y →
      |commKernel (periodicRieszGrad d s) v x y| ≤ C * tbrG a (x - y) := by
  obtain ⟨C₀, hC₀, hC⟩ := commKernel_bound (d := d) (by omega) hs0 hsd
  refine ⟨2 * C₀ * L, mul_nonneg (mul_nonneg (by norm_num) hC₀) hL, fun x y hxy => ?_⟩
  have h1 := hC L v hL hv x y hxy
  have ht : 0 < KernelGrad.tdist x y := by
    rw [KernelGrad.tdist_eq_sub_zero]
    exact KernelGrad.tdist_pos (sub_ne_zero.mpr hxy)
  have h2 := tbr_rpow_le hsa ht
  have htd : KernelGrad.tdist x y = KernelGrad.tdist (x - y) 0 := KernelGrad.tdist_eq_sub_zero x y
  unfold tbrG
  rw [← htd]
  calc |commKernel (periodicRieszGrad d s) v x y|
      ≤ C₀ * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
    _ ≤ C₀ * L * (2 * (KernelGrad.tdist x y ^ (-a) + 1)) :=
        mul_le_mul_of_nonneg_left
          (by linarith [Real.rpow_nonneg (KernelGrad.tdist_nonneg x y) (-a)]) (mul_nonneg hC₀ hL)
    _ = 2 * C₀ * L * (KernelGrad.tdist x y ^ (-a) + 1) := by ring

/-- `tbrG a ∈ L^q(𝕋^d)` when `a ≥ 0`, `q > 0` and `a q < d`. -/
theorem tbr_memLp_G (hd : 1 ≤ d) {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) (haq : a * q < d) :
    MemLp (tbrG (d := d) a) (ENNReal.ofReal q) volume := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hf : MemLp (fun z : Torus d => KernelGrad.tdist z 0 ^ (-a)) (ENNReal.ofReal q) volume := by
    have hm : Measurable fun z : Torus d => KernelGrad.tdist z 0 ^ (-a) :=
      (CoercAux.continuous_tdist_zero.measurable).pow_const _
    rw [← integrable_norm_rpow_iff hm.aestronglyMeasurable (ENNReal.ofReal_pos.2 hq).ne'
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hq.le]
    have hint := SliceAux.integrable_tdist_rpow (d := d) (α := a * q) (by omega) (mul_nonneg ha hq.le) haq
    refine hint.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) _),
      ← Real.rpow_mul (KernelGrad.tdist_nonneg z 0)]
    ring_nf
  have hc : MemLp (fun _ : Torus d => (1 : ℝ)) (ENNReal.ofReal q) volume := memLp_const 1
  exact hf.add hc

/-! ### Hölder estimates and Tonelli for the `L^r` integrability -/

theorem tbr_enorm_le {a b C : ℝ} (hC : 0 ≤ C) (h : |a| ≤ C * |b|) :
    ‖a‖ₑ ≤ ENNReal.ofReal C * ‖b‖ₑ := by
  rw [Real.enorm_eq_ofReal_abs a, Real.enorm_eq_ofReal_abs b, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal h

/-- The diagonal is `volume ⊗ volume`-null on `𝕋^d`. -/
theorem tbr_ae_ne_prod (hd : 1 ≤ d) :
    ∀ᵐ z ∂((volume : Measure (Torus d)).prod volume), z.1 ≠ z.2 := by
  rw [MeasureTheory.ae_iff]
  have hs : MeasurableSet {z : Torus d × Torus d | z.1 = z.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hfib : ∀ x : Torus d, (volume : Measure (Torus d)) (Prod.mk x ⁻¹' {z : Torus d × Torus d | z.1 = z.2}) = 0 := by
    intro x
    have hpre : Prod.mk x ⁻¹' {z : Torus d × Torus d | z.1 = z.2} = {x} := by
      ext y; simp [eq_comm]
    rw [hpre]
    exact volume_singleton_torus hd x
  have key : ((volume : Measure (Torus d)).prod volume) {z : Torus d × Torus d | z.1 = z.2} = 0 :=
    (Measure.measure_prod_null hs).2 (Filter.Eventually.of_forall fun x => hfib x)
  simpa using key

/-- Pointwise a.e. in `y`: `y ≠ x`. -/
theorem tbr_ae_ne (hd : 1 ≤ d) (x : Torus d) : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
  have hpre : {y : Torus d | ¬ y ≠ x} = {x} := by
    ext y; simp
  rw [MeasureTheory.ae_iff, hpre]
  exact volume_singleton_torus hd x

/-- Fibre Hölder bound: `∫ |G(x-y) ρ(y)| dy ≤ ‖G‖_{q} ‖ρ‖_{r}`, uniformly in `x`. -/
theorem tbr_fibre_lintegral {r q : ℝ} [(ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q)]
    {G ρ : Torus d → ℝ} (hG : MemLp G (ENNReal.ofReal q) volume)
    (hρ : MemLp ρ (ENNReal.ofReal r) volume) (x : Torus d) :
    ∫⁻ y, ‖G (x - y) * ρ y‖ₑ ≤
      eLpNorm G (ENNReal.ofReal q) volume * eLpNorm ρ (ENNReal.ofReal r) volume := by
  have hm1 : AEStronglyMeasurable (fun y => G (x - y)) volume :=
    hG.aestronglyMeasurable.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hmeas : AEStronglyMeasurable (fun y => G (x - y) * ρ y) volume :=
    hm1.mul hρ.aestronglyMeasurable
  have h1 : eLpNorm (fun y => G (x - y)) (ENNReal.ofReal q) volume =
      eLpNorm G (ENNReal.ofReal q) volume :=
    eLpNorm_comp_measurePreserving hG.aestronglyMeasurable (volume.measurePreserving_sub_left x)
  have h2 := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volume) (p := ENNReal.ofReal q)
    (q := ENNReal.ofReal r) (r := 1) (fun a b : ℝ => a * b) 1 continuous_mul hm1
    hρ.aestronglyMeasurable (Filter.Eventually.of_forall fun y => by simp [nnnorm_mul])
  rw [← eLpNorm_one_eq_lintegral_enorm hmeas]
  rw [h1] at h2
  simpa using h2

/-- Tonelli bound on `𝕋^d × 𝕋^d`: `∬ |ρ(x)| |G(x-y)| |ρ(y)| < ∞`. -/
theorem tbr_prod_lintegral_lt_top {r q : ℝ} [(ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q)]
    {G ρ : Torus d → ℝ} (hGm : Measurable G) (hG : MemLp G (ENNReal.ofReal q) volume)
    (hρ : MemLp ρ (ENNReal.ofReal r) volume) (h1 : Integrable ρ) :
    ∫⁻ z : Torus d × Torus d, ‖ρ z.1‖ₑ * ‖G (z.1 - z.2) * ρ z.2‖ₑ ∂(volume.prod volume) < ⊤ := by
  have hρa : AEMeasurable ρ (volume : Measure (Torus d)) := hρ.aestronglyMeasurable.aemeasurable
  have hF1 : AEMeasurable (fun z : Torus d × Torus d => ‖ρ z.1‖ₑ) ((volume : Measure (Torus d)).prod volume) :=
    (hρa.comp_fst (ν := volume)).enorm
  have hF2 : AEMeasurable (fun z : Torus d × Torus d => ‖G (z.1 - z.2) * ρ z.2‖ₑ)
      ((volume : Measure (Torus d)).prod volume) :=
    (((hGm.comp (measurable_fst.sub measurable_snd)).aemeasurable).mul
      (hρa.comp_snd (μ := volume))).enorm
  have hF : AEMeasurable (fun z : Torus d × Torus d => ‖ρ z.1‖ₑ * ‖G (z.1 - z.2) * ρ z.2‖ₑ)
      ((volume : Measure (Torus d)).prod volume) := hF1.mul hF2
  rw [lintegral_prod _ hF]
  have hM : eLpNorm G (ENNReal.ofReal q) volume * eLpNorm ρ (ENNReal.ofReal r) volume < ⊤ :=
    ENNReal.mul_lt_top hG.eLpNorm_lt_top hρ.eLpNorm_lt_top
  calc ∫⁻ x, ∫⁻ y, ‖ρ (x, y).1‖ₑ * ‖G ((x, y).1 - (x, y).2) * ρ (x, y).2‖ₑ ∂volume ∂volume
      ≤ ∫⁻ x, ‖ρ x‖ₑ * (eLpNorm G (ENNReal.ofReal q) volume * eLpNorm ρ (ENNReal.ofReal r) volume) := by
        refine lintegral_mono fun x => ?_
        simp only
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        gcongr
        exact tbr_fibre_lintegral hG hρ x
    _ = (∫⁻ x, ‖ρ x‖ₑ) * (eLpNorm G (ENNReal.ofReal q) volume * eLpNorm ρ (ENNReal.ofReal r) volume) :=
        lintegral_mul_const' _ _ hM.ne
    _ < ⊤ := ENNReal.mul_lt_top h1.2 hM

/-- Integrability of the pair integrand `k(x,y) ρ(x) ρ(y)` on `𝕋^d × 𝕋^d`, from the kernel bound
`|k(x,y)| ≤ C |G(x-y)|` off the diagonal. -/
theorem tbr_integrable_pair {r q : ℝ} [(ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q)]
    (hd : 1 ≤ d) {G ρ : Torus d → ℝ} (hGm : Measurable G) (hG : MemLp G (ENNReal.ofReal q) volume)
    (hρ : MemLp ρ (ENNReal.ofReal r) volume) (h1 : Integrable ρ)
    {k : Torus d → Torus d → ℝ} (hkm : Measurable (fun z : Torus d × Torus d => k z.1 z.2))
    {C : ℝ} (hC : 0 ≤ C) (hk : ∀ x y : Torus d, x ≠ y → |k x y| ≤ C * |G (x - y)|) :
    Integrable (fun z : Torus d × Torus d => k z.1 z.2 * ρ z.1 * ρ z.2) ((volume : Measure (Torus d)).prod volume) := by
  have hρa : AEMeasurable ρ (volume : Measure (Torus d)) := hρ.aestronglyMeasurable.aemeasurable
  have hm1 : AEStronglyMeasurable (fun z : Torus d × Torus d => ρ z.1) ((volume : Measure (Torus d)).prod volume) :=
    (hρa.comp_fst (ν := volume)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun z : Torus d × Torus d => ρ z.2) ((volume : Measure (Torus d)).prod volume) :=
    (hρa.comp_snd (μ := volume)).aestronglyMeasurable
  have hm : AEStronglyMeasurable (fun z : Torus d × Torus d => k z.1 z.2 * ρ z.1 * ρ z.2)
      ((volume : Measure (Torus d)).prod volume) :=
    (hkm.aestronglyMeasurable.mul hm1).mul hm2
  refine ⟨hm, ?_⟩
  have hfin := tbr_prod_lintegral_lt_top hGm hG hρ h1
  calc ∫⁻ z, ‖k z.1 z.2 * ρ z.1 * ρ z.2‖ₑ ∂((volume : Measure (Torus d)).prod volume)
      ≤ ∫⁻ z, ENNReal.ofReal C * (‖ρ z.1‖ₑ * ‖G (z.1 - z.2) * ρ z.2‖ₑ)
          ∂((volume : Measure (Torus d)).prod volume) := by
        refine lintegral_mono_ae ((tbr_ae_ne_prod hd).mono fun z hz => ?_)
        simp only [enorm_mul]
        have hkz := tbr_enorm_le hC (hk z.1 z.2 hz)
        calc ‖k z.1 z.2‖ₑ * ‖ρ z.1‖ₑ * ‖ρ z.2‖ₑ
            ≤ (ENNReal.ofReal C * ‖G (z.1 - z.2)‖ₑ) * ‖ρ z.1‖ₑ * ‖ρ z.2‖ₑ := by
              gcongr
          _ = ENNReal.ofReal C * (‖ρ z.1‖ₑ * (‖G (z.1 - z.2)‖ₑ * ‖ρ z.2‖ₑ)) := by ring
    _ = ENNReal.ofReal C * ∫⁻ z, ‖ρ z.1‖ₑ * ‖G (z.1 - z.2) * ρ z.2‖ₑ
          ∂((volume : Measure (Torus d)).prod volume) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- Integrability of the fibre `y ↦ k(x,y) ρ(y)` for each fixed `x`. -/
theorem tbr_integrable_fibre {r q : ℝ} [(ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q)]
    (hd : 1 ≤ d) {G ρ : Torus d → ℝ} (hG : MemLp G (ENNReal.ofReal q) volume)
    (hρ : MemLp ρ (ENNReal.ofReal r) volume)
    {k : Torus d → Torus d → ℝ} (hkm : Measurable (fun z : Torus d × Torus d => k z.1 z.2))
    {C : ℝ} (hC : 0 ≤ C) (hk : ∀ x y : Torus d, x ≠ y → |k x y| ≤ C * |G (x - y)|) (x : Torus d) :
    Integrable (fun y => k x y * ρ y) (volume : Measure (Torus d)) := by
  have hkx : Measurable (fun y => k x y) := hkm.comp (measurable_const.prodMk measurable_id)
  refine ⟨(hkx.aestronglyMeasurable).mul hρ.aestronglyMeasurable, ?_⟩
  have hM : eLpNorm G (ENNReal.ofReal q) volume * eLpNorm ρ (ENNReal.ofReal r) volume < ⊤ :=
    ENNReal.mul_lt_top hG.eLpNorm_lt_top hρ.eLpNorm_lt_top
  calc ∫⁻ y, ‖k x y * ρ y‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal C * ‖G (x - y) * ρ y‖ₑ := by
        refine lintegral_mono_ae ((tbr_ae_ne hd x).mono fun y hy => ?_)
        simp only [enorm_mul]
        have hkz := tbr_enorm_le hC (hk x y (Ne.symm hy))
        calc ‖k x y‖ₑ * ‖ρ y‖ₑ ≤ (ENNReal.ofReal C * ‖G (x - y)‖ₑ) * ‖ρ y‖ₑ := by gcongr
          _ = ENNReal.ofReal C * (‖G (x - y)‖ₑ * ‖ρ y‖ₑ) := by ring
    _ = ENNReal.ofReal C * ∫⁻ y, ‖G (x - y) * ρ y‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * (eLpNorm G (ENNReal.ofReal q) volume * eLpNorm ρ (ENNReal.ofReal r) volume) := by
        gcongr
        exact tbr_fibre_lintegral hG hρ x
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM

/-- The pair-integrability predicate `PairIntegrableT` from the kernel bound. -/
theorem tbr_pairIntegrable {r q : ℝ} [(ENNReal.ofReal r).HolderConjugate (ENNReal.ofReal q)]
    (hd : 1 ≤ d) {G ρ : Torus d → ℝ} (hGm : Measurable G) (hG : MemLp G (ENNReal.ofReal q) volume)
    (hρ : MemLp ρ (ENNReal.ofReal r) volume) (h1 : Integrable ρ)
    {k : Torus d → Torus d → ℝ} (hkm : Measurable (fun z : Torus d × Torus d => k z.1 z.2))
    {C : ℝ} (hC : 0 ≤ C) (hk : ∀ x y : Torus d, x ≠ y → |k x y| ≤ C * |G (x - y)|)
    {N : ℕ} (X : Config d N) :
    PairIntegrableT k X ρ :=
  ⟨fun i => tbr_integrable_fibre hd hG hρ hkm hC hk (X i),
    tbr_integrable_pair hd hGm hG hρ h1 hkm hC hk⟩

end HRS.Commutator.TorusNote
