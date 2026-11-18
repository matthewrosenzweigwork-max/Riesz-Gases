import HRS.MS.CzHlsAux1
import HRS.Whole.AppendixAAdjoint

/-!
# HLS-GLUE, part 2: `lp_screened_negative_order_lt_one` (the `0 < θ < 1` conjunct of S.A.15 (i)) and the
# Riesz-force kernel bounds with `L^q → L^p` bounds (S.A.16 E1)

Packet HLSG (CZ development), the first conjunct of the frozen theorem `HRS.Whole.lp_screened_negative_order`
(`HRS/Whole/AppendixAAdjoint.lean:897`) as a standalone theorem.  Self-contained: it uses only the definition
`pvOdd` (not any PV-API lemma).

Content: for `0 < θ < 1`, a continuous `Ω` (`IsOddSmooth Ω` gives `Continuous Ω`; oddness is not needed here),
`1 < p`, `1/p + (1-θ)/d < 1` (this is exactly `q > 1` for `1/q = 1/p + (1-θ)/d`):
`‖pvOdd θ Ω (aW)‖_p ≤ C ‖a‖_{d/(1-θ)} ‖W‖_p` for `a ∈ L^{d/(1-θ)}`, `W ∈ L^p`, with the same shape of
conclusion as the frozen statement.

Steps (all in this file):
* `hlsg_pvOdd_eq_integral`: if `I_{1-θ}|h|(x) < ⊤` then the truncations converge (dominated convergence) and
  `pvOdd d θ Ω h x = ∫ z, Ω(z/|z|)/|z|^{d+θ-1} h(x-z) dz`, absolutely convergent;
* `hlsg_pvOdd_enorm_le`: `‖pvOdd d θ Ω h x‖ₑ ≤ ofReal B * I_{1-θ}|h|(x)` with `B` a bound of `|Ω|` on the sphere;
* `hlsg_pvOdd_aesm`: `pvOdd d θ Ω h` is a.e. strongly measurable for `h` a.e. strongly measurable, in the
  `I_{1-θ}|h| < ⊤` a.e. regime (needed because `eLpNorm` of a non-a.e.-measurable function is `⊤`);
* Hölder `‖aW‖_q ≤ ‖a‖_{d/(1-θ)} ‖W‖_p` (`1/q = 1/p + (1-θ)/d`) and `riesz_pot_Lp` (`σ = 1 - θ`).

Second half (section `Force`, S.A.16 E1; `g = rieszKernel d s`, `c_s = s` for `s > 0`, `c_0 = 1`):
* `force_kernel_formula`, `force_kernel_bound` (`|∂_v g(z)| ≤ c_s |z|^{-s-1} |v|`, `s ≥ 0`, `z ≠ 0`; coordinate form
  `force_kernel_bound_coord`), `force_kernel_bound2` (`|∂_w ∂_v g(z)| ≤ c_s (s+3) |z|^{-s-2} |v||w|`);
* `force_conv_enorm_le`: the convolution form `‖g' * u (x)‖ₑ ≤ c_s|v| · I_{d-s-1}|u|(x)` in `ENNReal` (no integrability of
  the integrand needed: the Bochner integral of a non-integrable integrand is `0`, which is below the bound);
* `riesz_force_Lp` (`σ = d-s-1`, case (i)) and `riesz_force2_Lp` (`σ = d-s-2`, `s < d-2`): `‖∂_v g * u‖_p ≤ C|v|‖u‖_q`
  resp. `‖∂_w∂_v g * u‖_p ≤ C|v||w|‖u‖_q` for `1 < q < p`, `1/p = 1/q - σ/d`; exponent forms `riesz_force_Lp_of_p`
  (`q > 1 ↔ p(s+1) > d`, `hlsg_q_gt_one_iff`) and `riesz_force2_Lp_of_p` (`p(s+2) > d`).
  The convolution is `HRS.Whole.convFun`, `convFun g u x = ∫ y, g(x-y) u(y) dy`.  The case `s = 0` (`g = -log|z|`) is
  included (`c_0 = 1`).  Derivatives are Mathlib's `fderiv` (at `z = 0` they are junk, but `{0}` is null and every
  statement only uses `z ≠ 0`).

Corner cases: `a = 0` a.e. or `‖a‖ = 0` is covered (the bound reads `0 ≤ 0`-type, with all quantities finite);
`p = q` cannot occur since `θ < 1`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.CZ.Hls

open HRS.Commutator.Whole HRS.Whole.AppendixA HRS.Whole

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the kernel `Ω(z/|z|)/|z|^{d+θ-1}` of `pvOdd` -/
def hlsg_K (d : ℕ) (θ : ℝ) (Ω : EuclideanSpace ℝ (Fin d) → ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Ω (‖z‖⁻¹ • z) / ‖z‖ ^ ((d : ℝ) + θ - 1)

lemma hlsg_K_measurable (θ : ℝ) {Ω : 𝔼 → ℝ} (hΩ : Continuous Ω) : Measurable (hlsg_K d θ Ω) := by
  unfold hlsg_K
  exact (hΩ.measurable.comp (measurable_norm.inv.smul measurable_id)).div
    (measurable_norm.pow_const _)

lemma hlsg_K_zero (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) (Ω : 𝔼 → ℝ) : hlsg_K d θ Ω 0 = 0 := by
  have : (d : ℝ) + θ - 1 ≠ 0 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  simp [hlsg_K, Real.zero_rpow this]

/-- pointwise kernel bound `|K(z)| ≤ B |z|^{(1-θ)-d}` -/
lemma hlsg_K_le (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ w : 𝔼, ‖w‖ = 1 → |Ω w| ≤ B) (z : 𝔼) :
    ‖hlsg_K d θ Ω z‖ ≤ B * ‖z‖ ^ ((1 - θ) - (d : ℝ)) := by
  by_cases hz : z = 0
  · subst hz
    rw [hlsg_K_zero hd hθ]
    simp only [norm_zero]
    positivity
  · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hu : ‖‖z‖⁻¹ • z‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hzpos.ne']
    have hexp : ‖z‖ ^ ((1 - θ) - (d : ℝ)) = (‖z‖ ^ ((d : ℝ) + θ - 1))⁻¹ := by
      rw [← Real.rpow_neg hzpos.le]; congr 1; ring
    rw [hexp, hlsg_K, Real.norm_eq_abs, abs_div, abs_of_pos (Real.rpow_pos_of_pos hzpos _),
      div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hB _ hu) (by positivity)

/-- Convergence of the truncated integrals: if `I_{1-θ}|h|(x) < ⊤`, the `limUnder` in `pvOdd` is the
absolutely convergent integral. -/
lemma hlsg_pvOdd_eq_integral (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} (hΩ : Continuous Ω)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ w : 𝔼, ‖w‖ = 1 → |Ω w| ≤ B)
    {h : 𝔼 → ℝ} (hh : AEStronglyMeasurable h volume) (x : 𝔼)
    (hx : cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x < ⊤) :
    Integrable (fun z => hlsg_K d θ Ω z * h (x - z)) volume ∧
    pvOdd d θ Ω h x = ∫ z, hlsg_K d θ Ω z * h (x - z) := by
  set G : 𝔼 → ℝ := fun z => hlsg_K d θ Ω z * h (x - z) with hG
  have hGm : AEStronglyMeasurable G volume :=
    (hlsg_K_measurable θ hΩ).aestronglyMeasurable.mul
      (hh.comp_quasiMeasurePreserving (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving)
  have hbd : ∀ z, ‖G z‖ₑ ≤ ENNReal.ofReal B *
      (ENNReal.ofReal (‖z‖ ^ ((1 - θ) - (d : ℝ))) * ‖h (x - z)‖ₑ) := by
    intro z
    rw [hG]
    simp only
    rw [enorm_mul, ← mul_assoc, ← ENNReal.ofReal_mul hB0]
    refine mul_le_mul_left ?_ _
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hlsg_K_le hd hθ hB0 hB z)
  have hint : Integrable G volume := by
    refine ⟨hGm, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ z, ‖G z‖ₑ ≤ ∫⁻ z, ENNReal.ofReal B *
          (ENNReal.ofReal (‖z‖ ^ ((1 - θ) - (d : ℝ))) * ‖h (x - z)‖ₑ) := lintegral_mono hbd
      _ = ENNReal.ofReal B * cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hlsg_pot_eq_z]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hx
  refine ⟨hint, ?_⟩
  have hlim : Tendsto (fun ε : ℝ => ∫ z in {z : 𝔼 | ε < ‖z‖}, G z) (𝓝[>] 0) (𝓝 (∫ z, G z)) := by
    have hind : ∀ ε : ℝ, ∫ z in {z : 𝔼 | ε < ‖z‖}, G z = ∫ z, {z : 𝔼 | ε < ‖z‖}.indicator G z :=
      fun ε => (integral_indicator (measurableSet_lt measurable_const measurable_norm)).symm
    simp_rw [hind]
    refine tendsto_integral_filter_of_dominated_convergence (fun z => ‖G z‖)
      (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => ?_) hint.norm
      (Eventually.of_forall fun z => ?_)
    · exact hGm.indicator (measurableSet_lt measurable_const measurable_norm)
    · exact Eventually.of_forall fun z => norm_indicator_le_norm_self _ _
    · by_cases hz : z = 0
      · subst hz
        have : G 0 = 0 := by simp [hG, hlsg_K_zero hd hθ]
        have h0 : ∀ ε : ℝ, ({z : 𝔼 | ε < ‖z‖}).indicator G 0 = 0 := fun ε => by
          by_cases hε : ε < ‖(0 : 𝔼)‖
          · simp [this]
          · simp [indicator_of_notMem (show (0 : 𝔼) ∉ {z : 𝔼 | ε < ‖z‖} from hε)]
        simp [h0, this]
      · have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hzpos] with ε hε
        simp [indicator_of_mem (show z ∈ {z : 𝔼 | ε < ‖z‖} from hε.2)]
  exact hlim.limUnder_eq

/-- `‖pvOdd d θ Ω h x‖ₑ ≤ B · I_{1-θ}|h|(x)` where finite. -/
lemma hlsg_pvOdd_enorm_le (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} (hΩ : Continuous Ω)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ w : 𝔼, ‖w‖ = 1 → |Ω w| ≤ B)
    {h : 𝔼 → ℝ} (hh : AEStronglyMeasurable h volume) (x : 𝔼)
    (hx : cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x < ⊤) :
    ‖pvOdd d θ Ω h x‖ₑ ≤ ENNReal.ofReal B * cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x := by
  obtain ⟨-, heq⟩ := hlsg_pvOdd_eq_integral hd hθ hΩ hB0 hB hh x hx
  rw [heq, hlsg_pot_eq_z, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
  rw [enorm_mul, ← mul_assoc, ← ENNReal.ofReal_mul hB0]
  refine mul_le_mul_left ?_ _
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hlsg_K_le hd hθ hB0 hB z)

/-- a.e. strong measurability of `pvOdd d θ Ω h` (where the potential is a.e. finite). -/
lemma hlsg_pvOdd_aesm (hd : 1 ≤ d) {θ : ℝ} (hθ : 0 < θ) {Ω : 𝔼 → ℝ} (hΩ : Continuous Ω)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ w : 𝔼, ‖w‖ = 1 → |Ω w| ≤ B)
    {h : 𝔼 → ℝ} (hh : AEStronglyMeasurable h volume)
    (hfin : ∀ᵐ x ∂volume, cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x < ⊤) :
    AEStronglyMeasurable (pvOdd d θ Ω h) volume := by
  refine (hlsg_aesm_conv (hlsg_K_measurable θ hΩ) hh).congr ?_
  filter_upwards [hfin] with x hx
  exact (hlsg_pvOdd_eq_integral hd hθ hΩ hB0 hB hh x hx).2.symm

/-- Hölder for products in `ENNReal`-exponent form, with real exponents `1/q = 1/r + 1/p`. -/
lemma hlsg_holder {r p q : ℝ} (hr : 0 < r) (hp : 0 < p) (hq : 0 < q) (hrel : r⁻¹ + p⁻¹ = q⁻¹)
    {a W : 𝔼 → ℝ} (ha : AEStronglyMeasurable a volume) (hW : AEStronglyMeasurable W volume) :
    eLpNorm (fun x => a x * W x) (ENNReal.ofReal q) volume ≤
      eLpNorm a (ENNReal.ofReal r) volume * eLpNorm W (ENNReal.ofReal p) volume := by
  have : ENNReal.HolderTriple (ENNReal.ofReal r) (ENNReal.ofReal p) (ENNReal.ofReal q) :=
    ⟨by
      rw [← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_inv_of_pos hp,
        ← ENNReal.ofReal_inv_of_pos hq, ← ENNReal.ofReal_add (by positivity) (by positivity), hrel]⟩
  exact eLpNorm_smul_le_mul_eLpNorm ha hW

/-- **`lp_screened_negative_order_lt_one`**: the `0 < θ < 1` conjunct of `lp_screened_negative_order`
(S.A.15 (i), `AppendixAAdjoint.lean:897`): `‖𝒯_θ(aW)‖_p ≤ C ‖a‖_{d/(1-θ)} ‖W‖_p`.  The frozen hypothesis
`2 ≤ p` is weakened to `1 < p`; `IsOddSmooth Ω` is weakened to `Continuous Ω`. -/
theorem lp_screened_negative_order_lt_one (hd : 1 ≤ d) (θ p : ℝ) (Ω : 𝔼 → ℝ) (hΩ : Continuous Ω)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hp : 1 < p) (hq : 1 / p + (1 - θ) / d < 1) :
    ∃ C : ℝ, ∀ a W : 𝔼 → ℝ, MemLp a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume →
      MemLp W (ENNReal.ofReal p) volume →
      eLpNorm (pvOdd d θ Ω fun x => a x * W x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume *
          eLpNorm W (ENNReal.ofReal p) volume := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hr0 : 0 < (d : ℝ) / (1 - θ) := by positivity
  -- the intermediate exponent `1/q = 1/p + (1-θ)/d`
  set q : ℝ := (1 / p + (1 - θ) / d)⁻¹ with hqdef
  have hqinv : 1 / q = 1 / p + (1 - θ) / d := by rw [hqdef, one_div, inv_inv]
  have hq0 : 0 < q := by positivity
  have hq1 : 1 < q := by
    have : 1 / q < 1 := by rw [hqinv]; exact hq
    by_contra hcon
    rw [not_lt] at hcon
    have : 1 ≤ 1 / q := by rw [le_div_iff₀ hq0]; linarith
    linarith
  have hqp : q < p := by
    have hpos : 0 < (1 - θ) / d := by positivity
    have : 1 / p < 1 / q := by rw [hqinv]; linarith
    exact (one_div_lt_one_div hp0 hq0).1 this
  have hrel : 1 / p = 1 / q - (1 - θ) / d := by rw [hqinv]; ring
  obtain ⟨CH, hCH, hHLS⟩ := riesz_pot_Lp hd (σ := 1 - θ) h1θ hq1 hqp hrel
  obtain ⟨B0, hB0⟩ := (isCompact_sphere (0 : 𝔼) 1).exists_bound_of_continuousOn hΩ.continuousOn
  set B : ℝ := max B0 0 with hBdef
  have hBnn : 0 ≤ B := le_max_right _ _
  have hB : ∀ w : 𝔼, ‖w‖ = 1 → |Ω w| ≤ B := fun w hw =>
    (hB0 w (by simpa using hw)).trans (le_max_left _ _)
  refine ⟨B * CH, fun a W ha hW => ?_⟩
  set r : ℝ := (d : ℝ) / (1 - θ) with hrdef
  have hrel' : r⁻¹ + p⁻¹ = q⁻¹ := by
    have h2 := hqinv
    rw [one_div, one_div] at h2
    rw [h2, hrdef, inv_div]; ring
  have hholder := hlsg_holder hr0 hp0 hq0 hrel' ha.aestronglyMeasurable hW.aestronglyMeasurable
  set h : 𝔼 → ℝ := fun x => a x * W x with hh
  have hhm : AEStronglyMeasurable h volume := ha.aestronglyMeasurable.mul hW.aestronglyMeasurable
  have hhq : MemLp h (ENNReal.ofReal q) volume :=
    memLp_iff.2 (lt_of_le_of_lt hholder (ENNReal.mul_lt_top ha.eLpNorm_lt_top hW.eLpNorm_lt_top))
  have hfin := riesz_pot_ae_lt_top hd (σ := 1 - θ) h1θ hq1 hqp hrel hhq
  have hmeas := hlsg_pvOdd_aesm hd hθ0 hΩ hBnn hB hhm hfin
  -- pointwise domination
  have hdom : ∀ᵐ x ∂volume, ‖pvOdd d θ Ω h x‖ₑ ≤
      ENNReal.ofReal B * cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x := by
    filter_upwards [hfin] with x hx
    exact hlsg_pvOdd_enorm_le hd hθ0 hΩ hBnn hB hhm x hx
  have hnorm : eLpNorm (pvOdd d θ Ω h) (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖pvOdd d θ Ω h x‖ₑ ^ p) ^ (1 / p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top hmeas,
      ENNReal.toReal_ofReal hp0.le]
  have h1 : eLpNorm (pvOdd d θ Ω h) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal B * (∫⁻ x, cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x ^ p) ^ (1 / p) := by
    rw [hnorm]
    calc (∫⁻ x, ‖pvOdd d θ Ω h x‖ₑ ^ p) ^ (1 / p)
        ≤ (∫⁻ x, (ENNReal.ofReal B * cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x) ^ p) ^ (1 / p) :=
          ENNReal.rpow_le_rpow (lintegral_mono_ae (hdom.mono fun x hx =>
            ENNReal.rpow_le_rpow hx hp0.le)) (by positivity)
      _ = ENNReal.ofReal B * (∫⁻ x, cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x ^ p) ^ (1 / p) := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
            ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  have h2 := hHLS h hhm
  calc eLpNorm (pvOdd d θ Ω h) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal B * (∫⁻ x, cmxHLS_I (1 - θ) (fun y => ‖h y‖ₑ) x ^ p) ^ (1 / p) := h1
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal CH * eLpNorm h (ENNReal.ofReal q) volume) :=
        by gcongr
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal CH *
          (eLpNorm a (ENNReal.ofReal r) volume * eLpNorm W (ENNReal.ofReal p) volume)) :=
        by gcongr
    _ = ENNReal.ofReal (B * CH) * eLpNorm a (ENNReal.ofReal r) volume *
          eLpNorm W (ENNReal.ofReal p) volume := by
        rw [ENNReal.ofReal_mul hBnn]; ring

/-! ### Kernels of the Riesz force `∇ g`, `g = rieszKernel d s` (S.A.16 E1) -/

section Force

open scoped RealInnerProductSpace

/-- the constant `c_s` in `∇ g = -c_s z |z|^{-s-2}` (`c_s = s` for `s ≠ 0`, `c_0 = 1` for `g = -log|z|`) -/
def hlsg_c (s : ℝ) : ℝ := if s = 0 then 1 else s

lemma hlsg_c_pos {s : ℝ} (hs : 0 ≤ s) : 0 < hlsg_c s := by
  unfold hlsg_c; split_ifs with h
  · norm_num
  · exact lt_of_le_of_ne hs (Ne.symm h)

lemma hlsg_c_nonneg {s : ℝ} (hs : 0 ≤ s) : 0 ≤ hlsg_c s := (hlsg_c_pos hs).le

lemma hlsg_hasFDerivAt_norm_rpow {x : 𝔼} (hx : x ≠ 0) (p : ℝ) :
    HasFDerivAt (fun y : 𝔼 => ‖y‖ ^ p) ((p * ‖x‖ ^ (p - 2)) • innerSL ℝ x) x := by
  apply HasStrictFDerivAt.hasFDerivAt
  convert! (hasStrictFDerivAt_norm_sq x).rpow_const (p := p / 2) (by simp [hx]) using 0
  simp_rw [← Real.rpow_natCast_mul (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  ring_nf

/-- derivative of `rieszKernel d s` away from `0` -/
lemma hlsg_hasFDerivAt_rieszKernel (s : ℝ) {x : 𝔼} (hx : x ≠ 0) :
    HasFDerivAt (rieszKernel d s) ((-(hlsg_c s * ‖x‖ ^ (-s - 2))) • innerSL ℝ x) x := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  by_cases hs : s = 0
  · subst hs
    have h1 := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.log (by simpa using hx)).neg
    have h2 := h1.const_smul (1 / 2 : ℝ)
    have hfun : (rieszKernel d 0) = (1 / 2 : ℝ) • (-fun y : 𝔼 => Real.log (‖y‖ ^ 2)) := by
      funext y
      simp [rieszKernel, Real.log_pow]
    rw [hfun]
    convert h2 using 1
    ext v
    simp [hlsg_c]
    ring
  · have h1 := hlsg_hasFDerivAt_norm_rpow hx (-s)
    have hfun : (rieszKernel d s) = fun y : 𝔼 => ‖y‖ ^ (-s) := by
      funext y; simp [rieszKernel, hs]
    rw [hfun]
    convert h1 using 2
    simp [hlsg_c, hs]

/-- exact formula `∂_v g(z) = -c_s |z|^{-s-2} ⟨z, v⟩` -/
lemma force_kernel_formula (s : ℝ) {z : 𝔼} (hz : z ≠ 0) (v : 𝔼) :
    fderiv ℝ (rieszKernel d s) z v = -(hlsg_c s * ‖z‖ ^ (-s - 2) * ⟪z, v⟫) := by
  rw [(hlsg_hasFDerivAt_rieszKernel s hz).fderiv]
  simp

/-- **`force_kernel_bound`**: `|∂_v g(z)| ≤ c_s |z|^{-s-1} |v|` for `s ≥ 0`, `z ≠ 0`
(`c_s = s` for `s > 0`, `c_0 = 1`). -/
theorem force_kernel_bound {s : ℝ} (hs : 0 ≤ s) {z : 𝔼} (hz : z ≠ 0) (v : 𝔼) :
    |fderiv ℝ (rieszKernel d s) z v| ≤ hlsg_c s * ‖z‖ ^ (-s - 1) * ‖v‖ := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hc := hlsg_c_nonneg hs
  rw [force_kernel_formula s hz, abs_neg, abs_mul, abs_of_nonneg (by positivity : 0 ≤ hlsg_c s * ‖z‖ ^ (-s - 2))]
  have h1 : ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s - 2) * ‖z‖ := by
    rw [← Real.rpow_add_one hzpos.ne']; congr 1; ring
  calc hlsg_c s * ‖z‖ ^ (-s - 2) * |⟪z, v⟫| ≤ hlsg_c s * ‖z‖ ^ (-s - 2) * (‖z‖ * ‖v‖) := by
        gcongr; exact abs_real_inner_le_norm z v
    _ = hlsg_c s * ‖z‖ ^ (-s - 1) * ‖v‖ := by rw [h1]; ring

/-- coordinate form: `|∂_i g(z)| ≤ c_s |z|^{-s-1}`. -/
theorem force_kernel_bound_coord {s : ℝ} (hs : 0 ≤ s) {z : 𝔼} (hz : z ≠ 0) (i : Fin d) :
    |fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single i 1)| ≤ hlsg_c s * ‖z‖ ^ (-s - 1) := by
  simpa using force_kernel_bound hs hz (EuclideanSpace.single i (1 : ℝ))

/-- derivative of the force `z ↦ ∂_v g(z)` away from `0` (as a formula for its value on `w`) -/
lemma hlsg_force_second_formula (s : ℝ) {z : 𝔼} (hz : z ≠ 0) (v w : 𝔼) :
    fderiv ℝ (fun y => fderiv ℝ (rieszKernel d s) y v) z w =
      -(hlsg_c s * (‖z‖ ^ (-s - 2) * ⟪v, w⟫ + ⟪v, z⟫ * ((-s - 2) * ‖z‖ ^ (-s - 2 - 2) * ⟪z, w⟫))) := by
  have h1 := (hlsg_hasFDerivAt_norm_rpow hz (-s - 2)).mul (innerSL ℝ v).hasFDerivAt
  have h2 := (h1.const_mul (hlsg_c s)).neg
  have hev : (fun y : 𝔼 => fderiv ℝ (rieszKernel d s) y v) =ᶠ[nhds z]
      -fun y : 𝔼 => hlsg_c s * (‖y‖ ^ (-s - 2) * (innerSL ℝ v) y) := by
    filter_upwards [isOpen_ne.mem_nhds hz] with y hy
    rw [force_kernel_formula s hy, real_inner_comm]
    simp
    ring
  rw [(h2.congr_of_eventuallyEq hev).fderiv]
  simp [real_inner_comm]
  ring

/-- **`force_kernel_bound2`**: `|∂_w ∂_v g(z)| ≤ c_s (s+3) |z|^{-s-2} |v| |w|` for `s ≥ 0`, `z ≠ 0`
(with `v = e_i`, `w = e_j` this is `|∂_i ∂_j g| ≤ C |z|^{-s-2}`, `C = c_s (s+3)`). -/
theorem force_kernel_bound2 {s : ℝ} (hs : 0 ≤ s) {z : 𝔼} (hz : z ≠ 0) (v w : 𝔼) :
    |fderiv ℝ (fun y => fderiv ℝ (rieszKernel d s) y v) z w| ≤
      hlsg_c s * (s + 3) * ‖z‖ ^ (-s - 2) * (‖v‖ * ‖w‖) := by
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hc := hlsg_c_nonneg hs
  rw [hlsg_force_second_formula s hz, abs_neg, abs_mul, abs_of_nonneg hc]
  set A : ℝ := ‖z‖ ^ (-s - 2) with hA
  set P : ℝ := ‖z‖ ^ (-s - 2 - 2) with hP
  have hP0 : 0 < P := Real.rpow_pos_of_pos hzpos _
  have hA0 : 0 < A := Real.rpow_pos_of_pos hzpos _
  have hAP : A = P * ‖z‖ ^ 2 := by
    rw [hA, hP, ← Real.rpow_natCast, ← Real.rpow_add hzpos]; congr 1; push_cast; ring
  have hvw : |⟪v, w⟫| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
  have hvz : |⟪v, z⟫| ≤ ‖v‖ * ‖z‖ := abs_real_inner_le_norm v z
  have hzw : |⟪z, w⟫| ≤ ‖z‖ * ‖w‖ := abs_real_inner_le_norm z w
  have hs2 : |(-s - 2)| = s + 2 := by rw [abs_of_nonpos (by linarith)]; ring
  have hmain : |A * ⟪v, w⟫ + ⟪v, z⟫ * ((-s - 2) * P * ⟪z, w⟫)| ≤ (s + 3) * A * (‖v‖ * ‖w‖) := by
    refine (abs_add_le _ _).trans ?_
    have e1 : |A * ⟪v, w⟫| ≤ A * (‖v‖ * ‖w‖) := by
      rw [abs_mul, abs_of_pos hA0]; gcongr
    have e2 : |⟪v, z⟫ * ((-s - 2) * P * ⟪z, w⟫)| ≤ (s + 2) * A * (‖v‖ * ‖w‖) := by
      rw [abs_mul, abs_mul, abs_mul, hs2, abs_of_pos hP0]
      calc |⟪v, z⟫| * ((s + 2) * P * |⟪z, w⟫|) ≤ (‖v‖ * ‖z‖) * ((s + 2) * P * (‖z‖ * ‖w‖)) := by
            gcongr
        _ = (s + 2) * A * (‖v‖ * ‖w‖) := by rw [hAP]; ring
    linarith
  calc hlsg_c s * |A * ⟪v, w⟫ + ⟪v, z⟫ * ((-s - 2) * P * ⟪z, w⟫)|
      ≤ hlsg_c s * ((s + 3) * A * (‖v‖ * ‖w‖)) := by gcongr
    _ = hlsg_c s * (s + 3) * A * (‖v‖ * ‖w‖) := by ring

/-- `eLpNorm` of a function dominated a.e. by `B · I_σ|u|`. -/
lemma hlsg_eLpNorm_le_pot {p : ℝ} (hp0 : 0 < p) {σ B : ℝ} (hB0 : 0 ≤ B) {u v : 𝔼 → ℝ}
    (hv : AEStronglyMeasurable v volume)
    (hle : ∀ᵐ x ∂volume, ‖v x‖ₑ ≤ ENNReal.ofReal B * cmxHLS_I σ (fun y => ‖u y‖ₑ) x) :
    eLpNorm v (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal B * (∫⁻ x, cmxHLS_I σ (fun y => ‖u y‖ₑ) x ^ p) ^ (1 / p) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top hv,
    ENNReal.toReal_ofReal hp0.le]
  calc (∫⁻ x, ‖v x‖ₑ ^ p) ^ (1 / p)
      ≤ (∫⁻ x, (ENNReal.ofReal B * cmxHLS_I σ (fun y => ‖u y‖ₑ) x) ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow (lintegral_mono_ae (hle.mono fun x hx =>
          ENNReal.rpow_le_rpow hx hp0.le)) (by positivity)
    _ = ENNReal.ofReal B * (∫⁻ x, cmxHLS_I σ (fun y => ‖u y‖ₑ) x ^ p) ^ (1 / p) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- pointwise convolution bound: if `|K(z)| ≤ c |z|^{σ-d}` for `z ≠ 0` then
`‖∫ K(x-y) u(y) dy‖ₑ ≤ c · I_σ|u|(x)` (in `ENNReal`; no integrability of the integrand is needed). -/
lemma hlsg_conv_enorm_le (hd : 1 ≤ d) {K : 𝔼 → ℝ} {c σ : ℝ} (hc : 0 ≤ c)
    (hbd : ∀ z : 𝔼, z ≠ 0 → ‖K z‖ ≤ c * ‖z‖ ^ (σ - (d : ℝ))) (u : 𝔼 → ℝ) (x : 𝔼) :
    ‖∫ y, K (x - y) * u y‖ₑ ≤ ENNReal.ofReal c * cmxHLS_I σ (fun y => ‖u y‖ₑ) x := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hae : ∀ᵐ y ∂volume, y ≠ x := by
    have := (Set.countable_singleton x).ae_notMem (volume : Measure 𝔼)
    filter_upwards [this] with y hy
    simpa using hy
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  unfold cmxHLS_I cmxHLS_k
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae (hae.mono fun y hy => ?_)
  have hz : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  rw [enorm_mul, ← mul_assoc, ← ENNReal.ofReal_mul hc]
  refine mul_le_mul_left ?_ _
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hbd _ hz)

/-- the convolution `x ↦ ∫ K(x-y) u(y) dy` with a measurable kernel is a.e. strongly measurable -/
lemma hlsg_aesm_conv_y {K : 𝔼 → ℝ} (hK : Measurable K) {u : 𝔼 → ℝ} (hu : AEStronglyMeasurable u volume) :
    AEStronglyMeasurable (fun x => ∫ y, K (x - y) * u y) volume := by
  refine (hlsg_aesm_conv hK hu).congr (Eventually.of_forall fun x => ?_)
  have := integral_sub_left_eq_self (fun y => K (x - y) * u y) (volume : Measure 𝔼) x
  simp only [sub_sub_cancel] at this
  exact this

/-- **HLS for convolution with a kernel dominated by `c |z|^{σ-d}`** (`1 < q < p`, `1/p = 1/q - σ/d`):
`‖K * u‖_p ≤ C c ‖u‖_q`. -/
theorem hlsg_conv_Lp (hd : 1 ≤ d) {σ p q : ℝ} (hσ : 0 < σ) (hq : 1 < q) (hqp : q < p)
    (hrel : 1 / p = 1 / q - σ / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : 𝔼 → ℝ) (c : ℝ), Measurable K → 0 ≤ c →
      (∀ z : 𝔼, z ≠ 0 → ‖K z‖ ≤ c * ‖z‖ ^ (σ - (d : ℝ))) →
      ∀ u : 𝔼 → ℝ, AEStronglyMeasurable u volume →
        eLpNorm (fun x => ∫ y, K (x - y) * u y) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * c) * eLpNorm u (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC, hK⟩ := riesz_pot_Lp hd hσ hq hqp hrel
  have hp0 : 0 < p := by linarith
  refine ⟨C, hC, fun K c hKm hc hbd u hu => ?_⟩
  refine (hlsg_eLpNorm_le_pot hp0 hc (hlsg_aesm_conv_y hKm hu)
    (Eventually.of_forall fun x => hlsg_conv_enorm_le hd hc hbd u x)).trans ?_
  calc ENNReal.ofReal c * (∫⁻ x, cmxHLS_I σ (fun y => ‖u y‖ₑ) x ^ p) ^ (1 / p)
      ≤ ENNReal.ofReal c * (ENNReal.ofReal C * eLpNorm u (ENNReal.ofReal q) volume) := by
        gcongr; exact hK u hu
    _ = ENNReal.ofReal (C * c) * eLpNorm u (ENNReal.ofReal q) volume := by
        rw [mul_comm C c, ENNReal.ofReal_mul hc]; ring

/-- exponent bookkeeping: for `p > 0`, `σ > 0` with `1/p + σ/d < 1` the exponent `q = (1/p + σ/d)⁻¹`
satisfies `1 < q < p` and `1/p = 1/q - σ/d` (`q > 1` is exactly the hypothesis). -/
lemma hlsg_exponents (hd : 1 ≤ d) {p σ : ℝ} (hp : 0 < p) (hσ : 0 < σ) (h : 1 / p + σ / d < 1) :
    ∃ q : ℝ, 1 < q ∧ q < p ∧ 1 / q = 1 / p + σ / d ∧ 1 / p = 1 / q - σ / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hpos : 0 < σ / d := by positivity
  refine ⟨(1 / p + σ / d)⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [← one_div]
    rw [lt_one_div (by norm_num) (by positivity)]
    simpa using h
  · rw [← one_div, one_div_lt (by positivity) hp]
    have : 0 < 1 / p := by positivity
    simp only [one_div] at *
    linarith
  · rw [one_div, inv_inv]
  · rw [one_div ((1 / p + σ / d)⁻¹), inv_inv]; ring

/-- **`riesz_force_Lp`** (S.A.16 E1, case (i)): for `0 ≤ s`, `s + 1 < d`, `1 < q < p`,
`1/p = 1/q - (d-s-1)/d` (equivalently `1/q = 1/p + α/d`, `α = d-s-1 ∈ (0, d-1]`):
`‖∂_v g * u‖_p ≤ C |v| ‖u‖_q`, `g = rieszKernel d s`, for every a.e. strongly measurable `u`
(the right side is `⊤` unless `u ∈ L^q`).  Here `g' * u = convFun (∂_v g) u`. -/
theorem riesz_force_Lp (hd : 1 ≤ d) {s p q : ℝ} (hs : 0 ≤ s) (hsd : s + 1 < d) (hq : 1 < q)
    (hqp : q < p) (hrel : 1 / p = 1 / q - ((d : ℝ) - s - 1) / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : 𝔼) (u : 𝔼 → ℝ), AEStronglyMeasurable u volume →
      eLpNorm (HRS.Whole.convFun (fun z => fderiv ℝ (rieszKernel d s) z v) u) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * ‖v‖) * eLpNorm u (ENNReal.ofReal q) volume := by
  have hσ : 0 < (d : ℝ) - s - 1 := by linarith
  obtain ⟨C, hC, hK⟩ := hlsg_conv_Lp hd hσ hq hqp hrel
  have hc := hlsg_c_nonneg hs
  refine ⟨C * hlsg_c s, ?_, fun v u hu => ?_⟩
  · exact mul_pos hC (hlsg_c_pos hs)
  · have := hK (fun z => fderiv ℝ (rieszKernel d s) z v) (hlsg_c s * ‖v‖)
      (measurable_fderiv_apply_const ℝ (rieszKernel d s) v) (by positivity) (fun z hz => ?_) u hu
    · have e : C * hlsg_c s * ‖v‖ = C * (hlsg_c s * ‖v‖) := by ring
      rw [e]; exact this
    · have h2 := force_kernel_bound hs hz v
      have hexp : ((d : ℝ) - s - 1) - d = -s - 1 := by ring
      rw [hexp, Real.norm_eq_abs]
      linarith [h2, show hlsg_c s * ‖v‖ * ‖z‖ ^ (-s - 1) = hlsg_c s * ‖z‖ ^ (-s - 1) * ‖v‖ by ring]

/-- **`riesz_force2_Lp`** (S.A.16 E1, top term `s < d - 2`): for `0 ≤ s`, `s + 2 < d`, `1 < q < p`,
`1/p = 1/q - (d-s-2)/d`: `‖∂_w∂_v g * u‖_p ≤ C |v| |w| ‖u‖_q`. -/
theorem riesz_force2_Lp (hd : 1 ≤ d) {s p q : ℝ} (hs : 0 ≤ s) (hsd : s + 2 < d) (hq : 1 < q)
    (hqp : q < p) (hrel : 1 / p = 1 / q - ((d : ℝ) - s - 2) / d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v w : 𝔼) (u : 𝔼 → ℝ), AEStronglyMeasurable u volume →
      eLpNorm (HRS.Whole.convFun
          (fun z => fderiv ℝ (fun y => fderiv ℝ (rieszKernel d s) y v) z w) u)
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * (‖v‖ * ‖w‖)) * eLpNorm u (ENNReal.ofReal q) volume := by
  have hσ : 0 < (d : ℝ) - s - 2 := by linarith
  obtain ⟨C, hC, hK⟩ := hlsg_conv_Lp hd hσ hq hqp hrel
  have hc := hlsg_c_pos hs
  refine ⟨C * (hlsg_c s * (s + 3)), mul_pos hC (by positivity), fun v w u hu => ?_⟩
  have hmeas : Measurable (fun z => fderiv ℝ (fun y => fderiv ℝ (rieszKernel d s) y v) z w) :=
    measurable_fderiv_apply_const ℝ (fun y => fderiv ℝ (rieszKernel d s) y v) w
  have := hK (fun z => fderiv ℝ (fun y => fderiv ℝ (rieszKernel d s) y v) z w)
    (hlsg_c s * (s + 3) * (‖v‖ * ‖w‖)) hmeas (by positivity) (fun z hz => ?_) u hu
  · have e : C * (hlsg_c s * (s + 3)) * (‖v‖ * ‖w‖) = C * (hlsg_c s * (s + 3) * (‖v‖ * ‖w‖)) := by
      ring
    rw [e]; exact this
  · have h2 := force_kernel_bound2 hs hz v w
    have hexp : ((d : ℝ) - s - 2) - d = -s - 2 := by ring
    rw [hexp, Real.norm_eq_abs]
    linarith [h2, show hlsg_c s * (s + 3) * (‖v‖ * ‖w‖) * ‖z‖ ^ (-s - 2) =
      hlsg_c s * (s + 3) * ‖z‖ ^ (-s - 2) * (‖v‖ * ‖w‖) by ring]

/-- bookkeeping for case (i): `1/p + (d-s-1)/d < 1 ↔ d < p (s+1)` (`p > 0`), i.e. `q > 1` iff `p(s+1) > d`. -/
lemma hlsg_q_gt_one_iff (hd : 1 ≤ d) {p s : ℝ} (hp : 0 < p) :
    1 / p + ((d : ℝ) - s - 1) / d < 1 ↔ (d : ℝ) < p * (s + 1) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have : 1 / p + ((d : ℝ) - s - 1) / d = 1 / p + 1 - (s + 1) / d := by field_simp; ring
  rw [this]
  constructor
  · intro h
    have h1 : 1 / p < (s + 1) / d := by linarith
    rw [div_lt_div_iff₀ hp hdR] at h1
    linarith
  · intro h
    have h1 : 1 / p < (s + 1) / d := by
      rw [div_lt_div_iff₀ hp hdR]; linarith
    linarith

/-- bookkeeping for the top term: `1/p + (d-s-2)/d < 1 ↔ d < p (s+2)` (`p > 0`). -/
lemma hlsg_q_gt_one_iff2 (hd : 1 ≤ d) {p s : ℝ} (hp : 0 < p) :
    1 / p + ((d : ℝ) - s - 2) / d < 1 ↔ (d : ℝ) < p * (s + 2) := by
  have := hlsg_q_gt_one_iff hd hp (s := s + 1)
  have e : (d : ℝ) - (s + 1) - 1 = (d : ℝ) - s - 2 := by ring
  rw [e] at this
  rw [this]; ring_nf

/-- **`riesz_force_Lp`, exponent form** (case (i), `p (s+1) > d`): for `0 ≤ s < d - 1` and
`p (s+1) > d` there is `q` with `1 < q < p`, `1/q = 1/p + (d-s-1)/d`, and the `L^q → L^p` bound for `∂_v g * ·`. -/
theorem riesz_force_Lp_of_p (hd : 1 ≤ d) {s p : ℝ} (hs : 0 ≤ s) (hsd : s + 1 < d)
    (hpd : (d : ℝ) < p * (s + 1)) :
    ∃ q : ℝ, 1 < q ∧ q < p ∧ 1 / q = 1 / p + ((d : ℝ) - s - 1) / d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (v : 𝔼) (u : 𝔼 → ℝ), AEStronglyMeasurable u volume →
        eLpNorm (HRS.Whole.convFun (fun z => fderiv ℝ (rieszKernel d s) z v) u)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * ‖v‖) * eLpNorm u (ENNReal.ofReal q) volume := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 < p := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  obtain ⟨q, hq1, hqp, hq, hrel⟩ := hlsg_exponents hd hp (σ := (d : ℝ) - s - 1) (by linarith)
    ((hlsg_q_gt_one_iff hd hp).2 hpd)
  exact ⟨q, hq1, hqp, hq, riesz_force_Lp hd hs hsd hq1 hqp hrel⟩

/-- **`riesz_force2_Lp`, exponent form** (`s + 2 < d`, `p (s+2) > d`). -/
theorem riesz_force2_Lp_of_p (hd : 1 ≤ d) {s p : ℝ} (hs : 0 ≤ s) (hsd : s + 2 < d)
    (hpd : (d : ℝ) < p * (s + 2)) :
    ∃ q : ℝ, 1 < q ∧ q < p ∧ 1 / q = 1 / p + ((d : ℝ) - s - 2) / d ∧
      ∃ C : ℝ, 0 < C ∧ ∀ (v w : 𝔼) (u : 𝔼 → ℝ), AEStronglyMeasurable u volume →
        eLpNorm (HRS.Whole.convFun
            (fun z => fderiv ℝ (fun y => fderiv ℝ (rieszKernel d s) y v) z w) u)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * (‖v‖ * ‖w‖)) * eLpNorm u (ENNReal.ofReal q) volume := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hp : 0 < p := by
    by_contra h
    rw [not_lt] at h
    nlinarith
  obtain ⟨q, hq1, hqp, hq, hrel⟩ := hlsg_exponents hd hp (σ := (d : ℝ) - s - 2) (by linarith)
    ((hlsg_q_gt_one_iff2 hd hp).2 hpd)
  exact ⟨q, hq1, hqp, hq, riesz_force2_Lp hd hs hsd hq1 hqp hrel⟩

/-- **`force_conv_enorm_le`**: pointwise convolution form `‖(∂_v g) * u (x)‖ₑ ≤ c_s |v| · I_{d-s-1}|u|(x)`. -/
theorem force_conv_enorm_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (v : 𝔼) (u : 𝔼 → ℝ) (x : 𝔼) :
    ‖HRS.Whole.convFun (fun z => fderiv ℝ (rieszKernel d s) z v) u x‖ₑ ≤
      ENNReal.ofReal (hlsg_c s * ‖v‖) * cmxHLS_I ((d : ℝ) - s - 1) (fun y => ‖u y‖ₑ) x := by
  refine hlsg_conv_enorm_le (K := fun z => fderiv ℝ (rieszKernel d s) z v) (c := hlsg_c s * ‖v‖)
    (σ := (d : ℝ) - s - 1) hd (mul_nonneg (hlsg_c_nonneg hs) (norm_nonneg v)) (fun z hz => ?_) u x
  have h2 := force_kernel_bound hs hz v
  have hexp : ((d : ℝ) - s - 1) - d = -s - 1 := by ring
  rw [hexp, Real.norm_eq_abs]
  linarith [h2, show hlsg_c s * ‖v‖ * ‖z‖ ^ (-s - 1) = hlsg_c s * ‖z‖ ^ (-s - 1) * ‖v‖ by ring]

end Force

end HRS.CZ.Hls
