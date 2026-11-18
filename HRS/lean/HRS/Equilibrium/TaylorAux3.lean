/-
# HRS.Equilibrium.TaylorAux3 — pointwise Taylor bounds and the truncated field (Lemma 4.7,
packet TAYLOR)

* `taylor_H_nonneg`, `taylor_H_le`, `taylor_H_lip`: `0 ≤ H(v)`, `H(v) ≤ e^K v²` for `v ≥ -K`, and
  `H(v) ≤ H(w) + (v - w)` for `v ≥ w` (source lines 4318-4319: `|H(v)| ≤ C v²`, `|H'| ≤ C`).
* `taylorFieldH`: the truncated field `v_{Y,H}` (`g_+` replaced by `g_H` in the empirical sum, the
  common term `-β h` retained; source line 4337).
* `taylor_field_moment`: the `L^{4q}(μ^{⊗n})` bound on `v_{Y,H}(y)`, uniformly in `y`
  (`R:eq:truncated-v-moment`, source line 4339), via the Bernstein inequality of `TaylorAux1`.
-/
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.TaylorAux1
import HRS.Equilibrium.TaylorAux2

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.TaylorAux

variable {d : ℕ}

/-! ### The Taylor remainder `H(v) = e^{-v} - 1 + v` -/

theorem taylor_H_nonneg (v : ℝ) : 0 ≤ taylorH v := by
  unfold taylorH
  have := Real.add_one_le_exp (-v)
  linarith

theorem taylor_H_le {K : ℝ} (hK : 0 ≤ K) {v : ℝ} (hv : -K ≤ v) :
    taylorH v ≤ Real.exp K * v ^ 2 := by
  unfold taylorH
  have hK1 : 1 ≤ Real.exp K := Real.one_le_exp hK
  by_cases h1 : |v| ≤ 1
  · have := Real.abs_exp_sub_one_sub_id_le (x := -v) (by rwa [abs_neg])
    have h2 : Real.exp (-v) - 1 + v ≤ v ^ 2 := by
      have := (abs_le.1 this).2
      nlinarith
    nlinarith [sq_nonneg v]
  · push Not at h1
    rcases le_or_gt 0 v with hv0 | hv0
    · -- v > 1
      have : 1 < v := by rwa [abs_of_nonneg hv0] at h1
      have h2 : Real.exp (-v) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
      have h3 : Real.exp (-v) - 1 + v ≤ v := by linarith
      nlinarith [sq_nonneg v]
    · -- v < -1
      have : 1 < -v := by rw [abs_of_neg hv0] at h1; exact h1
      have h2 : Real.exp (-v) ≤ Real.exp K := Real.exp_le_exp.2 (by linarith)
      have h3 : Real.exp (-v) - 1 + v ≤ Real.exp K := by linarith
      have h4 : Real.exp K * 1 ≤ Real.exp K * v ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos K).le
      linarith

theorem taylor_H_lip {v w : ℝ} (h : w ≤ v) : taylorH v ≤ taylorH w + (v - w) := by
  unfold taylorH
  have : Real.exp (-v) ≤ Real.exp (-w) := Real.exp_le_exp.2 (by linarith)
  linarith

/-! ### The truncated field -/

/-- The truncated conditional field `v_{Y,H}(y) = λ ∑_{j≠i} g_H(y - y_j) - β h(y)`. -/
def taylorFieldH (d : ℕ) (s c β : ℝ) (ρ : Torus d → ℝ) (N : ℕ) {n : ℕ} (i : Fin n) (H : ℝ)
    (Y : Config d n) (y : Torus d) : ℝ :=
  (β / N) * ∑ j ∈ Finset.univ.erase i, gTrunc d s c H (y - Y j) -
    β * convMeasure (gPlus d s c) (withDensityReal ρ) y

variable {s : ℝ}

theorem taylor_real_integral_le {μ : Measure (Torus d)} {F : Torus d → ℝ}
    (hF0 : ∀ a, 0 ≤ F a) (hFm : AEStronglyMeasurable F μ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ a, ENNReal.ofReal (F a) ∂μ ≤ ENNReal.ofReal B) :
    ∫ a, F a ∂μ ≤ B := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFm]
  exact ENNReal.toReal_le_of_le_ofReal hB h

section Kernel

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
  (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)

include hd hcrit

theorem taylor_measurable_gTrunc (H : ℝ) : Measurable (gTrunc d s c H) := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  have := PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)
  exact this.min measurable_const

include hc hρ in
/-- Row integrals of `g_+`: integrability and a uniform bound for `h = g_+ * μ`. -/
theorem taylor_h_bound :
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ y : Torus d,
      Integrable (fun a => gPlus d s c (y - a)) (withDensityReal ρ) ∧
      0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Ch := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hgm := PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)
  set Im : ℝ≥0∞ := ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (gPlus d s c z) with hIm
  have hImfin : Im ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (taylor_lintegral_gPlus_lt_top hd hcrit c hc)
  refine ⟨Im.toReal, ENNReal.toReal_nonneg, fun y => ?_⟩
  have hm : Measurable fun a => gPlus d s c (y - a) := hgm.comp (measurable_const.sub measurable_id)
  have hle : ∫⁻ a, ENNReal.ofReal (gPlus d s c (y - a)) ∂(withDensityReal ρ) ≤ Im :=
    KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (gPlus d s c z)) y
  have hnn : 0 ≤ᵐ[withDensityReal ρ] fun a => gPlus d s c (y - a) :=
    Filter.Eventually.of_forall fun a => hc _
  refine ⟨?_, integral_nonneg fun a => hc _, ?_⟩
  · exact (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hnn).1
      (ne_top_of_le_ne_top hImfin hle)
  · exact taylor_real_integral_le (fun a => hc _) hm.aestronglyMeasurable ENNReal.toReal_nonneg
      (hle.trans (ENNReal.ofReal_toReal hImfin).symm.le)

include hc hρ in
/-- `0 ≤ ∫ (g_+ - g_H)(y - a) dμ(a) ≤ C/H`, and `∫ g_H(y-a)² dμ ≤ C log H`. -/
theorem taylor_trunc_bounds (β : ℝ) (hβ : 0 < β) :
    ∃ C2 : ℝ, 0 ≤ C2 ∧ ∀ H : ℝ, 2 ≤ H → ∀ y : Torus d,
      ∫ a, taylorG d s c H (y - a) ∂(withDensityReal ρ) ≤ C2 / H ∧
      ∫ a, gTrunc d s c H (y - a) ^ 2 ∂(withDensityReal ρ) ≤ C2 * Real.log H := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨C0, hC0⟩ := critical_integrals hd hcrit β hβ ρ hρ c hc |>.imp fun _ h => h.1
  refine ⟨max C0 0, le_max_right _ _, fun H hH y => ⟨?_, ?_⟩⟩
  · have hH0 : 0 < H := by linarith
    refine taylor_real_integral_le (fun a => taylorG_nonneg c H (by linarith) hc _)
      ((measurable_taylorG hd hs0 hsd c H).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (div_nonneg (le_max_right _ _) hH0.le) ?_
    refine (hC0 H hH y).2.trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (le_max_left _ _) hH0.le
  · have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
    have hm : Measurable fun a => gTrunc d s c H (y - a) ^ 2 :=
      ((taylor_measurable_gTrunc hd hcrit c H).comp (measurable_const.sub measurable_id)).pow_const 2
    refine taylor_real_integral_le (fun a => sq_nonneg _) hm.aestronglyMeasurable
      (mul_nonneg (le_max_right _ _) hlog) ?_
    refine (hC0 H hH y).1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hlog

end Kernel

theorem taylor_pow_sum (a e : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    (a + e) ^ (4 * q) ≤ 2 ^ (4 * q - 1) * (a ^ (4 * q) + e ^ (4 * q)) := by
  have hev : Even (4 * q) := ⟨2 * q, by ring⟩
  have h1 : (a + e) ^ (4 * q) = |a + e| ^ (4 * q) := (hev.pow_abs _).symm
  have h2 : |a + e| ^ (4 * q) ≤ (|a| + |e|) ^ (4 * q) :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_add_le _ _) _
  have h3 := add_pow_le (abs_nonneg a) (abs_nonneg e) (4 * q)
  rw [hev.pow_abs, hev.pow_abs] at h3
  rw [h1]; exact h2.trans h3

section FieldMoment

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc in
/-- The `L^{4q}(μ^{⊗n})` bound on the truncated conditional field, uniformly in `y`
(`R:eq:truncated-v-moment`, source line 4339). -/
theorem taylor_field_moment (q : ℕ) (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ H : ℝ, 2 ≤ H → ∀ i : Fin (N - 1), ∀ y : Torus d,
      ∫ Y, (taylorFieldH d s c β ρ N i H Y y) ^ (4 * q)
          ∂(Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) ≤
        C * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) ^ (2 * q) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨Ch, hCh0, hCh⟩ := taylor_h_bound hd hcrit c hc ρ hρ
  obtain ⟨C2, hC20, hC2⟩ := taylor_trunc_bounds hd hcrit c hc ρ hρ β hβ
  set c1 : ℝ := β ^ 2 * (C2 + 1) with hc1
  set c2 : ℝ := 8 * β ^ 2 * (C2 ^ 2 + Ch ^ 2) with hc2
  have hc10 : 0 ≤ c1 := by positivity
  have hc20 : 0 ≤ c2 := by positivity
  refine ⟨2 ^ (4 * q - 1) * (taylor_kb (2 * q) * c1 ^ (2 * q) + c2 ^ (2 * q)), by
    have := taylor_kb_one_le (2 * q); positivity, fun N hN H hH i y => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hH0 : 0 < H := by linarith
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  set μ : Measure (Torus d) := withDensityReal ρ with hμdef
  set Pm : Measure (Config d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => μ with hPm
  set J : Finset (Fin (N - 1)) := Finset.univ.erase i with hJ
  have hJcard : (J.card : ℝ) = N - 2 := by
    rw [hJ, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    have : 2 ≤ N := hN
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
  have hJle : (J.card : ℝ) ≤ N := by rw [hJcard]; linarith
  have hJ0 : (0 : ℝ) ≤ J.card := Nat.cast_nonneg _
  -- the centered summand
  set mH : ℝ := ∫ a, gTrunc d s c H (y - a) ∂μ with hmH
  set f : Torus d → ℝ := fun a => gTrunc d s c H (y - a) - mH with hf
  have hgm : Measurable fun a => gTrunc d s c H (y - a) :=
    (taylor_measurable_gTrunc hd hcrit c H).comp (measurable_const.sub measurable_id)
  have hg0 : ∀ a, 0 ≤ gTrunc d s c H (y - a) := fun a => le_min (hc _) (by linarith)
  have hgH : ∀ a, gTrunc d s c H (y - a) ≤ H := fun a => min_le_right _ _
  have hgint : Integrable (fun a => gTrunc d s c H (y - a)) μ :=
    taylor_integrable_of_bdd hgm (B := H) fun a => by rw [abs_of_nonneg (hg0 a)]; exact hgH a
  have hmH0 : 0 ≤ mH := integral_nonneg hg0
  have hmHH : mH ≤ H := by
    calc mH ≤ ∫ a, H ∂μ := integral_mono hgint (integrable_const _) hgH
      _ = H := by simp
  have hfm : Measurable f := hgm.sub_const _
  have hfb : ∀ a, |f a| ≤ H := fun a => by
    rw [abs_le]; constructor <;> simp only [hf] <;> linarith [hg0 a, hgH a]
  have hf0 : ∫ a, f a ∂μ = 0 := by
    simp only [hf]
    rw [integral_sub hgint (integrable_const _)]; simp [hmH]
  have hfv : ∫ a, f a ^ 2 ∂μ ≤ C2 * Real.log H := by
    have h1 : ∫ a, f a ^ 2 ∂μ = ∫ a, gTrunc d s c H (y - a) ^ 2 ∂μ - mH ^ 2 := by
      have e : ∀ a, f a ^ 2 = gTrunc d s c H (y - a) ^ 2 - 2 * mH * gTrunc d s c H (y - a) + mH ^ 2 :=
        fun a => by simp only [hf]; ring
      have hsq : Integrable (fun a => gTrunc d s c H (y - a) ^ 2) μ :=
        taylor_integrable_of_bdd (hgm.pow_const 2) (B := H ^ 2) fun a => by
          rw [abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (hg0 a) (hgH a) 2
      have hlin : Integrable (fun a => 2 * mH * gTrunc d s c H (y - a)) μ := hgint.const_mul _
      have hsub : Integrable (fun a => gTrunc d s c H (y - a) ^ 2 -
          2 * mH * gTrunc d s c H (y - a)) μ := hsq.sub hlin
      simp_rw [e]
      rw [integral_add hsub (integrable_const _), integral_sub hsq hlin, integral_const_mul]
      simp [hmH]; ring
    rw [h1]
    exact (sub_le_self _ (sq_nonneg _)).trans (hC2 H hH y).2
  -- Bernstein
  have hbern := taylor_bernstein_pi μ (N - 1) f hfm (M := H) (σ2 := C2 * Real.log H) hH0
    (mul_nonneg hC20 hlog) hfb hf0 hfv (2 * q) J
  -- the field
  set S : Config d (N - 1) → ℝ := fun Y => ∑ j ∈ J, f (Y j) with hS
  set lam : ℝ := β / N with hlam
  set hy : ℝ := convMeasure (gPlus d s c) μ y with hhy
  set e : ℝ := lam * J.card * mH - β * hy with he
  have hfield : ∀ Y, taylorFieldH d s c β ρ N i H Y y = lam * S Y + e := by
    intro Y
    simp only [taylorFieldH, hS, hf, he]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← hJ]
    ring
  -- the deterministic part `e`
  have hhy_int : Integrable (fun a => gPlus d s c (y - a)) μ := (hCh y).1
  have hdH : hy - mH = ∫ a, taylorG d s c H (y - a) ∂μ := by
    simp only [hhy, hmH, convMeasure, taylorG]
    rw [integral_sub hhy_int hgint]
  have hdH0 : 0 ≤ hy - mH := by
    rw [hdH]; exact integral_nonneg fun a => taylorG_nonneg c H (by linarith) hc _
  have hdH1 : hy - mH ≤ C2 / H := by rw [hdH]; exact (hC2 H hH y).1
  have hhyCh : hy ≤ Ch := (hCh y).2.2
  have he_eq : e = -(β * (hy - mH)) - (2 * β / N) * mH := by
    simp only [he, hlam]
    have : (J.card : ℝ) = N - 2 := hJcard
    rw [this]; field_simp; ring
  have hebound : e ^ 2 ≤ c2 * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2) := by
    have h1 : |e| ≤ β * (C2 / H) + 2 * β / N * Ch := by
      rw [he_eq, abs_le]; constructor
      · have : β * (hy - mH) ≤ β * (C2 / H) := mul_le_mul_of_nonneg_left hdH1 hβ.le
        have : 2 * β / N * mH ≤ 2 * β / N * Ch :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have : 0 ≤ 2 * β / N * mH := by positivity
        have : 0 ≤ β * (hy - mH) := mul_nonneg hβ.le hdH0
        linarith
      · have : 0 ≤ β * (hy - mH) := mul_nonneg hβ.le hdH0
        have : 0 ≤ 2 * β / N * mH := by positivity
        have : 0 ≤ β * (C2 / H) := by positivity
        have : 0 ≤ 2 * β / N * Ch := by positivity
        linarith
    have h2 : e ^ 2 ≤ (β * (C2 / H) + 2 * β / N * Ch) ^ 2 := by
      rw [← sq_abs e]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    refine h2.trans ?_
    have h3 : (β * (C2 / H) + 2 * β / N * Ch) ^ 2 ≤ 2 * (β * (C2 / H)) ^ 2 + 2 * (2 * β / N * Ch) ^ 2 := by
      nlinarith [sq_nonneg (β * (C2 / H) - 2 * β / N * Ch)]
    refine h3.trans ?_
    have e1 : 2 * (β * (C2 / H)) ^ 2 = 2 * β ^ 2 * C2 ^ 2 * (1 / H ^ 2) := by field_simp
    have e2 : 2 * (2 * β / N * Ch) ^ 2 = 8 * β ^ 2 * Ch ^ 2 * (1 / (N : ℝ) ^ 2) := by field_simp; ring
    rw [e1, e2, hc2]
    have a1 : 0 ≤ 1 / H ^ 2 := by positivity
    have a2 : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
    have b1 : 0 ≤ β ^ 2 * C2 ^ 2 := by positivity
    have b2 : 0 ≤ β ^ 2 * Ch ^ 2 := by positivity
    have key : 8 * β ^ 2 * (C2 ^ 2 + Ch ^ 2) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2) -
        (2 * β ^ 2 * C2 ^ 2 * (1 / H ^ 2) + 8 * β ^ 2 * Ch ^ 2 * (1 / (N : ℝ) ^ 2)) =
        6 * (β ^ 2 * C2 ^ 2) * (1 / H ^ 2) + 8 * (β ^ 2 * C2 ^ 2) * (1 / (N : ℝ) ^ 2) +
          8 * (β ^ 2 * Ch ^ 2) * (1 / H ^ 2) := by ring
    have hk0 : 0 ≤ 6 * (β ^ 2 * C2 ^ 2) * (1 / H ^ 2) + 8 * (β ^ 2 * C2 ^ 2) * (1 / (N : ℝ) ^ 2) +
          8 * (β ^ 2 * Ch ^ 2) * (1 / H ^ 2) := by positivity
    linarith
  -- the random part
  have hlam2 : lam ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2) ≤
      c1 * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) := by
    have hl2 : lam ^ 2 = β ^ 2 / (N : ℝ) ^ 2 := by rw [hlam]; ring
    rw [hl2]
    have hCl : 0 ≤ C2 * Real.log H := mul_nonneg hC20 hlog
    have h1 : β ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H)) ≤
        β ^ 2 / (N : ℝ) ^ 2 * (N * (C2 * Real.log H)) := by gcongr
    have h2 : β ^ 2 / (N : ℝ) ^ 2 * (N * (C2 * Real.log H)) + β ^ 2 / (N : ℝ) ^ 2 * H ^ 2 =
        β ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) := by field_simp
    have a1 : 0 ≤ Real.log H / N := by positivity
    have a2 : 0 ≤ H ^ 2 / (N : ℝ) ^ 2 := by positivity
    have a3 : 0 ≤ 1 / H ^ 2 := by positivity
    have a4 : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
    calc β ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2)
        = β ^ 2 / (N : ℝ) ^ 2 * (J.card * (C2 * Real.log H)) + β ^ 2 / (N : ℝ) ^ 2 * H ^ 2 := by ring
      _ ≤ β ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) := by linarith
      _ ≤ _ := by
        rw [hc1]
        have key : β ^ 2 * (C2 + 1) * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2) -
            β ^ 2 * (C2 * (Real.log H / N) + H ^ 2 / (N : ℝ) ^ 2) =
            β ^ 2 * (Real.log H / N + C2 * (H ^ 2 / (N : ℝ) ^ 2) +
              (C2 + 1) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) := by ring
        have hk0 : 0 ≤ β ^ 2 * (Real.log H / N + C2 * (H ^ 2 / (N : ℝ) ^ 2) +
              (C2 + 1) * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) := by positivity
        linarith
  -- assemble
  set Θ : ℝ := Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2 with hΘ
  have hΘ0 : 0 ≤ Θ := by positivity
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ => hfm.comp (measurable_pi_apply j)
  have hSb : ∀ Y, |S Y| ≤ J.card * H := fun Y => by
    simp only [hS]
    calc |∑ j ∈ J, f (Y j)| ≤ ∑ j ∈ J, |f (Y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ J, H := Finset.sum_le_sum fun j _ => hfb _
      _ = _ := by simp
  have hSint : Integrable (fun Y => S Y ^ (4 * q)) Pm :=
    taylor_integrable_of_bdd (hSm.pow_const _) (B := (J.card * H) ^ (4 * q)) fun Y => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hSb Y) _
  have hev : Even (4 * q) := ⟨2 * q, by ring⟩
  have hvm : Measurable fun Y : Config d (N - 1) => (taylorFieldH d s c β ρ N i H Y y) := by
    simp_rw [hfield]
    exact (hSm.const_mul _).add_const _
  have hRHS : Integrable (fun Y => 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q))) Pm := by
    refine Integrable.const_mul (Integrable.add ?_ (integrable_const _)) _
    simp_rw [mul_pow]
    exact hSint.const_mul _
  have hS4 : ∫ Y, S Y ^ (4 * q) ∂Pm ≤ taylor_kb (2 * q) * (J.card * (C2 * Real.log H) + H ^ 2) ^ (2 * q) := by
    have : 4 * q = 2 * (2 * q) := by ring
    rw [this]; exact hbern
  have he4 : e ^ (4 * q) ≤ (c2 * (1 / H ^ 2 + 1 / (N : ℝ) ^ 2)) ^ (2 * q) := by
    have : e ^ (4 * q) = (e ^ 2) ^ (2 * q) := by rw [← pow_mul]; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (sq_nonneg _) hebound _
  have hstep1 : ∫ Y, (taylorFieldH d s c β ρ N i H Y y) ^ (4 * q) ∂Pm ≤
      ∫ Y, 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q)) ∂Pm := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun Y => hev.pow_nonneg _) hRHS
      (Filter.Eventually.of_forall fun Y => ?_)
    simp only [hfield]
    exact taylor_pow_sum _ _ q hq
  have hstep2 : ∫ Y, 2 ^ (4 * q - 1) * ((lam * S Y) ^ (4 * q) + e ^ (4 * q)) ∂Pm =
      2 ^ (4 * q - 1) * (lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm + e ^ (4 * q)) := by
    rw [integral_const_mul]
    congr 1
    simp_rw [mul_pow]
    rw [integral_add (hSint.const_mul _) (integrable_const _), integral_const_mul]
    simp
  have hk := taylor_kb_one_le (2 * q)
  have hlamq : lam ^ (4 * q) * (taylor_kb (2 * q) * (J.card * (C2 * Real.log H) + H ^ 2) ^ (2 * q)) =
      taylor_kb (2 * q) * (lam ^ 2 * (J.card * (C2 * Real.log H) + H ^ 2)) ^ (2 * q) := by
    rw [mul_pow, ← pow_mul]; ring_nf
  have hstep3 : 2 ^ (4 * q - 1) * (lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm + e ^ (4 * q)) ≤
      2 ^ (4 * q - 1) * (taylor_kb (2 * q) * (c1 * Θ) ^ (2 * q) + (c2 * Θ) ^ (2 * q)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hlam4 : 0 ≤ lam ^ (4 * q) := by positivity
    have h1 : lam ^ (4 * q) * ∫ Y, S Y ^ (4 * q) ∂Pm ≤ taylor_kb (2 * q) * (c1 * Θ) ^ (2 * q) := by
      refine (mul_le_mul_of_nonneg_left hS4 hlam4).trans ?_
      rw [hlamq]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hlam2 _) (by linarith)
    have h2 : e ^ (4 * q) ≤ (c2 * Θ) ^ (2 * q) := by
      refine he4.trans (pow_le_pow_left₀ (by positivity) ?_ _)
      refine mul_le_mul_of_nonneg_left ?_ hc20
      have : 0 ≤ Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 := by positivity
      rw [hΘ]; linarith
    linarith
  refine hstep1.trans (hstep2.le.trans (hstep3.trans (le_of_eq ?_)))
  rw [mul_pow, mul_pow]
  ring

end FieldMoment

end HRS.TaylorAux
