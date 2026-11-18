import Mathlib
import HRS.Whole.AppendixALemmas
import HRS.MH.CoercLowerDefs
import HRS.MH.CoercLowerFinal
import HRS.MH.CoercTestSpecDefs

noncomputable section

open MeasureTheory
open scoped BigOperators FourierTransform

namespace HRS.MH.CoercTest

open HRS.MH.CoercLower

variable {d N : ℕ}

open scoped ContDiff in
/-- The `L²` Fourier transform of a real `L¹ ∩ L²` function is its pointwise Fourier integral. -/
theorem p_wt1_fourierL2_eq {d : ℕ} (u : Euc d → ℝ) (hu1 : Integrable u) (hu2 : MemLp u 2 volume) :
    HRS.PDE.ToolboxRd.fourierL2 u =ᵐ[volume] 𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) := by
  set G : Euc d → ℂ := 𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ)) with hGdef
  have hGc : Continuous G := by
    have hi : Integrable (fun x : Euc d => ((u x : ℝ) : ℂ)) := hu1.ofReal
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi
  have hFloc : LocallyIntegrable (HRS.PDE.ToolboxRd.fourierL2 u) volume :=
    (HRS.PDE.ToolboxRd.FourierAux.memLp_fourierL2 hu2).locallyIntegrable (by norm_num)
  have hGloc : LocallyIntegrable G volume := hGc.locallyIntegrable
  have hFl := HRS.PDE.ToolboxRd.FourierAux.fourierL2_eq hu2
  have key : ∀ g : Euc d → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∫ x, g x • (HRS.PDE.ToolboxRd.fourierL2 u x - G x) = 0 := by
    intro g hg hsupp
    have hgC : ContDiff ℝ ∞ (fun x => ((g x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    have hsC : HasCompactSupport (fun x => ((g x : ℝ) : ℂ)) :=
      hsupp.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
    set φ : SchwartzMap (Euc d) ℂ := hsC.toSchwartzMap hgC with hφdef
    have hφ : ⇑φ = fun x => ((g x : ℝ) : ℂ) := rfl
    set Fl := HRS.PDE.ToolboxRd.FourierAux.ofRealLp hu2 with hFldef
    -- the `L²` side: `∫ φ · 𝓕u = ∫ (𝓕φ) · u`
    have hL2side : ∫ x, φ x • (HRS.PDE.ToolboxRd.fourierL2 u x) =
        ∫ x, (𝓕 φ) x • ((u x : ℝ) : ℂ) := by
      have h1 : ∫ x, φ x • (HRS.PDE.ToolboxRd.fourierL2 u x) =
          ∫ x, φ x • ((HRS.PDE.ToolboxRd.FourierAux.FT d Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [congrFun hFl x]
      have h2 : (𝓕 (MeasureTheory.Lp.toTemperedDistribution Fl)) φ =
          ∫ x, φ x • ((𝓕 Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := by
        rw [MeasureTheory.Lp.fourier_toTemperedDistribution_eq,
          MeasureTheory.Lp.toTemperedDistribution_apply]
      have h3 : (𝓕 (MeasureTheory.Lp.toTemperedDistribution Fl)) φ =
          (MeasureTheory.Lp.toTemperedDistribution Fl) (𝓕 φ) := rfl
      have h4 : (MeasureTheory.Lp.toTemperedDistribution Fl) (𝓕 φ) = ∫ x, (𝓕 φ) x • Fl x :=
        MeasureTheory.Lp.toTemperedDistribution_apply _ _
      have h5 : ∫ x, φ x • ((HRS.PDE.ToolboxRd.FourierAux.FT d Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x =
          ∫ x, φ x • ((𝓕 Fl : MeasureTheory.Lp (α := Euc d) ℂ 2 volume) : Euc d → ℂ) x := rfl
      rw [h1, h5, ← h2, h3, h4]
      refine integral_congr_ae ?_
      filter_upwards [HRS.PDE.ToolboxRd.FourierAux.ofRealLp_coe hu2] with x hx
      rw [hx]
    -- the `L¹` side: `∫ φ · 𝓕u = ∫ u · 𝓕φ`
    have hL1side : ∫ x, φ x • G x = ∫ x, ((u x : ℝ) : ℂ) • (𝓕 φ) x := by
      have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
        (L := innerₗ (Euc d)) (f := fun x : Euc d => ((u x : ℝ) : ℂ)) (g := φ)
        Real.continuous_fourierChar continuous_inner hu1.ofReal φ.integrable
      have hflip : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
        ext x y
        simp
      rw [hflip] at this
      have hc : ∫ x, φ x • G x = ∫ x, G x * φ x :=
        integral_congr_ae (ae_of_all _ fun x => by simp only [smul_eq_mul]; ring)
      rw [hc]
      simp only [smul_eq_mul]
      exact this
    have hintF : Integrable (fun x => φ x • HRS.PDE.ToolboxRd.fourierL2 u x) := by
      have hF2 := HRS.PDE.ToolboxRd.FourierAux.memLp_fourierL2 hu2
      have hφ2 : MemLp (fun x => φ x) 2 volume := φ.memLp 2 volume
      have := hφ2.integrable_mul hF2
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply, smul_eq_mul]
    have hφs : HasCompactSupport (fun x => φ x) := by
      show HasCompactSupport (⇑φ)
      rw [hφ]
      exact hsC
    have hintG : Integrable (fun x => φ x • G x) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact φ.continuous.smul hGc
      · exact hφs.smul_right
    have hsplit : ∫ x, g x • (HRS.PDE.ToolboxRd.fourierL2 u x - G x) =
        (∫ x, φ x • HRS.PDE.ToolboxRd.fourierL2 u x) - ∫ x, φ x • G x := by
      rw [← integral_sub hintF hintG]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hφ, Complex.real_smul, smul_eq_mul, mul_sub]
    have hc2 : ∫ x, ((u x : ℝ) : ℂ) * (𝓕 φ) x = ∫ x, (𝓕 φ) x * ((u x : ℝ) : ℂ) :=
      integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    rw [hsplit, hL2side, hL1side]
    simp only [smul_eq_mul]
    rw [hc2, sub_self]
  have hzero := ae_eq_zero_of_integral_contDiff_smul_eq_zero (hFloc.sub hGloc) key
  filter_upwards [hzero] with x hx
  simpa [sub_eq_zero] using hx

/-- [W1a] `ν̂` is continuous (`ρ ∈ L¹`, atoms are characters).  Route: `VectorFourier.fourierIntegral_continuous`
for `𝓕ρ`, `continuous_exp`/`Continuous.inner` for the finite sum. -/
theorem continuous_nuHat {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (X : HRS.Whole.EucConfig d N) :
    Continuous (nuHat X ρ) := by
  have hρi : Integrable ρ := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this
    exact zero_ne_one this
  have h1 : Continuous (fun ξ : Euc d => 𝓕 (fun x : Euc d => ((ρ x : ℝ) : ℂ)) ξ) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hρi.ofReal
  unfold nuHat
  refine Continuous.sub (continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)) h1
  fun_prop

lemma p_wt1_fourier_gauss {u : ℝ} (hu : 0 < u) (ξ : Euc d) :
    𝓕 (fun x : Euc d => ((gaussK u x : ℝ) : ℂ)) ξ =
      (((Real.pi / u) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / u) : ℝ) : ℂ) := by
  have hb : (0:ℝ) < (u:ℂ).re := by simpa using hu
  have := fourier_gaussian_innerProductSpace (V := Euc d) hb ξ
  have e : (fun x : Euc d => ((gaussK u x : ℝ) : ℂ)) =
      fun v : Euc d => Complex.exp (-(u:ℂ) * ‖v‖ ^ 2) := by
    ext v; unfold gaussK; push_cast; rfl
  rw [e, this]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  push_cast
  rw [Complex.ofReal_cpow (by positivity)]
  push_cast
  congr 1

lemma p_wt1_fourier_translate (b : ℝ) (x ξ : Euc d) :
    𝓕 (fun z : Euc d => ((gaussK b (x - z) : ℝ) : ℂ)) ξ =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ξ : ℝ) : ℂ))) *
        𝓕 (fun z : Euc d => ((gaussK b z : ℝ) : ℂ)) ξ := by
  have heven : ∀ z : Euc d, gaussK b (x - z) = gaussK b (z - x) := fun z => by
    unfold gaussK; rw [norm_sub_rev]
  simp_rw [heven]
  rw [Real.fourier_eq, Real.fourier_eq]
  simp only [Circle.smul_def]
  have h1 := integral_add_right_eq_self (μ := (volume : Measure (Euc d)))
    (fun z : Euc d => (𝐞 (-inner ℝ z ξ) : ℂ) • ((gaussK b (z - x) : ℝ) : ℂ)) x
  rw [← h1]
  simp only [add_sub_cancel_right]
  have h2 : ∀ w : Euc d, (𝐞 (-inner ℝ (w + x) ξ) : ℂ) • ((gaussK b w : ℝ) : ℂ) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ξ : ℝ) : ℂ))) *
        ((𝐞 (-inner ℝ w ξ) : ℂ) • ((gaussK b w : ℝ) : ℂ)) := by
    intro w
    have hk : (𝐞 (-inner ℝ x ξ) : ℂ) =
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ξ : ℝ) : ℂ))) := by
      rw [Real.fourierChar_apply]
      push_cast
      ring_nf
    rw [inner_add_left, neg_add, AddChar.map_add_eq_mul]
    simp only [smul_eq_mul, Circle.coe_mul]
    rw [hk]
    ring
  simp_rw [h2]
  rw [integral_const_mul]

lemma p_wt1_fourier_lin {ι : Type*} (s : Finset ι) (c : ℂ) (a : ι → Euc d → ℂ) (b : Euc d → ℂ)
    (ha : ∀ i ∈ s, Integrable (a i)) (hb : Integrable b) (ξ : Euc d) :
    𝓕 (fun z => c * ∑ i ∈ s, a i z - b z) ξ = c * ∑ i ∈ s, 𝓕 (a i) ξ - 𝓕 b ξ := by
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  have hai : ∀ i ∈ s, Integrable (fun z : Euc d => (𝐞 (-inner ℝ z ξ) : ℂ) * a i z) := fun i hi => by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) ξ).2 (ha i hi)
    simpa [Circle.smul_def] using this
  have hbi : Integrable (fun z : Euc d => (𝐞 (-inner ℝ z ξ) : ℂ) * b z) := by
    have := (Real.fourierIntegral_convergent_iff (μ := volume) ξ).2 hb
    simpa [Circle.smul_def] using this
  have h1 : ∀ z : Euc d, (𝐞 (-inner ℝ z ξ) : ℂ) * (c * ∑ i ∈ s, a i z - b z) =
      c * ∑ i ∈ s, ((𝐞 (-inner ℝ z ξ) : ℂ) * a i z) - (𝐞 (-inner ℝ z ξ) : ℂ) * b z := by
    intro z
    simp only [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  simp_rw [h1]
  rw [integral_sub ((integrable_finsetSum s hai).const_mul c) hbi, integral_const_mul,
    integral_finsetSum s hai]

lemma p_wt1_fourier_conv {ρ : Euc d → ℝ} (hρi : Integrable ρ) {b : ℝ} (hb : 0 < b) (ξ : Euc d) :
    𝓕 (fun z : Euc d => ((∫ y, gaussK b (y - z) * ρ y : ℝ) : ℂ)) ξ =
      𝓕 (fun x : Euc d => ((ρ x : ℝ) : ℂ)) ξ * 𝓕 (fun z : Euc d => ((gaussK b z : ℝ) : ℂ)) ξ := by
  have hG : Integrable (fun z : Euc d => ((gaussK b z : ℝ) : ℂ)) :=
    (gaussK_basic (d := d) hb).2.2.1.ofReal
  have := Real.fourier_mul_convolution_eq (hρi.ofReal (𝕜 := ℂ)) hG ξ
  have hfun : (fun z : Euc d => ((∫ y, gaussK b (y - z) * ρ y : ℝ) : ℂ)) =
      convolution (fun x : Euc d => ((ρ x : ℝ) : ℂ)) (fun z : Euc d => ((gaussK b z : ℝ) : ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume := by
    ext z
    rw [convolution_def]
    simp only [ContinuousLinearMap.mul_apply']
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [gaussK, norm_sub_rev z y]
    push_cast
    ring
  rw [hfun]
  exact this


lemma p_wt1_integrable_rho {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  exact zero_ne_one this

lemma p_wt1_U_integrable {b : ℝ} (hb : 0 < b) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) :
    Integrable (fun z : Euc d => ∫ y, gaussK b (y - z) * ρ y) := by
  have hG : Integrable (gaussK b : Euc d → ℝ) := (gaussK_basic (d := d) hb).2.2.1
  have h := (p_wt1_integrable_rho hρ).integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hG
  refine h.congr (Filter.Eventually.of_forall fun z => ?_)
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [gaussK, norm_sub_rev z y]
  ring

lemma p_wt1_U_bounds {b : ℝ} (hb : 0 < b) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (z : Euc d) :
    0 ≤ ∫ y, gaussK b (y - z) * ρ y ∧ ∫ y, gaussK b (y - z) * ρ y ≤ 1 := by
  have hρi := p_wt1_integrable_rho hρ
  have hle : ∀ w : Euc d, gaussK b w ≤ 1 := fun w => ((gaussK_basic (d := d) hb).2.1 w).2
  have hpos : ∀ w : Euc d, 0 < gaussK b w := fun w => ((gaussK_basic (d := d) hb).2.1 w).1
  refine ⟨integral_nonneg fun y => mul_nonneg (hpos _).le (hρ.nonneg y), ?_⟩
  have hi : Integrable (fun y => gaussK b (y - z) * ρ y) := by
    refine hρi.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (by unfold gaussK; have := hρ.measurable; fun_prop :
        Measurable (fun y => gaussK b (y - z) * ρ y)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hpos _).le (hρ.nonneg y))]
      have := hle (y - z); have := hρ.nonneg y
      nlinarith
  calc ∫ y, gaussK b (y - z) * ρ y ≤ ∫ y, ρ y := integral_mono hi hρi fun y => by
        have := hle (y - z); have := hρ.nonneg y
        show gaussK b (y - z) * ρ y ≤ ρ y
        nlinarith
    _ = 1 := hρ.integral_one

lemma p_wt1_gaussU_integrable {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (X : HRS.Whole.EucConfig d N) :
    Integrable (gaussU t X ρ) := by
  have hb : 0 < 2 * t := by linarith
  have hG : Integrable (gaussK (2 * t) : Euc d → ℝ) := (gaussK_basic (d := d) hb).2.2.1
  have h1 : Integrable (fun z : Euc d => (1 / (N : ℝ)) * ∑ i, gaussK (2 * t) (X i - z)) :=
    (integrable_finsetSum _ fun i _ => hG.comp_sub_left (X i)).const_mul _
  exact h1.sub (p_wt1_U_integrable hb hρ)

lemma p_wt1_gaussU_abs_le {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (X : HRS.Whole.EucConfig d N) (z : Euc d) :
    |gaussU t X ρ z| ≤ 1 := by
  have hb : 0 < 2 * t := by linarith
  have hle : ∀ w : Euc d, gaussK (2 * t) w ≤ 1 := fun w => ((gaussK_basic (d := d) hb).2.1 w).2
  have hpos : ∀ w : Euc d, 0 < gaussK (2 * t) w := fun w => ((gaussK_basic (d := d) hb).2.1 w).1
  have hU := p_wt1_U_bounds hb hρ z
  have hS0 : 0 ≤ (1 / (N : ℝ)) * ∑ i, gaussK (2 * t) (X i - z) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => (hpos _).le)
  have hS1 : (1 / (N : ℝ)) * ∑ i, gaussK (2 * t) (X i - z) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · subst h0; simp
    · have hNp : (0 : ℝ) < N := by exact_mod_cast hN
      have : ∑ i, gaussK (2 * t) (X i - z) ≤ (N : ℝ) := by
        calc ∑ i, gaussK (2 * t) (X i - z) ≤ ∑ _i : Fin N, (1 : ℝ) :=
              Finset.sum_le_sum fun i _ => hle _
          _ = N := by simp
      rw [one_div, inv_mul_le_iff₀ hNp]
      linarith
  unfold gaussU
  rw [abs_le]
  constructor <;> linarith [hU.1, hU.2]

lemma p_wt1_gaussU_memLp {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (X : HRS.Whole.EucConfig d N) :
    MemLp (gaussU t X ρ) 2 volume := by
  have hi := p_wt1_gaussU_integrable ht hρ X
  refine (memLp_two_iff_integrable_sq hi.aestronglyMeasurable).2 ?_
  refine hi.norm.mono' (hi.aestronglyMeasurable.pow 2) (Filter.Eventually.of_forall fun z => ?_)
  have h := p_wt1_gaussU_abs_le ht hρ X z
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have := abs_nonneg (gaussU t X ρ z)
  nlinarith


/-- [W1b] `gaussU t` is in `L¹ ∩ L²` and its `L²`-Fourier transform is `(π/2t)^{d/2} e^{-π²‖ξ‖²/(2t)} ν̂(ξ)` a.e.
(`gaussU t = N⁻¹ ∑ G(·-x_i) - G * ρ` with `G = e^{-2t‖·‖²}` even, `Ĝ = (π/2t)^{d/2} e^{-π²‖ξ‖²/(2t)}`).
Route: `cla3_U_integrable`/boundedness for `L¹ ∩ L²`; `HRS.Commutator.Whole.energyAux_fourierL2_eq` (or a copy) to
pass from `fourierL2` to `𝓕`; translation formula and the convolution theorem (Fubini) for `𝓕`; `fourier_gauss`
(`HRS/Commutator/Whole/PositiveAux.lean:132`, copy it: heavy import). -/
theorem fourierL2_gaussU (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (X : HRS.Whole.EucConfig d N) :
    (Integrable (gaussU t X ρ) ∧ MemLp (gaussU t X ρ) 2 volume) ∧
      ∀ᵐ ξ : Euc d ∂volume, HRS.PDE.ToolboxRd.fourierL2 (gaussU t X ρ) ξ =
        (((Real.pi / (2 * t)) ^ ((d : ℝ) / 2) * Real.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / (2 * t)) : ℝ) : ℂ) *
          nuHat X ρ ξ := by
  have hb : 0 < 2 * t := by linarith
  have hi := p_wt1_gaussU_integrable ht hρ X
  have hm := p_wt1_gaussU_memLp ht hρ X
  refine ⟨⟨hi, hm⟩, ?_⟩
  filter_upwards [p_wt1_fourierL2_eq _ hi hm] with ξ hξ
  rw [hξ]
  have hG : Integrable (fun z : Euc d => ((gaussK (2 * t) z : ℝ) : ℂ)) :=
    (gaussK_basic (d := d) hb).2.2.1.ofReal
  have hfun : (fun z : Euc d => ((gaussU t X ρ z : ℝ) : ℂ)) =
      fun z => (1 / (N : ℂ)) * ∑ i : Fin N, ((gaussK (2 * t) (X i - z) : ℝ) : ℂ) -
        ((∫ y, gaussK (2 * t) (y - z) * ρ y : ℝ) : ℂ) := by
    ext z
    unfold gaussU
    push_cast
    rfl
  rw [hfun, p_wt1_fourier_lin Finset.univ _ (fun i z => ((gaussK (2 * t) (X i - z) : ℝ) : ℂ))
    (fun z : Euc d => ((∫ y, gaussK (2 * t) (y - z) * ρ y : ℝ) : ℂ))
    (fun i _ => hG.comp_sub_left (X i)) (p_wt1_U_integrable hb hρ).ofReal ξ]
  simp_rw [p_wt1_fourier_translate]
  rw [p_wt1_fourier_conv (p_wt1_integrable_rho hρ) hb, p_wt1_fourier_gauss hb ξ]
  unfold nuHat
  rw [← Finset.sum_mul]
  ring

end HRS.MH.CoercTest
