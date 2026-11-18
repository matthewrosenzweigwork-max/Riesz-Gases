import HRS.PDE.EnergyEstimate
import HRS.PDE.Galerkin
import HRS.PDE.GalerkinLimit
import HRS.PDE.Assembly
import HRS.PDE.Uniqueness
import HRS.PDE.HsAnalysis
import HRS.PDE.EnergyTorus
import HRS.PDE.EnergyTorusDeriv
import HRS.PDE.Energy

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.TRA

variable {d : ℕ}

/-! ### Calculus: square of a primitive -/

/-- `(c + ∫_0^τ γ)² = c² + ∫_0^τ 2 (c + ∫_0^x γ) γ(x) dx` for an interval integrable `γ`. -/
theorem sq_primitive_real (c : ℝ) {τ : ℝ} (γ : ℝ → ℝ) (hγ : IntervalIntegrable γ volume 0 τ) :
    (c + ∫ x in (0 : ℝ)..τ, γ x) ^ 2 =
      c ^ 2 + ∫ x in (0 : ℝ)..τ, 2 * (c + ∫ y in (0 : ℝ)..x, γ y) * γ x := by
  set I : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, γ y with hI
  have hAC : AbsolutelyContinuousOnInterval I 0 τ :=
    hγ.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hmain := hAC.integral_deriv_mul_eq_sub hAC
  have hderiv : ∀ᵐ x, x ∈ Set.uIcc 0 τ → deriv I x = γ x := by
    filter_upwards [hγ.ae_hasDerivAt_integral] with x hx hxm
    exact (hx hxm 0 (by simp)).deriv
  have hIc : ContinuousOn I (Set.uIcc 0 τ) := hAC.continuousOn
  have hi1 : IntervalIntegrable (fun x => I x * γ x) volume 0 τ :=
    hγ.continuousOn_mul hIc
  have hi2 : IntervalIntegrable (fun x => γ x * I x) volume 0 τ := hγ.mul_continuousOn hIc
  have e1 : ∫ x in (0 : ℝ)..τ, (deriv I x * I x + I x * deriv I x) =
      ∫ x in (0 : ℝ)..τ, 2 * (I x * γ x) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderiv] with x hx hxm
    have := hx (Set.uIoc_subset_uIcc hxm)
    rw [this]; ring
  have hI0 : I 0 = 0 := by simp [hI]
  rw [e1, intervalIntegral.integral_const_mul, hI0] at hmain
  have hint : ∫ x in (0 : ℝ)..τ, 2 * (c + I x) * γ x =
      2 * c * (∫ x in (0 : ℝ)..τ, γ x) + 2 * ∫ x in (0 : ℝ)..τ, I x * γ x := by
    have : ∀ x, 2 * (c + I x) * γ x = (2 * c) * γ x + 2 * (I x * γ x) := fun x => by ring
    simp_rw [this]
    rw [intervalIntegral.integral_add (hγ.const_mul _) (hi1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  show (c + I τ) ^ 2 = c ^ 2 + ∫ x in (0 : ℝ)..τ, 2 * (c + I x) * γ x
  rw [hint]
  have h2 : I τ * I τ - 0 * 0 = 2 * ∫ x in (0 : ℝ)..τ, I x * γ x := by
    simpa using hmain.symm
  have : I τ = ∫ x in (0 : ℝ)..τ, γ x := rfl
  nlinarith [h2, this]


/-- Complex version: `|a + ∫_0^τ g|² = |a|² + ∫_0^τ 2 Re(conj(a + ∫_0^x g) g(x)) dx`. -/
theorem sq_norm_primitive (a : ℂ) {τ : ℝ} (hτ : 0 ≤ τ) (g : ℝ → ℂ)
    (hg : IntervalIntegrable g volume 0 τ) :
    ‖a + ∫ x in (0 : ℝ)..τ, g x‖ ^ 2 = ‖a‖ ^ 2 +
      ∫ x in (0 : ℝ)..τ, 2 * (conj (a + ∫ y in (0 : ℝ)..x, g y) * g x).re := by
  have hre : IntervalIntegrable (fun x => (g x).re) volume 0 τ := ⟨Complex.reCLM.integrable_comp hg.1, Complex.reCLM.integrable_comp hg.2⟩
  have him : IntervalIntegrable (fun x => (g x).im) volume 0 τ := ⟨Complex.imCLM.integrable_comp hg.1, Complex.imCLM.integrable_comp hg.2⟩
  have hsub : ∀ x ∈ Set.Icc 0 τ, IntervalIntegrable g volume 0 x := fun x hx =>
    hg.mono_set (by rw [Set.uIcc_of_le hτ, Set.uIcc_of_le hx.1]; exact Set.Icc_subset_Icc_right hx.2)
  have hR : ∀ x ∈ Set.Icc 0 τ, (∫ y in (0 : ℝ)..x, g y).re = ∫ y in (0 : ℝ)..x, (g y).re :=
    fun x hx => (intervalIntegral.intervalIntegral_re (hsub x hx)).symm
  have hI : ∀ x ∈ Set.Icc 0 τ, (∫ y in (0 : ℝ)..x, g y).im = ∫ y in (0 : ℝ)..x, (g y).im :=
    fun x hx => (intervalIntegral.intervalIntegral_im (hsub x hx)).symm
  have h1 := sq_primitive_real a.re (τ := τ) (fun x => (g x).re) hre
  have h2 := sq_primitive_real a.im (τ := τ) (fun x => (g x).im) him
  have e1 : ‖a + ∫ x in (0 : ℝ)..τ, g x‖ ^ 2 =
      (a.re + ∫ x in (0 : ℝ)..τ, (g x).re) ^ 2 + (a.im + ∫ x in (0 : ℝ)..τ, (g x).im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
      hR τ ⟨hτ, le_rfl⟩, hI τ ⟨hτ, le_rfl⟩]
    ring
  rw [e1, h1, h2, Complex.sq_norm, Complex.normSq_apply]
  have hi1 : IntervalIntegrable (fun x => 2 * (a.re + ∫ y in (0 : ℝ)..x, (g y).re) * (g x).re)
      volume 0 τ := by
    have hc : ContinuousOn (fun x => 2 * (a.re + ∫ y in (0 : ℝ)..x, (g y).re)) (Set.uIcc 0 τ) :=
      (continuousOn_const.mul (continuousOn_const.add
        (intervalIntegral.continuousOn_primitive_interval' hre (by simp))))
    exact (hre.continuousOn_mul hc).congr (fun x _ => by ring)
  have hi2 : IntervalIntegrable (fun x => 2 * (a.im + ∫ y in (0 : ℝ)..x, (g y).im) * (g x).im)
      volume 0 τ := by
    have hc : ContinuousOn (fun x => 2 * (a.im + ∫ y in (0 : ℝ)..x, (g y).im)) (Set.uIcc 0 τ) :=
      (continuousOn_const.mul (continuousOn_const.add
        (intervalIntegral.continuousOn_primitive_interval' him (by simp))))
    exact (him.continuousOn_mul hc).congr (fun x _ => by ring)
  have hcongr : ∫ x in (0 : ℝ)..τ, 2 * (conj (a + ∫ y in (0 : ℝ)..x, g y) * g x).re =
      (∫ x in (0 : ℝ)..τ, 2 * (a.re + ∫ y in (0 : ℝ)..x, (g y).re) * (g x).re) +
        ∫ x in (0 : ℝ)..τ, 2 * (a.im + ∫ y in (0 : ℝ)..x, (g y).im) * (g x).im := by
    rw [← intervalIntegral.integral_add hi1 hi2]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hτ] at hx
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im,
      hR x hx, hI x hx]
    ring
  rw [hcongr]
  ring


/-! ### Abstract continuity of the weighted energy series -/

theorem intervalIntegrable_of_integrableOn {h : ℝ → ℝ} {t τ : ℝ} (hτ : τ ∈ Set.Icc 0 t)
    (hi : IntegrableOn h (Set.Icc 0 t)) : IntervalIntegrable h volume 0 τ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
  exact hi.mono_set (Set.Icc_subset_Icc_right hτ.2)

theorem intervalIntegrable_of_integrableOn' {E : Type*} [NormedAddCommGroup E] {h : ℝ → E}
    {t τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) (hi : IntegrableOn h (Set.Icc 0 t)) :
    IntervalIntegrable h volume 0 τ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
  exact hi.mono_set (Set.Icc_subset_Icc_right hτ.2)

/-- If `f_k(τ) = φ_k + ∫_0^τ g_k` with `g_k` integrable on `[0,t]` and
`∑ w_k ∫_0^t |f_k||g_k| < ∞`, then `τ ↦ ∑ w_k |f_k(τ)|²` is continuous on `[0,t]`. -/
theorem continuousOn_tsum_sq {ι : Type*} {t : ℝ} (ht : 0 ≤ t) (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k)
    (f g : ι → ℝ → ℂ) (φ : ι → ℂ)
    (hfc : ∀ k, ContinuousOn (f k) (Set.Icc 0 t))
    (hgi : ∀ k, IntegrableOn (g k) (Set.Icc 0 t))
    (hfe : ∀ k, ∀ τ ∈ Set.Icc 0 t, f k τ = φ k + ∫ σ in (0 : ℝ)..τ, g k σ)
    (hφ : Summable fun k => w k * ‖φ k‖ ^ 2)
    (hc : Summable fun k => w k * ∫ σ in (0 : ℝ)..t, ‖f k σ‖ * ‖g k σ‖) :
    ContinuousOn (fun τ => ∑' k, w k * ‖f k τ‖ ^ 2) (Set.Icc 0 t) := by
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hP : ∀ k, IntegrableOn (fun x => conj (f k x) * g k x) (Set.Icc 0 t) := fun k =>
    IntegrableOn.continuousOn_mul (Complex.continuous_conj.comp_continuousOn (hfc k)) (hgi k)
      isCompact_Icc
  have hN : ∀ k, IntegrableOn (fun x => ‖f k x‖ * ‖g k x‖) (Set.Icc 0 t) := fun k =>
    IntegrableOn.continuousOn_mul (hfc k).norm (hgi k).norm isCompact_Icc
  have hH : ∀ k, IntegrableOn (fun x => 2 * (conj (f k x) * g k x).re) (Set.Icc 0 t) := fun k =>
    ((Complex.reCLM.integrable_comp (hP k)).const_mul 2)
  set c : ι → ℝ := fun k => ∫ σ in (0 : ℝ)..t, ‖f k σ‖ * ‖g k σ‖ with hcdef
  set E : ι → ℝ → ℝ := fun k τ => ∫ x in (0 : ℝ)..τ, 2 * (conj (f k x) * g k x).re with hEdef
  have hc0 : ∀ k, 0 ≤ c k := fun k =>
    intervalIntegral.integral_nonneg ht (fun x _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  -- the identity
  have hid : ∀ k, ∀ τ ∈ Set.Icc 0 t, ‖f k τ‖ ^ 2 = ‖φ k‖ ^ 2 + E k τ := by
    intro k τ hτ
    have hgτ : IntervalIntegrable (g k) volume 0 τ := intervalIntegrable_of_integrableOn' hτ (hgi k)
    have h1 := sq_norm_primitive (φ k) hτ.1 (g k) hgτ
    rw [← hfe k τ hτ] at h1
    rw [h1]
    congr 1
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    rw [Set.uIcc_of_le hτ.1] at hx
    rw [← hfe k x ⟨hx.1, hx.2.trans hτ.2⟩]
  -- the bound
  have hbd : ∀ k, ∀ τ ∈ Set.Icc 0 t, |E k τ| ≤ 2 * c k := by
    intro k τ hτ
    have hHτ : IntervalIntegrable (fun x => 2 * (conj (f k x) * g k x).re) volume 0 τ :=
      intervalIntegrable_of_integrableOn hτ (hH k)
    have hNτ : IntervalIntegrable (fun x => 2 * (‖f k x‖ * ‖g k x‖)) volume 0 τ :=
      (intervalIntegrable_of_integrableOn hτ (hN k)).const_mul 2
    have hNt : IntervalIntegrable (fun x => 2 * (‖f k x‖ * ‖g k x‖)) volume 0 t :=
      (intervalIntegrable_of_integrableOn ht' (hN k)).const_mul 2
    calc |E k τ| = ‖E k τ‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ x in (0 : ℝ)..τ, ‖2 * (conj (f k x) * g k x).re‖ :=
          intervalIntegral.norm_integral_le_integral_norm hτ.1
      _ ≤ ∫ x in (0 : ℝ)..τ, 2 * (‖f k x‖ * ‖g k x‖) := by
          refine intervalIntegral.integral_mono_on hτ.1 hHτ.norm hNτ (fun x hx => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_two]
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          calc |(conj (f k x) * g k x).re| ≤ ‖conj (f k x) * g k x‖ := Complex.abs_re_le_norm _
            _ = ‖f k x‖ * ‖g k x‖ := by rw [norm_mul, Complex.norm_conj]
      _ ≤ ∫ x in (0 : ℝ)..t, 2 * (‖f k x‖ * ‖g k x‖) := by
          refine intervalIntegral.integral_mono_interval le_rfl hτ.1 hτ.2 ?_ hNt
          exact Filter.Eventually.of_forall fun x => by positivity
      _ = 2 * c k := by rw [intervalIntegral.integral_const_mul]
  have hEc : ∀ k, ContinuousOn (E k) (Set.Icc 0 t) := by
    intro k
    have := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_of_integrableOn ht' (hH k)) (a := 0) (by simp)
    rwa [Set.uIcc_of_le ht] at this
  have hsumE : ∀ τ ∈ Set.Icc 0 t, Summable fun k => w k * E k τ := by
    intro τ hτ
    refine Summable.of_norm_bounded (g := fun k => 2 * (w k * c k)) (hc.mul_left 2) fun k => ?_
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw k), Real.norm_eq_abs]
    calc w k * |E k τ| ≤ w k * (2 * c k) := mul_le_mul_of_nonneg_left (hbd k τ hτ) (hw k)
      _ = 2 * (w k * c k) := by ring
  have hcont : ContinuousOn (fun τ => ∑' k, w k * E k τ) (Set.Icc 0 t) := by
    refine continuousOn_tsum (u := fun k => 2 * (w k * c k)) (fun k => (hEc k).const_mul (w k))
      (hc.mul_left 2) (fun k τ hτ => ?_)
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw k), Real.norm_eq_abs]
    calc w k * |E k τ| ≤ w k * (2 * c k) := mul_le_mul_of_nonneg_left (hbd k τ hτ) (hw k)
      _ = 2 * (w k * c k) := by ring
  have heq : ∀ τ ∈ Set.Icc 0 t, ∑' k, w k * ‖f k τ‖ ^ 2 =
      (∑' k, w k * ‖φ k‖ ^ 2) + ∑' k, w k * E k τ := by
    intro τ hτ
    rw [← (hφ).tsum_add (hsumE τ hτ)]
    refine tsum_congr fun k => ?_
    rw [hid k τ hτ]; ring
  exact (continuousOn_const.add hcont).congr heq


/-! ### Strong continuity from weak continuity and continuity of the norm -/

theorem hsNormSq_sub_expand {r : ℝ} {a b : Coeff d} (ha : MemHs r a) (hb : MemHs r b) :
    hsNormSq r (a - b) = hsNormSq r a + hsNormSq r b - 2 * (hsInner r a b).re := by
  have hab := (ET.memHs_sub_sq ha hb).1
  have hS := ET.hsInner_summable ha hb
  have hre : (hsInner r a b).re = ∑' k, (((sobWeight r k : ℝ) : ℂ) * (a k * conj (b k))).re := by
    unfold hsInner
    exact (Complex.reCLM.map_tsum hS)
  have hS2 : Summable fun k => (((sobWeight r k : ℝ) : ℂ) * (a k * conj (b k))).re :=
    Complex.reCLM.summable hS
  have hpt : ∀ k, sobWeight r k * ‖(a - b) k‖ ^ 2 = sobWeight r k * ‖a k‖ ^ 2 +
      sobWeight r k * ‖b k‖ ^ 2 - 2 * (((sobWeight r k : ℝ) : ℂ) * (a k * conj (b k))).re := by
    intro k
    simp only [Pi.sub_apply, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  unfold hsNormSq
  rw [hre, ← tsum_mul_left, ← ha.tsum_add hb, ← (ha.add hb).tsum_sub (hS2.mul_left 2)]
  exact tsum_congr hpt

theorem continuousInHs_of_weak_norm {m t : ℝ} {F : ℝ → Coeff d} (hw : WeakContinuousInHs m F t)
    (hn : ContinuousOn (fun τ => hsNormSq m (F τ)) (Set.Icc 0 t)) : ContinuousInHs m F t := by
  refine ⟨hw.1, fun τ₀ hτ₀ => ?_⟩
  have h1 : Tendsto (fun τ => hsNormSq m (F τ)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 (hsNormSq m (F τ₀))) :=
    hn τ₀ hτ₀
  have h2 : Tendsto (fun τ => (hsInner m (F τ) (F τ₀)).re) (𝓝[Set.Icc 0 t] τ₀)
      (𝓝 (hsInner m (F τ₀) (F τ₀)).re) :=
    (Complex.continuous_re.continuousAt.tendsto.comp (hw.2 (F τ₀) (hw.1 τ₀ hτ₀) τ₀ hτ₀))
  have hself : (hsInner m (F τ₀) (F τ₀)).re = hsNormSq m (F τ₀) := by
    have := hsNormSq_sub_expand (hw.1 τ₀ hτ₀) (hw.1 τ₀ hτ₀)
    simp only [sub_self] at this
    have h0 : hsNormSq m (0 : Coeff d) = 0 := by simp [hsNormSq]
    rw [h0] at this
    linarith
  rw [hself] at h2
  have h3 : Tendsto (fun τ => hsNormSq m (F τ - F τ₀)) (𝓝[Set.Icc 0 t] τ₀) (𝓝 0) := by
    have := (h1.add_const (hsNormSq m (F τ₀))).sub (h2.const_mul 2)
    have e : hsNormSq m (F τ₀) + hsNormSq m (F τ₀) - 2 * hsNormSq m (F τ₀) = 0 := by ring
    rw [e] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [hsNormSq_sub_expand (hw.1 τ hτ) (hw.1 τ₀ hτ₀)]
  have := h3.sqrt
  simpa [hsNorm] using this


/-! ### The cross-term estimate by Cauchy–Schwarz and the dissipation bound -/

theorem amgm_weight (j : ℕ) (k : Lattice d) (a b : ℝ) :
    sobWeight ((j : ℝ) + 1) k * (a * b) ≤
      (1 / 2) * (sobWeight ((j : ℝ) + 2) k * a ^ 2 + sobWeight (j : ℝ) k * b ^ 2) := by
  have hx : sobWeight ((j : ℝ) + 1) k = sobWeight (j : ℝ) k * sobWeight 1 k := by
    rw [← sobWeight_add]
  have hy : sobWeight ((j : ℝ) + 2) k = sobWeight (j : ℝ) k * sobWeight 1 k * sobWeight 1 k := by
    rw [← sobWeight_add, ← sobWeight_add]; ring_nf
  rw [hx, hy]
  have hv := (sobWeight_pos (j : ℝ) k).le
  nlinarith [mul_nonneg hv (sq_nonneg (sobWeight 1 k * a - b))]

theorem summable_cross {ι : Type*} [Countable ι] (f g : ι → ℝ → ℂ) (t : ℝ) (ht : 0 ≤ t)
    (K'' : ℝ) (hK'' : 0 ≤ K'')
    (wA wB wC : ι → ℝ) (hA : ∀ k, 0 ≤ wA k) (hC : ∀ k, 0 ≤ wC k)
    (hamgm : ∀ k (a b : ℝ), wC k * (a * b) ≤ (1 / 2) * (wA k * a ^ 2 + wB k * b ^ 2))
    (hfc : ∀ k, ContinuousOn (f k) (Set.Icc 0 t))
    (hgi : ∀ k, IntegrableOn (g k) (Set.Icc 0 t))
    (Kd : ℝ)
    (hdiss : ∀ S : Finset ι, ∑ k ∈ S, ∫ σ in (0 : ℝ)..t, wA k * ‖f k σ‖ ^ 2 ≤ Kd)
    (hgen : ∀ σ ∈ Set.Icc 0 t, (Summable fun k => wA k * ‖f k σ‖ ^ 2) →
      (∀ S : Finset ι, ∑ k ∈ S, wB k * ‖g k σ‖ ^ 2 ≤
        K'' * ∑' k, wA k * ‖f k σ‖ ^ 2)) :
    ∃ M : ℝ, ∀ S : Finset ι, ∑ k ∈ S, wC k * ∫ σ in (0 : ℝ)..t, ‖f k σ‖ * ‖g k σ‖ ≤ M := by
  have hKd0 : 0 ≤ Kd := by simpa using hdiss ∅
  have ht' : t ∈ Set.Icc (0 : ℝ) t := ⟨ht, le_rfl⟩
  have hW : ∀ k, ContinuousOn (fun σ => wA k * ‖f k σ‖ ^ 2) (Set.Icc 0 t) := fun k =>
    continuousOn_const.mul ((hfc k).norm.pow 2)
  have hWnn : ∀ k σ, 0 ≤ wA k * ‖f k σ‖ ^ 2 := fun k σ => mul_nonneg (hA k) (sq_nonneg _)
  set Φ : ℝ → ℝ≥0∞ := fun σ => ∑' k, ENNReal.ofReal (wA k * ‖f k σ‖ ^ 2) with hΦ
  have hΦint : ∫⁻ σ in Set.Icc 0 t, Φ σ ≤ ENNReal.ofReal Kd := by
    have hlt : ∫⁻ σ in Set.Icc 0 t, Φ σ =
        ∑' k, ∫⁻ σ in Set.Icc 0 t, ENNReal.ofReal (wA k * ‖f k σ‖ ^ 2) :=
      lintegral_tsum (fun k => ENNReal.measurable_ofReal.comp_aemeasurable
        ((hW k).aemeasurable measurableSet_Icc))
    rw [hlt]
    have hterm : ∀ k, ∫⁻ σ in Set.Icc 0 t, ENNReal.ofReal (wA k * ‖f k σ‖ ^ 2) =
        ENNReal.ofReal (∫ σ in (0 : ℝ)..t, wA k * ‖f k σ‖ ^ 2) := by
      intro k
      rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc,
        ofReal_integral_eq_lintegral_ofReal ((hW k).integrableOn_Icc)
          (Filter.Eventually.of_forall fun σ => hWnn k σ)]
    simp_rw [hterm]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun S => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => intervalIntegral.integral_nonneg ht
      (fun σ _ => hWnn k σ))]
    exact ENNReal.ofReal_le_ofReal (hdiss S)
  have hN : ∀ k, IntegrableOn (fun x => ‖f k x‖ * ‖g k x‖) (Set.Icc 0 t) := fun k =>
    IntegrableOn.continuousOn_mul (hfc k).norm (hgi k).norm isCompact_Icc
  set M₀ : ℝ := (1 + K'') / 2 with hM₀
  have hM₀pos : 0 < M₀ := by rw [hM₀]; linarith
  refine ⟨M₀ * Kd, fun S => ?_⟩
  set H : ℝ → ℝ := fun σ => ∑ k ∈ S, wC k * (‖f k σ‖ * ‖g k σ‖) with hH
  have hHint : IntegrableOn H (Set.Icc 0 t) :=
    integrable_finsetSum _ fun k _ => (hN k).const_mul (wC k)
  have hHnn : ∀ σ, 0 ≤ H σ := fun σ =>
    Finset.sum_nonneg fun k _ => mul_nonneg (hC k) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hsumeq : ∑ k ∈ S, wC k * ∫ σ in (0 : ℝ)..t, ‖f k σ‖ * ‖g k σ‖ =
      ∫ σ in Set.Icc 0 t, H σ := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht, hH,
      intervalIntegral.integral_finsetSum (fun k _ =>
        (intervalIntegrable_of_integrableOn ht' (hN k)).const_mul (wC k))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul]
  have hpt : ∀ σ ∈ Set.Icc 0 t, ENNReal.ofReal (H σ) ≤ ENNReal.ofReal M₀ * Φ σ := by
    intro σ hσ
    by_cases hsum : Summable fun k => wA k * ‖f k σ‖ ^ 2
    · have hΦσ : Φ σ = ENNReal.ofReal (∑' k, wA k * ‖f k σ‖ ^ 2) :=
        (ENNReal.ofReal_tsum_of_nonneg (hWnn · σ) hsum).symm
      rw [hΦσ, ← ENNReal.ofReal_mul hM₀pos.le]
      refine ENNReal.ofReal_le_ofReal ?_
      set T := ∑' k, wA k * ‖f k σ‖ ^ 2 with hT
      have h1 : ∑ k ∈ S, wA k * ‖f k σ‖ ^ 2 ≤ T :=
        hsum.sum_le_tsum S (fun k _ => hWnn k σ)
      have h2 := hgen σ hσ hsum S
      calc H σ ≤ ∑ k ∈ S, (1 / 2) * (wA k * ‖f k σ‖ ^ 2 + wB k * ‖g k σ‖ ^ 2) :=
            Finset.sum_le_sum fun k _ => hamgm k _ _
        _ = (1 / 2) * (∑ k ∈ S, wA k * ‖f k σ‖ ^ 2 + ∑ k ∈ S, wB k * ‖g k σ‖ ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
        _ ≤ M₀ * T := by
            rw [hM₀]; nlinarith
    · have htop : Φ σ = ⊤ := by
        by_contra hne
        apply hsum
        have := ENNReal.summable_toReal hne
        refine this.congr fun k => ?_
        exact ENNReal.toReal_ofReal (hWnn k σ)
      rw [htop, ENNReal.mul_top (by simpa using hM₀pos)]
      exact le_top
  have hlint : ENNReal.ofReal (∫ σ in Set.Icc 0 t, H σ) ≤ ENNReal.ofReal (M₀ * Kd) := by
    rw [ofReal_integral_eq_lintegral_ofReal hHint (Filter.Eventually.of_forall hHnn)]
    calc ∫⁻ σ in Set.Icc 0 t, ENNReal.ofReal (H σ)
        ≤ ∫⁻ σ in Set.Icc 0 t, ENNReal.ofReal M₀ * Φ σ :=
          setLIntegral_mono' measurableSet_Icc hpt
      _ = ENNReal.ofReal M₀ * ∫⁻ σ in Set.Icc 0 t, Φ σ :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal M₀ * ENNReal.ofReal Kd := by gcongr
      _ = ENNReal.ofReal (M₀ * Kd) := (ENNReal.ofReal_mul hM₀pos.le).symm
  rw [hsumeq]
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hM₀pos.le hKd0)).1 hlint


/-! ### Continuity of the energy of a weakly continuous forward solution, given the dissipation bound -/

theorem normSq_continuousOn (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    {R : Regime} {MB Λ VB : ℝ} {D : DynData d} {ν₀ T : ℝ} {μ : ℝ → Torus d → ℝ}
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {φc : Coeff d}
    (hφ : MemHs (m : ℝ) φc) {F : ℝ → Coeff d} (hF : IsForwardSolution D μ t φc F)
    (hw : WeakContinuousInHs (m : ℝ) F t) (Kd : ℝ)
    (hdiss : ∀ S : Finset (Lattice d), ∑ k ∈ S,
      ∫ σ in (0 : ℝ)..t, sobWeight ((m : ℝ) + 1) k * ‖F σ k‖ ^ 2 ≤ Kd) :
    ContinuousOn (fun τ => hsNormSq (m : ℝ) (F τ)) (Set.Icc 0 t) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have e0 : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  have e1 : ((j + 1 : ℕ) : ℝ) + 1 = (j : ℝ) + 2 := by rw [e0]; ring
  have e2 : ((j + 1 : ℕ) : ℝ) - 1 = (j : ℝ) := by rw [e0]; ring
  have hVj : VHyp j VB D.V :=
    ⟨ET.isCk_mono' (a := j + 3) (b := j + 1 + 3) (by omega) hA.hV.1,
      (ET.cbNorm_mono' (a := j + 3) (b := j + 1 + 3) (by omega) D.V).trans hA.hV.2⟩
  obtain ⟨K, hK0, hK⟩ := ET.forwardGen_hs_bound hd s hs0 hsd j MB Λ VB
  have ht0 : 0 ≤ t := ht.1.le
  have hgen : ∀ σ ∈ Set.Icc 0 t, ∀ u : Coeff d, MemHs ((j : ℝ) + 2) u →
      MemHs (j : ℝ) (forwardGen D (μ (t - σ)) u) ∧ hsNormSq (j : ℝ) (forwardGen D (μ (t - σ)) u) ≤
        (3 * D.invβ ^ 2 + K) * hsNormSq ((j : ℝ) + 2) u := by
    intro σ hσ u hu
    have hr := ET.tsub_mem_Icc ht hσ
    exact hK D hA.hs hA.hM hVj (μ (t - σ)) (hA.hμ.prob _ hr)
      (ET.isCk_mono' (a := j + 3) (b := j + 1 + 3) (by omega) (hA.hμ.smooth _ hr))
      ((ET.cbNorm_mono' (a := j + 3) (b := j + 1 + 3) (by omega) _).trans (hA.hμ.bound _ hr)) u hu
  have hfc : ∀ k, ContinuousOn (fun σ => F σ k) (Set.Icc 0 t) := fun k =>
    continuousOn_coord_of_weak hw k
  have hgi : ∀ k, IntegrableOn (fun σ => forwardGen D (μ (t - σ)) (F σ) k) (Set.Icc 0 t) :=
    hF.integrable
  obtain ⟨M, hM⟩ := summable_cross (fun k σ => F σ k)
    (fun k σ => forwardGen D (μ (t - σ)) (F σ) k) t ht0 (3 * D.invβ ^ 2 + K) (by positivity)
    (fun k => sobWeight (((j + 1 : ℕ) : ℝ) + 1) k) (fun k => sobWeight (((j + 1 : ℕ) : ℝ) - 1) k)
    (fun k => sobWeight ((j + 1 : ℕ) : ℝ) k) (fun k => sobWeight_nonneg _ k) (fun k => sobWeight_nonneg _ k)
    (fun k a b => by
      have := amgm_weight j k a b
      rw [e1, e2, e0]; exact this)
    hfc hgi Kd hdiss (fun σ hσ hsum S => by
      have hu : MemHs ((j : ℝ) + 2) (F σ) := by rw [← e1]; exact hsum
      obtain ⟨h1, h2⟩ := hgen σ hσ (F σ) hu
      have h3 := sum_le_hsNormSq h1 S
      have h4 : ∑' k, sobWeight (((j + 1 : ℕ) : ℝ) + 1) k * ‖F σ k‖ ^ 2 = hsNormSq ((j : ℝ) + 2) (F σ) := by
        rw [e1]; rfl
      rw [h4]
      simp only [e2]
      exact h3.trans h2)
  have hcsum : Summable fun k => sobWeight ((j + 1 : ℕ) : ℝ) k *
      ∫ σ in (0 : ℝ)..t, ‖F σ k‖ * ‖forwardGen D (μ (t - σ)) (F σ) k‖ := by
    refine summable_of_sum_le (c := M) (fun k => mul_nonneg (sobWeight_nonneg _ k)
      (intervalIntegral.integral_nonneg ht0 fun σ _ => mul_nonneg (norm_nonneg _)
        (norm_nonneg _))) hM
  exact continuousOn_tsum_sq ht0 (fun k => sobWeight ((j + 1 : ℕ) : ℝ) k) (fun k => sobWeight_nonneg _ k)
    (fun k σ => F σ k) (fun k σ => forwardGen D (μ (t - σ)) (F σ) k) φc hfc hgi
    (fun k τ hτ => hF.eq k τ hτ) hφ hcsum


/-! ### Dissipation for Galerkin solutions with real data -/

theorem galSol_hsNormSq_continuousOn {t : ℝ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {n : ℕ}
    {φc : Coeff d} {F : ℝ → Coeff d} (hF : IsGalSol D μ t n φc F) (r : ℝ) :
    ContinuousOn (fun τ => hsNormSq r (F τ)) (Set.Icc 0 t) := by
  have e : (fun τ => hsNormSq r (F τ)) =
      fun τ => ∑ k ∈ boxFinset d n, sobWeight r k * ‖F τ k‖ ^ 2 :=
    funext fun τ => hsNormSq_trig (hF.trig τ) r
  rw [e]
  exact continuousOn_finsetSum _ fun k _ => continuousOn_const.mul ((hF.cont k).norm.pow 2)

theorem hasDerivWithinAt_integral_real {t : ℝ} (ht : 0 ≤ t) {p : ℝ → ℝ}
    (hp : ContinuousOn p (Set.Icc 0 t)) :
    ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt (fun τ => ∫ σ in (0 : ℝ)..τ, p σ) (p τ)
      (Set.Icc 0 t) τ := by
  intro τ hτ
  set B : ℝ → ℝ := Set.IccExtend ht (fun s : Set.Icc (0 : ℝ) t => p s) with hBdef
  have hB : Continuous B := hp.domRestrict.Icc_extend'
  have hBg : ∀ s ∈ Set.Icc (0 : ℝ) t, B s = p s := fun s hs => Set.IccExtend_of_mem ht _ hs
  have h1 : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, B s) (B τ) τ :=
    (hB.integral_hasStrictDerivAt 0 τ).hasDerivAt
  have h2 := h1.hasDerivWithinAt (s := Set.Icc 0 t)
  rw [hBg τ hτ] at h2
  have hint : ∀ u ∈ Set.Icc (0 : ℝ) t, ∫ s in (0 : ℝ)..u, p s = ∫ s in (0 : ℝ)..u, B s := by
    intro u hu
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [hBg s (Set.uIcc_subset_Icc ⟨le_rfl, ht⟩ hu hs)]
  exact h2.congr (fun u hu => hint u hu) (hint τ hτ)

theorem sub_le_integral_of_hasDerivWithinAt {t : ℝ} (ht : 0 ≤ t) {y y' p : ℝ → ℝ}
    (hy : ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt y (y' τ) (Set.Icc 0 t) τ)
    (hle : ∀ τ ∈ Set.Icc 0 t, y' τ ≤ p τ) (hp : ContinuousOn p (Set.Icc 0 t)) :
    y t - y 0 ≤ ∫ τ in (0 : ℝ)..t, p τ := by
  set u : ℝ → ℝ := fun τ => y τ - ∫ σ in (0 : ℝ)..τ, p σ with hu
  have hud : ∀ τ ∈ Set.Icc 0 t, HasDerivWithinAt u (y' τ - p τ) (Set.Icc 0 t) τ :=
    fun τ hτ => (hy τ hτ).sub (hasDerivWithinAt_integral_real ht hp τ hτ)
  have hanti : AntitoneOn u (Set.Icc 0 t) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t) ?_ ?_ ?_
    · exact fun τ hτ => (hud τ hτ).continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact (((hud τ (Set.Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2))
        ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      rw [((hud τ (Set.Ioo_subset_Icc_self hτ)).hasDerivAt (Icc_mem_nhds hτ.1 hτ.2)).deriv]
      linarith [hle τ (Set.Ioo_subset_Icc_self hτ)]
  have h := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only [hu, intervalIntegral.integral_same, sub_zero] at h
  linarith


theorem energyRHS_le_grad (R : Regime) (Λm : ℝ) (D : DynData d) (m : ℕ)
    (lam : Fin d → ℝ) (q : Fin d → Euc d) (hd : 1 ≤ d) (hlam : R.IsR2 → ∀ l, 0 ≤ lam l)
    (μ : Torus d → ℝ) (F : Coeff d) :
    energyRHS R Λm D m lam q μ F ≤
      Λm * hsNormSq m F - (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α F := by
  unfold energyRHS
  have h2 : 0 ≤ (if R.IsR2 then (1 / 2) * weightedDissipation D m lam q μ F else 0) := by
    split_ifs with hR
    · refine mul_nonneg (by norm_num) ?_
      unfold weightedDissipation
      refine Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun l _ => ?_
      exact mul_nonneg (hlam hR l) (quadForm_symbolK_nonneg hd D.hs0 D.hsd _ _)
    · exact le_rfl
  linarith

/-- The constant of the dissipation bound. -/
def dissConst (c ν Λm t : ℝ) : ℝ :=
  ((2 * |Λm| + ν * c) * t * Real.exp (2 * |Λm| * t) + 1) / (ν * c)

theorem galSol_dissipation {m : ℕ} {Λ T VB : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {D : DynData d} (hV : VHyp m VB D.V) (hν : 0 < D.invβ)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {n : ℕ} {φc : Coeff d} (hφ : IsRealCoeff φc)
    (hmem : MemHs (m : ℝ) φc) {F : ℝ → Coeff d} (hF : IsGalSol D μ t n φc F) (Λm c : ℝ)
    (hc0 : 0 < c)
    (hc : ∀ G : Coeff d, MemHs ((m : ℝ) + 1) G →
      c * (hsNormSq ((m : ℝ) + 1) G - hsNormSq (m : ℝ) G) ≤
        ∑ α ∈ multiIndices d m, gradDerivL2Sq α G)
    (hform : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ G : Coeff d, IsRealCoeff G → IsTrigPoly n G →
      (hsInner (m : ℝ) (forwardGen D (μ r) G) G).re ≤
        Λm * hsNormSq (m : ℝ) G - (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α G) :
    (∀ τ ∈ Set.Icc 0 t, hsNorm (m : ℝ) (F τ) ≤ Real.exp (Λm * τ) * hsNorm (m : ℝ) φc) ∧
    ∫ τ in (0 : ℝ)..t, hsNormSq ((m : ℝ) + 1) (F τ) ≤
      dissConst c D.invβ Λm t * hsNormSq (m : ℝ) φc := by
  have ht0 : 0 ≤ t := ht.1.le
  have hreal := hF.isReal h hV ht hφ
  have hgradnn : ∀ G : Coeff d, 0 ≤ ∑ α ∈ multiIndices d m, gradDerivL2Sq α G := fun G =>
    Finset.sum_nonneg fun α _ => gradDerivL2Sq_nonneg α G
  have hsup := galSol_bound h hV ht hφ hmem hF Λm (fun r hr G hG hGt => by
    have := hform r hr G hG hGt
    have h2 := mul_nonneg (div_nonneg hν.le (by norm_num : (0 : ℝ) ≤ 2)) (hgradnn G)
    linarith)
  refine ⟨hsup, ?_⟩
  set y : ℝ → ℝ := fun τ => hsNormSq (m : ℝ) (F τ) with hy
  set z : ℝ → ℝ := fun τ => hsNormSq ((m : ℝ) + 1) (F τ) with hz
  have hyc : ContinuousOn y (Set.Icc 0 t) := galSol_hsNormSq_continuousOn hF _
  have hzc : ContinuousOn z (Set.Icc 0 t) := galSol_hsNormSq_continuousOn hF _
  set p : ℝ → ℝ := fun τ => 2 * Λm * y τ - D.invβ * c * (z τ - y τ) with hp
  have hpc : ContinuousOn p (Set.Icc 0 t) :=
    (continuousOn_const.mul hyc).sub (continuousOn_const.mul (hzc.sub hyc))
  have hdev := hF.hasDeriv_hsNormSq h ht (m : ℝ)
  have hle : ∀ τ ∈ Set.Icc 0 t,
      2 * (hsInner (m : ℝ) (forwardGen D (μ (t - τ)) (F τ)) (F τ)).re ≤ p τ := by
    intro τ hτ
    have hr : t - τ ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hτ.2], by linarith [hτ.1, ht.2]⟩
    have h1 := hform (t - τ) hr (F τ) (hreal τ hτ) (hF.trig τ)
    have h2 := hc (F τ) (isTrigPoly_memHs (hF.trig τ) _)
    have h3 := mul_le_mul_of_nonneg_left h2 hν.le
    simp only [hp, hy, hz]
    nlinarith
  have hmain := sub_le_integral_of_hasDerivWithinAt ht0 hdev hle hpc
  have hyi : IntervalIntegrable y volume 0 t := hyc.intervalIntegrable_of_Icc ht0
  have hzi : IntervalIntegrable z volume 0 t := hzc.intervalIntegrable_of_Icc ht0
  have hint : ∫ τ in (0 : ℝ)..t, p τ = 2 * Λm * (∫ τ in (0 : ℝ)..t, y τ) -
      D.invβ * c * ((∫ τ in (0 : ℝ)..t, z τ) - ∫ τ in (0 : ℝ)..t, y τ) := by
    simp only [hp]
    rw [intervalIntegral.integral_sub (hyi.const_mul _) ((hzi.sub hyi).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub hzi hyi]
  rw [hint] at hmain
  -- bounds on y
  have hysq : ∀ τ ∈ Set.Icc 0 t, y τ ≤ Real.exp (2 * |Λm| * t) * hsNormSq (m : ℝ) φc := by
    intro τ hτ
    have h1 := hsup τ hτ
    have hn0 := Real.sqrt_nonneg (hsNormSq (m : ℝ) (F τ))
    have h2 : hsNormSq (m : ℝ) (F τ) = hsNorm (m : ℝ) (F τ) ^ 2 :=
      (Real.sq_sqrt (hsNormSq_nonneg _ _)).symm
    have h3 : hsNormSq (m : ℝ) φc = hsNorm (m : ℝ) φc ^ 2 :=
      (Real.sq_sqrt (hsNormSq_nonneg _ _)).symm
    have h4 : Real.exp (Λm * τ) ≤ Real.exp (|Λm| * t) := by
      refine Real.exp_le_exp.2 ?_
      calc Λm * τ ≤ |Λm| * τ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ.1
        _ ≤ |Λm| * t := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)
    have h5 : hsNorm (m : ℝ) (F τ) ≤ Real.exp (|Λm| * t) * hsNorm (m : ℝ) φc :=
      h1.trans (mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg _))
    show hsNormSq (m : ℝ) (F τ) ≤ _
    rw [h2, h3]
    calc hsNorm (m : ℝ) (F τ) ^ 2 ≤ (Real.exp (|Λm| * t) * hsNorm (m : ℝ) φc) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h5 2
      _ = Real.exp (2 * |Λm| * t) * hsNorm (m : ℝ) φc ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
  have hy0 : y 0 ≤ hsNormSq (m : ℝ) φc := by
    have h0 : F 0 = truncCoeff n φc := by
      funext k
      have := hF.eq k 0 ⟨le_rfl, ht0⟩
      simpa using this
    show hsNormSq (m : ℝ) (F 0) ≤ _
    rw [h0]; exact hsNormSq_truncCoeff_le n hmem
  have hyint : ∫ τ in (0 : ℝ)..t, y τ ≤ t * (Real.exp (2 * |Λm| * t) * hsNormSq (m : ℝ) φc) := by
    have := intervalIntegral.integral_mono_on ht0 hyi intervalIntegrable_const hysq
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    linarith
  have hyint0 : 0 ≤ ∫ τ in (0 : ℝ)..t, y τ :=
    intervalIntegral.integral_nonneg ht0 fun τ _ => hsNormSq_nonneg _ _
  have hyt : 0 ≤ y t := hsNormSq_nonneg _ _
  -- conclusion
  unfold dissConst
  rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hν hc0)]
  set A := ∫ τ in (0 : ℝ)..t, z τ with hA
  set Y := ∫ τ in (0 : ℝ)..t, y τ with hY
  set N := hsNormSq (m : ℝ) φc with hN
  have hN0 : 0 ≤ N := hsNormSq_nonneg _ _
  have h1 : D.invβ * c * A ≤ (2 * Λm + D.invβ * c) * Y + y 0 - y t := by nlinarith
  have h2 : (2 * Λm + D.invβ * c) * Y ≤ (2 * |Λm| + D.invβ * c) * Y :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self Λm]) hyint0
  have h3 : (2 * |Λm| + D.invβ * c) * Y ≤
      (2 * |Λm| + D.invβ * c) * (t * (Real.exp (2 * |Λm| * t) * N)) :=
    mul_le_mul_of_nonneg_left hyint (by positivity)
  have h4 : A * (D.invβ * c) = D.invβ * c * A := by ring
  rw [h4]
  nlinarith


/-- Complex data: existence of a Galerkin solution with the sup bound and the dissipation bound. -/
theorem galSol_complex_dissipation {m : ℕ} {Λ T VB : ℝ} {μ : ℝ → Torus d → ℝ}
    (h : CoeffHyp m Λ T μ) {D : DynData d} (hV : VHyp m VB D.V) {t : ℝ} (ht : t ∈ Set.Ioc 0 T)
    (E : ℝ → ℝ) (hE0 : ∀ τ, 0 ≤ E τ) (K₀ : ℝ)
    (hreal : ∀ (φ' : Coeff d), MemHs (m : ℝ) φ' → IsRealCoeff φ' → ∀ (n : ℕ) (F : ℝ → Coeff d),
      IsGalSol D μ t n φ' F →
        (∀ τ ∈ Set.Icc 0 t, hsNorm (m : ℝ) (F τ) ≤ E τ * hsNorm (m : ℝ) φ') ∧
        ∫ τ in (0 : ℝ)..t, hsNormSq ((m : ℝ) + 1) (F τ) ≤ K₀ * hsNormSq (m : ℝ) φ')
    (n : ℕ) (φ : Coeff d) (hφ : MemHs (m : ℝ) φ) :
    ∃ F : ℝ → Coeff d, IsGalSol D μ t n φ F ∧
      (∀ τ ∈ Set.Icc 0 t, hsNorm (m : ℝ) (F τ) ≤ E τ * hsNorm (m : ℝ) φ) ∧
      ∫ τ in (0 : ℝ)..t, hsNormSq ((m : ℝ) + 1) (F τ) ≤ K₀ * hsNormSq (m : ℝ) φ := by
  have ht0 : 0 ≤ t := ht.1.le
  obtain ⟨hre, him, hsum⟩ := memHs_rePart_imPart hφ
  obtain ⟨F₁, hF₁, -⟩ := galSol_exists_unique h ht D n (rePart φ)
  obtain ⟨F₂, hF₂, -⟩ := galSol_exists_unique h ht D n (imPart φ)
  have hF := IsGalSol.add_smul h ht Complex.I hF₁ hF₂
  rw [rePart_add_I_imPart] at hF
  have r₁ := hF₁.isReal h hV ht (isRealCoeff_rePart φ)
  have r₂ := hF₂.isReal h hV ht (isRealCoeff_imPart φ)
  obtain ⟨b₁, i₁⟩ := hreal _ hre (isRealCoeff_rePart φ) n F₁ hF₁
  obtain ⟨b₂, i₂⟩ := hreal _ him (isRealCoeff_imPart φ) n F₂ hF₂
  refine ⟨_, hF, fun τ hτ => ?_, ?_⟩
  · have py := hsNormSq_add_I_smul (hF₁.trig τ) (hF₂.trig τ) (r₁ τ hτ) (r₂ τ hτ) (m : ℝ)
    have sq : ∀ c : Coeff d, hsNorm (m : ℝ) c ^ 2 = hsNormSq (m : ℝ) c := fun c =>
      Real.sq_sqrt (hsNormSq_nonneg _ _)
    have hnorm : hsNorm (m : ℝ) (F₁ τ + Complex.I • F₂ τ) ^ 2 ≤
        (E τ * hsNorm (m : ℝ) φ) ^ 2 := by
      simp only [sq, py]
      rw [← sq (F₁ τ), ← sq (F₂ τ)]
      calc hsNorm (m : ℝ) (F₁ τ) ^ 2 + hsNorm (m : ℝ) (F₂ τ) ^ 2
          ≤ (E τ * hsNorm (m : ℝ) (rePart φ)) ^ 2 + (E τ * hsNorm (m : ℝ) (imPart φ)) ^ 2 :=
            add_le_add (pow_le_pow_left₀ (Real.sqrt_nonneg _) (b₁ τ hτ) 2)
              (pow_le_pow_left₀ (Real.sqrt_nonneg _) (b₂ τ hτ) 2)
        _ = E τ ^ 2 * (hsNorm (m : ℝ) (rePart φ) ^ 2 + hsNorm (m : ℝ) (imPart φ) ^ 2) := by ring
        _ = (E τ * hsNorm (m : ℝ) φ) ^ 2 := by rw [sq, sq, hsum, ← sq]; ring
    exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _)
      (mul_nonneg (hE0 τ) (Real.sqrt_nonneg _)) two_ne_zero).1 hnorm
  · have hc1 := galSol_hsNormSq_continuousOn hF₁ ((m : ℝ) + 1)
    have hc2 := galSol_hsNormSq_continuousOn hF₂ ((m : ℝ) + 1)
    have e : ∫ τ in (0 : ℝ)..t, hsNormSq ((m : ℝ) + 1) (F₁ τ + Complex.I • F₂ τ) =
        ∫ τ in (0 : ℝ)..t, (hsNormSq ((m : ℝ) + 1) (F₁ τ) + hsNormSq ((m : ℝ) + 1) (F₂ τ)) := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le ht0] at hτ
      exact hsNormSq_add_I_smul (hF₁.trig τ) (hF₂.trig τ) (r₁ τ hτ) (r₂ τ hτ) _
    show ∫ τ in (0 : ℝ)..t, hsNormSq ((m : ℝ) + 1) (F₁ τ + Complex.I • F₂ τ) ≤ _
    rw [e, intervalIntegral.integral_add (hc1.intervalIntegrable_of_Icc ht0)
      (hc2.intervalIntegrable_of_Icc ht0)]
    calc _ ≤ K₀ * hsNormSq (m : ℝ) (rePart φ) + K₀ * hsNormSq (m : ℝ) (imPart φ) :=
          add_le_add i₁ i₂
      _ = K₀ * hsNormSq (m : ℝ) φ := by rw [← mul_add, hsum]


/-! ### Passage to the limit in the dissipation bound -/

theorem limit_integral_coord {t : ℝ} (ht : 0 ≤ t) (m : ℝ) (Fn : ℕ → ℝ → Coeff d)
    (G : ℝ → Coeff d) (ψ : ℕ → ℕ) (B : ℝ)
    (hconv : ∀ k, TendstoUniformlyOn (fun n τ => Fn (ψ n) τ k) (fun τ => G τ k) atTop
      (Set.Icc 0 t))
    (hcont : ∀ n k, ContinuousOn (fun τ => Fn n τ k) (Set.Icc 0 t))
    (hmem : ∀ n τ, MemHs m (Fn n τ))
    (hB : ∀ n, ∀ τ ∈ Set.Icc 0 t, hsNormSq m (Fn n τ) ≤ B) (k : Lattice d) :
    Tendsto (fun n => ∫ σ in (0 : ℝ)..t, sobWeight (m + 1) k * ‖Fn (ψ n) σ k‖ ^ 2) atTop
      (𝓝 (∫ σ in (0 : ℝ)..t, sobWeight (m + 1) k * ‖G σ k‖ ^ 2)) := by
  have hsub : Set.uIoc (0 : ℝ) t ⊆ Set.Icc 0 t := by
    rw [Set.uIoc_of_le ht]; exact Set.Ioc_subset_Icc_self
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => sobWeight 1 k * B) (Filter.Eventually.of_forall fun n => ?_)
    (Filter.Eventually.of_forall fun n => Filter.Eventually.of_forall fun x hx => ?_)
    intervalIntegrable_const (Filter.Eventually.of_forall fun x hx => ?_)
  · exact (continuousOn_const.mul (((hcont (ψ n) k).norm.pow 2))).mono
      hsub |>.aestronglyMeasurable measurableSet_uIoc
  · have h1 := sobWeight_mul_sq_le_hsNormSq (hmem (ψ n) x) k
    have h2 := hB (ψ n) x (hsub hx)
    have hw1 := (sobWeight_pos 1 (d := d) k).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sobWeight_nonneg _ k) (sq_nonneg _)),
      sobWeight_add]
    calc sobWeight m k * sobWeight 1 k * ‖Fn (ψ n) x k‖ ^ 2
        = sobWeight 1 k * (sobWeight m k * ‖Fn (ψ n) x k‖ ^ 2) := by ring
      _ ≤ sobWeight 1 k * B := mul_le_mul_of_nonneg_left (h1.trans h2) hw1
  · exact ((((hconv k).tendsto_at (hsub hx)).norm).pow 2).const_mul _


/-! ### Step 1: the integrated dissipation bound for a weakly continuous forward solution -/

theorem top_dissipation (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (hν : 0 < D.invβ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T)
    (φc : Coeff d) (hφ : MemHs (m : ℝ) φc) (F : ℝ → Coeff d)
    (hF : IsForwardSolution D μ t φc F) (hw : WeakContinuousInHs (m : ℝ) F t) :
    ∃ Kd : ℝ, ∀ S : Finset (Lattice d), ∑ k ∈ S,
      ∫ σ in (0 : ℝ)..t, sobWeight ((m : ℝ) + 1) k * ‖F σ k‖ ^ 2 ≤ Kd := by
  have ht0 : 0 ≤ t := ht.1.le
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨C, hC, hmain⟩ := energy_form_estimate hd s hs0 hsd m R MB Λ VB
  set Λm := R.lambdaM C ν₀ (thetaOrder d s) with hΛm
  obtain ⟨c, hc0, hc⟩ := gradDeriv_sum_lower (d := d) m
  obtain ⟨lam, q, hlq⟩ : ∃ (lam : Fin d → ℝ) (q : Fin d → Euc d),
      R.IsR2 → IsSymDiag D.M lam q := by
    by_cases hR : R.IsR2
    · obtain ⟨lam, q, h⟩ := exists_symDiag (regime_symNonpos hR hA.regime)
      exact ⟨lam, q, fun _ => h⟩
    · exact ⟨0, fun _ => 0, fun h => absurd h hR⟩
  have hreal : ∀ (φ' : Coeff d), MemHs (m : ℝ) φ' → IsRealCoeff φ' → ∀ (n : ℕ) (F' : ℝ → Coeff d),
      IsGalSol D μ t n φ' F' →
        (∀ τ ∈ Set.Icc 0 t, hsNorm (m : ℝ) (F' τ) ≤ Real.exp (Λm * τ) * hsNorm (m : ℝ) φ') ∧
        ∫ τ in (0 : ℝ)..t, hsNormSq ((m : ℝ) + 1) (F' τ) ≤
          dissConst c D.invβ Λm t * hsNormSq (m : ℝ) φ' := by
    intro φ' h1 h2 n F' hF'
    exact galSol_dissipation hA.hμ hA.hV hν ht h2 h1 hF' Λm c hc0 hc
      (fun r hr G hG hGt =>
        ((hmain D ν₀ T μ hA lam q hlq r hr n G hG hGt).2).trans
          (energyRHS_le_grad R _ D m lam q hd (fun hR l => (hlq hR).nonneg l) (μ r) G))
  have hex : ∀ n, ∃ F' : ℝ → Coeff d, IsGalSol D μ t n φc F' ∧
      (∀ τ ∈ Set.Icc 0 t, hsNorm (m : ℝ) (F' τ) ≤ Real.exp (Λm * τ) * hsNorm (m : ℝ) φc) ∧
      ∫ τ in (0 : ℝ)..t, hsNormSq ((m : ℝ) + 1) (F' τ) ≤
        dissConst c D.invβ Λm t * hsNormSq (m : ℝ) φc := fun n =>
    galSol_complex_dissipation hA.hμ hA.hV ht (fun τ => Real.exp (Λm * τ))
      (fun τ => (Real.exp_pos _).le) _ hreal n φc hφ
  choose Fn hFn hFb hFi using hex
  set Bs := Real.exp (|Λm| * t) * hsNorm (m : ℝ) φc with hBs
  have hB : ∀ n, ∀ τ ∈ Set.Icc 0 t, hsNorm (m : ℝ) (Fn n τ) ≤ Bs := by
    intro n τ hτ
    refine (hFb n τ hτ).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_)
      (Real.sqrt_nonneg _))
    calc Λm * τ ≤ |Λm| * τ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ.1
      _ ≤ |Λm| * t := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)
  obtain ⟨ψ, G, hψ, hconv, hGsol, hGw, -⟩ := galerkin_limit_core D μ m hm Λ VB T hA.hμ hA.hV t ht
    φc Fn (fun n => (hFn n).trig) (fun n k => (hFn n).cont k)
    (fun n k τ hτ => (hFn n).eq k τ hτ) Bs hB
  have huniq := forward_unique_core hd s hs0 hsd m R MB Λ VB D ν₀ T μ hA t ht φc F G hF
    (weakContinuousInHs_mono hm1 hw) hGsol (weakContinuousInHs_mono hm1 hGw)
  refine ⟨dissConst c D.invβ Λm t * hsNormSq (m : ℝ) φc, fun S => ?_⟩
  have hFG : ∀ k, ∫ σ in (0 : ℝ)..t, sobWeight ((m : ℝ) + 1) k * ‖F σ k‖ ^ 2 =
      ∫ σ in (0 : ℝ)..t, sobWeight ((m : ℝ) + 1) k * ‖G σ k‖ ^ 2 := by
    intro k
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [Set.uIcc_of_le ht0] at hσ
    simp only [huniq σ hσ]
  simp_rw [hFG]
  have hlim : Tendsto (fun n => ∑ k ∈ S,
      ∫ σ in (0 : ℝ)..t, sobWeight ((m : ℝ) + 1) k * ‖Fn (ψ n) σ k‖ ^ 2) atTop
      (𝓝 (∑ k ∈ S, ∫ σ in (0 : ℝ)..t, sobWeight ((m : ℝ) + 1) k * ‖G σ k‖ ^ 2)) :=
    tendsto_finsetSum S fun k _ => limit_integral_coord ht0 (m : ℝ) Fn G ψ (Bs ^ 2) hconv
      (fun n k => (hFn n).cont k) (fun n τ => isTrigPoly_memHs ((hFn n).trig τ) _)
      (fun n τ hτ => (Real.sqrt_le_iff.mp ((hB n τ hτ).trans le_rfl)).2) k
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  have hcn : ∀ k, ContinuousOn (fun σ => sobWeight ((m : ℝ) + 1) k * ‖Fn (ψ n) σ k‖ ^ 2)
      (Set.Icc 0 t) := fun k => continuousOn_const.mul (((hFn (ψ n)).cont k).norm.pow 2)
  rw [← intervalIntegral.integral_finsetSum (fun k _ => (hcn k).intervalIntegrable_of_Icc ht0)]
  refine le_trans (intervalIntegral.integral_mono_on ht0
    ((continuousOn_finsetSum S fun k _ => hcn k).intervalIntegrable_of_Icc ht0) ((galSol_hsNormSq_continuousOn (hFn (ψ n)) _).intervalIntegrable_of_Icc ht0) (fun σ hσ => ?_)) (hFi (ψ n))
  exact sum_le_hsNormSq (isTrigPoly_memHs ((hFn (ψ n)).trig σ) _) S

end HRS.PDE.TRA

namespace HRS.PDE

variable {d : ℕ}

/-- **Strong time continuity at the top level** (Proposition 3.9, `C([0,t];H^m)`): a forward
solution in `C_w([0,t];H^m)` with `H^m` datum is norm-continuous in `H^m`.  The proof combines the
viscous dissipation bound `L²(0,t;H^{m+1})` (Galerkin approximation, uniqueness), the Fourier-side
energy identity `|F̂_k(τ)|² = |φ̂_k|² + ∫_0^τ 2 Re(conj F̂_k ĝ_k)` with the pairing of
`H^{m+1}` against `H^{m-1}`, and weak continuity. -/
theorem forward_continuousInHs_top (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (hm : 1 ≤ m) (R : Regime) (MB Λ VB : ℝ) (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (hA : AdjointData s m R MB Λ VB D ν₀ T μ) (hν : 0 < D.invβ) (t : ℝ) (ht : t ∈ Set.Ioc 0 T)
    (φc : Coeff d) (hφ : MemHs m φc) (F : ℝ → Coeff d) (hF : IsForwardSolution D μ t φc F)
    (hw : WeakContinuousInHs m F t) :
    ContinuousInHs m F t := by
  obtain ⟨Kd, hKd⟩ := TRA.top_dissipation hd s hs0 hsd m hm R MB Λ VB D ν₀ T μ hA hν t ht φc hφ F
    hF hw
  exact TRA.continuousInHs_of_weak_norm hw
    (TRA.normSq_continuousOn hd s hs0 hsd m hm hA ht hφ hF hw Kd hKd)

end HRS.PDE
