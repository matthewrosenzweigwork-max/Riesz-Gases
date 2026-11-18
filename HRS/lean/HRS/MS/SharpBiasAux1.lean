import HRS.MS.SuppU12
import HRS.MS.WrMargBAux2

/-!
# HRS.MS.SharpBiasAux1 -- S7.1 `sharp_bias`: `L²(μ)` toolbox and the response bound

Packet S71, namespace `HRS.MS.S71`, helper prefix `s71_`.  Abstract (cavity-free) part of the proof of
`HRS.Whole.sharp_bias` (TeX S L5847-5917, "Solving the first-marginal response"):

* elementary `L²(μ)` facts for a probability measure `μ` (triangle inequality, domination, centring `P_μ`,
  Cauchy-Schwarz for `l2Inner`);
* linearity of `K_μ` on `L²_0(μ)` (through the `Lp` realisation of `Q34`);
* existence of the response `R P_μ ψ` for every `ψ ∈ L²(μ)` (`s71_resp_spec`);
* `s71_main_bound`: if `z ∈ L²_0(μ)` solves `z + β K_μ z = P_μ G` then
  `‖z/δ - c₀ R P_μ ρ‖ ≤ ‖G/δ - c₀ ρ‖` (positivity of `K_μ`, i.e. `‖R‖ ≤ 1`, `‖P_μ‖ ≤ 1`);
* `s71_euler_to_response`: a pointwise Euler equation `z + β (g*(zμ)) = H + k` (`k` constant) with
  `z ∈ L²_0` gives `z + β K_μ z = P_μ H`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Whole.S71


variable {d : ℕ} {s : ℝ}

/-! ### Centering -/

theorem s71_integral_projMean {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : Integrable f μ) : ∫ x, projMean μ f x ∂μ = 0 := by
  simp only [projMean, pair]
  rw [integral_sub hf (integrable_const _), integral_const]
  simp

theorem s71_memL2Zero_projMean {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : MemLp f 2 μ) : MemL2Zero μ (projMean μ f) :=
  ⟨hf.sub (memLp_const _), s71_integral_projMean (hf.integrable one_le_two)⟩

theorem s71_projMean_idem {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : Integrable f μ) : projMean μ (projMean μ f) = projMean μ f := by
  funext x
  have h := s71_integral_projMean hf
  simp only [projMean, pair] at h ⊢
  rw [h]
  ring

theorem s71_l2Norm_projMean_le {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : MemLp f 2 μ) : l2Norm μ (projMean μ f) ≤ l2Norm μ f := by
  unfold l2Norm
  apply Real.sqrt_le_sqrt
  have h1 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have h2 : Integrable f μ := hf.integrable one_le_two
  set c := pair μ f with hc
  have hcf : ∫ x, f x ∂μ = c := rfl
  have e : (fun x => projMean μ f x ^ 2) = fun x => f x ^ 2 - 2 * c * f x + c ^ 2 := by
    funext x
    simp only [projMean]
    rw [← hc]
    ring
  have hI : Integrable (fun x => f x ^ 2 - 2 * c * f x) μ := h1.sub (h2.const_mul _)
  have hJ : Integrable (fun x => 2 * c * f x) μ := h2.const_mul _
  rw [e, integral_add hI (integrable_const _), integral_sub h1 hJ, integral_const_mul, hcf,
    integral_const]
  simp
  nlinarith [sq_nonneg c]

/-! ### Norms -/

theorem s71_l2Norm_add_le {μ : Measure (Euc d)} {f g : Euc d → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : l2Norm μ (fun x => f x + g x) ≤ l2Norm μ f + l2Norm μ g := by
  have hF := MemLp.coeFn_toLp hf
  have hG := MemLp.coeFn_toLp hg
  have hfg : (fun x => f x + g x) =ᵐ[μ] ((hf.toLp f + hg.toLp g : Lp ℝ 2 μ) : Euc d → ℝ) := by
    filter_upwards [Lp.coeFn_add (hf.toLp f) (hg.toLp g), hF, hG] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
  rw [Q34.l2Norm_eq hfg, Q34.l2Norm_eq hF.symm, Q34.l2Norm_eq hG.symm]
  exact norm_add_le _ _

theorem s71_l2Norm_sub_le {μ : Measure (Euc d)} {f g : Euc d → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : l2Norm μ (fun x => f x - g x) ≤ l2Norm μ f + l2Norm μ g := by
  have h := s71_l2Norm_add_le hf (hg.const_mul (-1))
  have e1 : (fun x => f x + (-1 * g x)) = fun x => f x - g x := by funext x; ring
  have e2 : l2Norm μ (fun x => -1 * g x) = l2Norm μ g := by
    rw [HRS.MS.SuppN.u12_l2Norm_smul]; simp
  simp only [e2] at h
  simpa only [e1] using h

theorem s71_l2Norm_mono {μ : Measure (Euc d)} {f g : Euc d → ℝ} (hg : MemLp g 2 μ)
    (h : ∀ x, |f x| ≤ |g x|) : l2Norm μ f ≤ l2Norm μ g := by
  unfold l2Norm
  apply Real.sqrt_le_sqrt
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hg.integrable_sq
    (Eventually.of_forall fun x => ?_)
  have := h x
  calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
    _ ≤ |g x| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = g x ^ 2 := sq_abs _

theorem s71_l2Norm_le_of_bound {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ x, |f x| ≤ B) : l2Norm μ f ≤ B := by
  unfold l2Norm
  rw [Real.sqrt_le_left hB]
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
    (integrable_const (B ^ 2)) (Eventually.of_forall fun x => ?_)).trans (by simp)
  calc f x ^ 2 = |f x| ^ 2 := (sq_abs _).symm
    _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (h x) 2

theorem s71_l2Norm_const_mul {μ : Measure (Euc d)} (c : ℝ) (f : Euc d → ℝ) :
    l2Norm μ (fun x => c * f x) = |c| * l2Norm μ f :=
  HRS.MS.SuppN.u12_l2Norm_smul μ c f

theorem s71_l2Norm_nonneg (μ : Measure (Euc d)) (f : Euc d → ℝ) : 0 ≤ l2Norm μ f :=
  Real.sqrt_nonneg _

theorem s71_abs_l2Inner_le {μ : Measure (Euc d)} {f g : Euc d → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : |l2Inner μ f g| ≤ l2Norm μ f * l2Norm μ g := by
  have hF := MemLp.coeFn_toLp hf
  have hG := MemLp.coeFn_toLp hg
  rw [Q34.l2Inner_eq hF.symm hG.symm, Q34.l2Norm_eq hF.symm, Q34.l2Norm_eq hG.symm]
  exact abs_real_inner_le_norm _ _

/-! ### The operator `K_μ` and the response -/

section Response

variable {ρ : Euc d → ℝ} {M : ℝ}

theorem s71_Kop_lin (hq : Q34.Q34Hyp d s ρ M) [IsProbabilityMeasure (withDensityReal ρ)]
    {f h : Euc d → ℝ} (hf : MemL2Zero (withDensityReal ρ) f) (hh : MemL2Zero (withDensityReal ρ) h)
    (a b : ℝ) :
    Kop (rieszKernel d s) (withDensityReal ρ) (fun x => a * f x + b * h x) =ᵐ[withDensityReal ρ]
      fun x => a * Kop (rieszKernel d s) (withDensityReal ρ) f x +
        b * Kop (rieszKernel d s) (withDensityReal ρ) h x := by
  obtain ⟨F, hF, hPF⟩ := Q34.exists_class hf
  obtain ⟨H, hH, hPH⟩ := Q34.exists_class hh
  have hu : (fun x => a * f x + b * h x) =ᵐ[withDensityReal ρ] ((a • F + b • H : Lp ℝ 2 _) : Euc d → ℝ) := by
    filter_upwards [Lp.coeFn_add (a • F) (b • H), Lp.coeFn_smul a F, Lp.coeFn_smul b H, hF, hH]
      with x h1 h2 h3 h4 h5
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply, h4, h5]
    rfl
  have hP : Q34.Pc (withDensityReal ρ) (a • F + b • H) = a • F + b • H := by
    rw [map_add, map_smul, map_smul, hPF, hPH]
  have k1 := Q34.kop_class hq hu hP
  have k2 := Q34.kop_class hq hF hPF
  have k3 := Q34.kop_class hq hH hPH
  filter_upwards [k1, k2, k3, Lp.coeFn_add (a • Q34.Kc hq F) (b • Q34.Kc hq H),
    Lp.coeFn_smul a (Q34.Kc hq F), Lp.coeFn_smul b (Q34.Kc hq H)] with x e1 e2 e3 e4 e5 e6
  rw [e1, map_add, map_smul, map_smul, e4, Pi.add_apply, e5, e6, Pi.smul_apply, Pi.smul_apply, e2, e3]
  rfl

/-- `‖z‖ ≤ ‖P_μ G‖` when `z ∈ L²_0` solves `z + β K_μ z = P_μ G`. -/
theorem s71_response_bound (hq : Q34.Q34Hyp d s ρ M) [IsProbabilityMeasure (withDensityReal ρ)]
    {β : ℝ} (hβ : 0 < β) {W G : Euc d → ℝ} (hW : MemL2Zero (withDensityReal ρ) W)
    (hG : MemLp G 2 (withDensityReal ρ))
    (hWG : ∀ᵐ x ∂(withDensityReal ρ),
      W x + β * Kop (rieszKernel d s) (withDensityReal ρ) W x = projMean (withDensityReal ρ) G x) :
    l2Norm (withDensityReal ρ) W ≤ l2Norm (withDensityReal ρ) G := by
  obtain ⟨F, hF, hPF⟩ := Q34.exists_class hW
  have k := Q34.kop_class hq hF hPF
  set V : Lp ℝ 2 (withDensityReal ρ) := F + β • Q34.Kc hq F with hV
  have hVa : projMean (withDensityReal ρ) G =ᵐ[withDensityReal ρ] (V : Euc d → ℝ) := by
    filter_upwards [hWG, k, hF, Lp.coeFn_add F (β • Q34.Kc hq F), Lp.coeFn_smul β (Q34.Kc hq F)]
      with x h1 h2 h3 h4 h5
    rw [← h1, hV, h4, Pi.add_apply, h5, Pi.smul_apply, h2, h3]
    rfl
  have hnV : l2Norm (withDensityReal ρ) (projMean (withDensityReal ρ) G) = ‖V‖ :=
    Q34.l2Norm_eq hVa
  have hnF : l2Norm (withDensityReal ρ) W = ‖F‖ := Q34.l2Norm_eq hF
  have h1 : ‖F‖ ^ 2 ≤ inner ℝ V F := by
    rw [hV, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    have := Q34.Kc_pos hq F
    simp only [conj_trivial]
    nlinarith [mul_nonneg hβ.le this]
  have h2 : inner ℝ V F ≤ ‖V‖ * ‖F‖ := real_inner_le_norm _ _
  have h3 : ‖F‖ ≤ ‖V‖ := by
    by_cases h0 : ‖F‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      nlinarith
  rw [hnF]
  refine h3.trans ?_
  rw [← hnV]
  exact s71_l2Norm_projMean_le hG

theorem s71_memLp_div {μ : Measure (Euc d)} {f : Euc d → ℝ} (hf : MemLp f 2 μ) (δ : ℝ) :
    MemLp (fun x => f x / δ) 2 μ := by
  have := hf.const_mul δ⁻¹
  simpa only [div_eq_inv_mul] using this

theorem s71_isResponse_projMean {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {g : Euc d → ℝ}
    {β : ℝ} {ψ : Euc d → ℝ} (hψ : Integrable ψ μ) {h : Euc d → ℝ} :
    IsResponse g μ β (projMean μ ψ) h ↔ IsResponse g μ β ψ h := by
  unfold IsResponse
  rw [s71_projMean_idem hψ]

theorem s71_resp_spec (hq : Q34.Q34Hyp d s ρ M) [IsProbabilityMeasure (withDensityReal ρ)]
    {β : ℝ} (hβ : 0 < β) {ψ : Euc d → ℝ} (hψ : MemLp ψ 2 (withDensityReal ρ)) :
    IsResponse (rieszKernel d s) (withDensityReal ρ) β ψ
      (responseInverse (rieszKernel d s) (withDensityReal ρ) β ψ) := by
  have hex : ∃ h, IsResponse (rieszKernel d s) (withDensityReal ρ) β ψ h := by
    obtain ⟨h, hh⟩ := (Q34.partD hq hβ (s71_memL2Zero_projMean hψ)).1
    exact ⟨h, (s71_isResponse_projMean (hψ.integrable one_le_two)).1 hh⟩
  unfold responseInverse
  rw [dif_pos hex]
  exact hex.choose_spec

theorem s71_main_bound (hq : Q34.Q34Hyp d s ρ M) [IsProbabilityMeasure (withDensityReal ρ)]
    {β : ℝ} (hβ : 0 < β) {z G : Euc d → ℝ} (hz : MemL2Zero (withDensityReal ρ) z)
    (hG : MemLp G 2 (withDensityReal ρ)) {δ : ℝ} (hδ : 0 < δ) (c₀ : ℝ)
    (hzG : ∀ᵐ x ∂(withDensityReal ρ),
      z x + β * Kop (rieszKernel d s) (withDensityReal ρ) z x = projMean (withDensityReal ρ) G x) :
    l2Norm (withDensityReal ρ) (fun x => z x / δ -
        c₀ * responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ x) ≤
      l2Norm (withDensityReal ρ) (fun x => G x / δ - c₀ * ρ x) := by
  set μ := withDensityReal ρ with hμ
  have hρL : MemLp ρ 2 μ := by
    have hM0 : 0 ≤ M := (hq.hρ.nonneg 0).trans (hq.hM 0)
    exact MemLp.of_bound hq.hρ.measurable.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq.hρ.nonneg x)]
      exact hq.hM x)
  set r := responseInverse (rieszKernel d s) μ β ρ with hr
  obtain ⟨hr0, hr1⟩ := s71_resp_spec hq hβ hρL
  have hW : MemL2Zero μ (fun x => z x / δ - c₀ * r x) := by
    refine ⟨(s71_memLp_div hz.1 δ).sub (hr0.1.const_mul c₀), ?_⟩
    rw [integral_sub ((s71_memLp_div hz.1 δ).integrable one_le_two) ((hr0.1.const_mul c₀).integrable one_le_two),
      integral_div, integral_const_mul, hz.2, hr0.2]
    simp
  have hlin := s71_Kop_lin hq hz hr0 (1 / δ) (-c₀)
  have e1 : (fun x => z x / δ - c₀ * r x) = fun x => 1 / δ * z x + -c₀ * r x := by
    funext x; ring
  have hG' : MemLp (fun x => G x / δ - c₀ * ρ x) 2 μ := (s71_memLp_div hG δ).sub (hρL.const_mul c₀)
  refine s71_response_bound hq hβ hW hG' ?_
  rw [e1]
  filter_upwards [hlin, hzG, hr1] with x h1 h2 h3
  rw [h1]
  have hp : projMean μ (fun x => G x / δ - c₀ * ρ x) x =
      1 / δ * projMean μ G x - c₀ * projMean μ ρ x := by
    simp only [projMean, pair]
    rw [integral_sub ((s71_memLp_div hG δ).integrable one_le_two) ((hρL.const_mul c₀).integrable one_le_two),
      integral_div, integral_const_mul]
    ring
  rw [hp, ← h2, ← h3]
  ring

/-- Pointwise Euler equation to the projected response equation. -/
theorem s71_euler_to_response (hq : Q34.Q34Hyp d s ρ M) [IsProbabilityMeasure (withDensityReal ρ)]
    {β : ℝ} (hβ : 0 < β) {z H : Euc d → ℝ} (hz : MemL2Zero (withDensityReal ρ) z)
    (hH : Integrable H (withDensityReal ρ)) (k : ℝ)
    (heq : ∀ x, z x + β * (∫ y, rieszKernel d s (x - y) * z y ∂(withDensityReal ρ)) = H x + k) :
    ∀ᵐ x ∂(withDensityReal ρ),
      z x + β * Kop (rieszKernel d s) (withDensityReal ρ) z x = projMean (withDensityReal ρ) H x := by
  set μ := withDensityReal ρ with hμ
  set S : Euc d → ℝ := fun x => ∫ y, rieszKernel d s (x - y) * z y ∂μ with hS
  have hzi : Integrable z μ := hz.1.integrable one_le_two
  have hSe : ∀ x, S x = (H x + k - z x) / β := by
    intro x
    have := heq x
    simp only [hS]
    field_simp
    linarith
  have hSi : Integrable S μ := by
    have : S = fun x => (H x + k - z x) / β := funext hSe
    rw [this]
    exact ((hH.add (integrable_const k)).sub hzi).div_const β
  have hint : ∫ x, S x ∂μ = (∫ x, H x ∂μ + k) / β := by
    have : S = fun x => (H x + k - z x) / β := funext hSe
    have hA : Integrable (fun x => H x + k) μ := hH.add (integrable_const k)
    rw [this, integral_div, integral_sub hA hzi, integral_add hH (integrable_const k), hz.2]
    simp
  refine Eventually.of_forall fun x => ?_
  have hK : Kop (rieszKernel d s) μ z x = S x - ∫ y, S y ∂μ := rfl
  rw [hK, hint, hSe x]
  simp only [projMean, pair]
  field_simp
  ring

end Response

end HRS.Whole.S71
