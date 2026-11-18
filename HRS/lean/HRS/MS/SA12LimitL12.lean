import HRS.MS.SA12CcDenseH
import HRS.MP.HNegInfra

/-!
# S.A.12 L12: the negative-order norm from pairings with smooth compactly supported tests
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MP.HNegInfra HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem sa12l12_measure_le {q : ℝ} (hq : 0 ≤ q) : sobolevMeasure d q ≤ (volume : Measure (Euc d)) := by
  rw [Measure.le_iff']
  intro s
  unfold sobolevMeasure
  rw [withDensity_apply' _ s]
  calc ∫⁻ ξ in s, sobolevWeight d q ξ ≤ ∫⁻ ξ in s, 1 := by
        refine lintegral_mono fun ξ => ?_
        unfold sobolevWeight
        rw [← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_wt ξ) (by linarith)
    _ = volume s := by simp

/-- The Fourier-side element of `H^{-q}` attached to an `L²` function. -/
theorem sa12l12_element {q : ℝ} (hq : 0 ≤ q) {u : Euc d → ℝ} (hu : MemLp u 2 volume) :
    ∃ F : HNeg d q, (∀ᵐ ξ : Euc d, F.fourier ξ = fourierL2 u ξ) ∧
      Integrable (fun ξ => wt ξ ^ (-q) * ‖fourierL2 u ξ‖ ^ 2) volume ∧
      ‖F‖ ^ 2 = ∫ ξ, wt ξ ^ (-q) * ‖fourierL2 u ξ‖ ^ 2 := by
  have hmem : MemLp (fourierL2 u) 2 (sobolevMeasure d q) :=
    (memLp_fourierL2 hu).mono_measure (sa12l12_measure_le hq)
  set G : Lp ℂ 2 (sobolevMeasure d q) := hmem.toLp _ with hG
  have hGae : ∀ᵐ ξ : Euc d, (G : Euc d → ℂ) ξ = fourierL2 u ξ :=
    (mhn_ae_mu_iff _).1 hmem.coeFn_toLp
  have hGmem : G ∈ HNegSubmodule d q := by
    apply mhn_mem_of_conj
    rw [mhn_ae_mu_iff]
    have h1 := (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving.ae hGae
    filter_upwards [hGae, h1, fourierL2_neg hu] with ξ a b c
    rw [b, c, a]
  have hwm : Measurable (sobolevWeight d q : Euc d → ℝ≥0∞) := mhn_measurable_weight
  have hwlt : ∀ᵐ ξ : Euc d, sobolevWeight d q ξ < ⊤ :=
    Filter.Eventually.of_forall fun ξ => ENNReal.ofReal_lt_top
  have hGsq : Integrable (fun ξ => ‖(G : Euc d → ℂ) ξ‖ ^ 2) (sobolevMeasure d q) :=
    (Lp.memLp G).norm.integrable_sq
  have hGsq' : Integrable (fun ξ => (sobolevWeight d q ξ).toReal • ‖(G : Euc d → ℂ) ξ‖ ^ 2)
      volume := (integrable_withDensity_iff_integrable_smul' hwm hwlt).1 hGsq
  have hrho : ∀ ξ : Euc d, (sobolevWeight d q ξ).toReal = wt ξ ^ (-q) := fun ξ => mhn_toReal_weight ξ
  have hint : Integrable (fun ξ => wt ξ ^ (-q) * ‖fourierL2 u ξ‖ ^ 2) volume := by
    refine hGsq'.congr ?_
    filter_upwards [hGae] with ξ hξ
    simp only [smul_eq_mul, hrho]
    rw [hξ]
  refine ⟨⟨G, hGmem⟩, hGae, hint, ?_⟩
  have h1 : ‖G‖ ^ 2 = ∫ ξ, ‖(G : Euc d → ℂ) ξ‖ ^ 2 ∂(sobolevMeasure d q) := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) G
    rw [MeasureTheory.L2.inner_def] at this
    have h2 : (∫ ξ, inner ℂ ((G : Euc d → ℂ) ξ) ((G : Euc d → ℂ) ξ) ∂(sobolevMeasure d q)) =
        ((∫ ξ, ‖(G : Euc d → ℂ) ξ‖ ^ 2 ∂(sobolevMeasure d q) : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      beta_reduce
      rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
    rw [h2] at this
    have h3 := Complex.ofReal_injective (by simpa using this.symm : ((‖G‖ ^ 2 : ℝ) : ℂ) = _)
    exact h3
  show ‖G‖ ^ 2 = _
  rw [h1]
  have hdens : ∫ ξ, ‖(G : Euc d → ℂ) ξ‖ ^ 2 ∂(sobolevMeasure d q) =
      ∫ ξ, (sobolevWeight d q ξ).toReal • ‖(G : Euc d → ℂ) ξ‖ ^ 2 :=
    integral_withDensity_eq_integral_toReal_smul hwm hwlt (fun ξ => ‖(G : Euc d → ℂ) ξ‖ ^ 2)
  rw [hdens]
  refine integral_congr_ae ?_
  filter_upwards [hGae] with ξ hξ
  simp only [smul_eq_mul, hrho]
  rw [hξ]

theorem sa12l12_norm_sq {f : Euc d → ℝ} (hf : MemLp f 2 volume) :
    (eLpNorm f 2 volume).toReal ^ 2 = ∫ x, f x ^ 2 := by
  have h1 := sa12x_inner_toLp hf hf
  rw [real_inner_self_eq_norm_sq, Lp.norm_toLp] at h1
  rw [h1]
  congr 1; funext x; ring

theorem sa12l12_sq_split (s : ℝ) {f g : Euc d → ℝ} (hf : HRS.PDE.ToolboxRd.MemSobolev s f) (hg : HRS.PDE.ToolboxRd.MemSobolev s g)
    {t : ℝ} (ht : 0 < t) :
    HRS.PDE.ToolboxRd.MemSobolev s (fun x => f x - g x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq s (fun x => f x - g x) ≤
        (1 + t) * HRS.PDE.ToolboxRd.sobolevNormSq s f + (1 + 1 / t) * HRS.PDE.ToolboxRd.sobolevNormSq s g := by
  have hsub := fourierL2_sub hf.1 hg.1
  have hpt : ∀ᵐ ξ : Euc d, wt ξ ^ s * ‖fourierL2 (fun x => f x - g x) ξ‖ ^ 2 ≤
      (1 + t) * (wt ξ ^ s * ‖fourierL2 f ξ‖ ^ 2) + (1 + 1 / t) * (wt ξ ^ s * ‖fourierL2 g ξ‖ ^ 2) := by
    filter_upwards [hsub] with ξ hξ
    rw [hξ]
    have hw : 0 ≤ wt ξ ^ s := (Real.rpow_pos_of_pos (wt_pos ξ) s).le
    have h1 : ‖fourierL2 f ξ - fourierL2 g ξ‖ ≤ ‖fourierL2 f ξ‖ + ‖fourierL2 g ξ‖ := norm_sub_le _ _
    have h2 : ‖fourierL2 f ξ - fourierL2 g ξ‖ ^ 2 ≤
        (1 + t) * ‖fourierL2 f ξ‖ ^ 2 + (1 + 1 / t) * ‖fourierL2 g ξ‖ ^ 2 := by
      set x := ‖fourierL2 f ξ‖
      set y := ‖fourierL2 g ξ‖
      have hx : 0 ≤ x := norm_nonneg _
      have hy : 0 ≤ y := norm_nonneg _
      have h3 : 2 * x * y ≤ t * x ^ 2 + 1 / t * y ^ 2 := by
        have h4 : t * (2 * x * y) ≤ t * (t * x ^ 2 + 1 / t * y ^ 2) := by
          have : t * (1 / t * y ^ 2) = y ^ 2 := by field_simp
          nlinarith [sq_nonneg (t * x - y), this]
        exact le_of_mul_le_mul_left h4 ht
      calc ‖fourierL2 f ξ - fourierL2 g ξ‖ ^ 2 ≤ (x + y) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ _ := by nlinarith [h3]
    calc wt ξ ^ s * ‖fourierL2 f ξ - fourierL2 g ξ‖ ^ 2
        ≤ wt ξ ^ s * ((1 + t) * ‖fourierL2 f ξ‖ ^ 2 + (1 + 1 / t) * ‖fourierL2 g ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hw
      _ = _ := by ring
  have hbound : Integrable (fun ξ : Euc d => (1 + t) * (wt ξ ^ s * ‖fourierL2 f ξ‖ ^ 2) +
      (1 + 1 / t) * (wt ξ ^ s * ‖fourierL2 g ξ‖ ^ 2)) volume :=
    (hf.2.const_mul _).add (hg.2.const_mul _)
  have hmeas : AEStronglyMeasurable (fun ξ : Euc d => wt ξ ^ s * ‖fourierL2 (fun x => f x - g x) ξ‖ ^ 2) volume :=
    aesm_wt_mul (aestronglyMeasurable_fourierL2 (hf.1.sub hg.1)) s
  have hint : Integrable (fun ξ : Euc d => wt ξ ^ s * ‖fourierL2 (fun x => f x - g x) ξ‖ ^ 2) volume := by
    refine Integrable.mono' hbound hmeas ?_
    filter_upwards [hpt] with ξ hξ
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_pos_of_pos (wt_pos ξ) s).le (sq_nonneg _))]
    exact hξ
  refine ⟨⟨hf.1.sub hg.1, hint⟩, ?_⟩
  show ∫ ξ, wt ξ ^ s * ‖fourierL2 (fun x => f x - g x) ξ‖ ^ 2 ≤ _
  calc ∫ ξ, wt ξ ^ s * ‖fourierL2 (fun x => f x - g x) ξ‖ ^ 2
      ≤ ∫ ξ, ((1 + t) * (wt ξ ^ s * ‖fourierL2 f ξ‖ ^ 2) +
          (1 + 1 / t) * (wt ξ ^ s * ‖fourierL2 g ξ‖ ^ 2)) := integral_mono_ae hint hbound hpt
    _ = _ := by
        have hI1 : Integrable (fun ξ : Euc d => (1 + t) * (wt ξ ^ s * ‖fourierL2 f ξ‖ ^ 2)) volume :=
          hf.2.const_mul _
        have hI2 : Integrable (fun ξ : Euc d => (1 + 1 / t) * (wt ξ ^ s * ‖fourierL2 g ξ‖ ^ 2)) volume :=
          hg.2.const_mul _
        rw [integral_add hI1 hI2, integral_const_mul, integral_const_mul]
        rfl

theorem sa12l12_S_mono {s s' : ℝ} (h : s' ≤ s) {f : Euc d → ℝ}
    (hf : HRS.PDE.ToolboxRd.MemSobolev s f) :
    HRS.PDE.ToolboxRd.sobolevNormSq s' f ≤ HRS.PDE.ToolboxRd.sobolevNormSq s f := by
  have hf' := memSobolev_mono h hf
  refine integral_mono hf'.2 hf.2 fun ξ => ?_
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (one_le_wt ξ) h) (sq_nonneg _)

theorem sa12l12_S_nonneg (s : ℝ) (f : Euc d → ℝ) : 0 ≤ HRS.PDE.ToolboxRd.sobolevNormSq s f :=
  integral_nonneg fun ξ => by
    have := wt_pos (d := d) ξ
    positivity

theorem sa12l12_test_ext {q A : ℝ} (hq : 0 ≤ q) (hA : 0 ≤ A) {u : Euc d → ℝ} (hu : MemLp u 2 volume)
    (hpair : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      |∫ x, u x * ψ x| ≤ A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq q ψ))
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hjets : ∀ j ≤ ⌈q⌉₊, Integrable (fun x => ‖iteratedFDeriv ℝ j φ x‖ ^ 2) volume)
    (hφS : HRS.PDE.ToolboxRd.MemSobolev q φ) :
    |∫ x, u x * φ x| ≤ A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq q φ) := by
  set N : ℕ := ⌈q⌉₊ with hN
  have hqN : q ≤ (N : ℝ) := Nat.le_ceil q
  obtain ⟨hmem, htend⟩ := sa12cc_remainder N hφ hjets
  have hφ2 : MemLp φ 2 volume := hφS.1
  set S : ℝ := HRS.PDE.ToolboxRd.sobolevNormSq q φ with hS
  set σ : ℝ → ℝ := fun a => HRS.PDE.ToolboxRd.sobolevNormSq (N : ℝ)
    (fun x => φ x - sa12cc_rho a x * φ x) with hσ
  have hσ0 : ∀ a, 0 ≤ σ a := fun a => sa12l12_S_nonneg _ _
  have hψ : ∀ a : ℝ, 1 ≤ a → IsCcInfty (fun x => sa12cc_rho a x * φ x) := fun a ha =>
    ⟨(sa12cc_rho_contDiff a).mul hφ, (sa12cc_rho_compact (by linarith)).mul_right⟩
  -- the pairing bound at level `a`
  have hpa : ∀ t : ℝ, 0 < t → ∀ a : ℝ, 1 ≤ a →
      |∫ x, u x * (sa12cc_rho a x * φ x)| ≤ A * Real.sqrt ((1 + t) * S + (1 + 1 / t) * σ a) := by
    intro t ht a ha
    refine (hpair _ (hψ a ha)).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hA)
    have hh : HRS.PDE.ToolboxRd.MemSobolev q (fun x => φ x - sa12cc_rho a x * φ x) :=
      memSobolev_mono hqN (hmem a ha)
    have hsp := (sa12l12_sq_split q hφS hh ht).2
    have e : (fun x => φ x - (φ x - sa12cc_rho a x * φ x)) = fun x => sa12cc_rho a x * φ x := by
      funext x; ring
    rw [e] at hsp
    refine hsp.trans ?_
    have := sa12l12_S_mono hqN (hmem a ha)
    have h2 : (1 + 1 / t) * HRS.PDE.ToolboxRd.sobolevNormSq q (fun x => φ x - sa12cc_rho a x * φ x) ≤
        (1 + 1 / t) * σ a := mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  -- the pairing with the remainder
  set Cu : ℝ := (eLpNorm u 2 volume).toReal with hCu
  have hE : ∀ a : ℝ, 1 ≤ a →
      |∫ x, u x * φ x| ≤ |∫ x, u x * (sa12cc_rho a x * φ x)| + Cu * Real.sqrt (σ a) := by
    intro a ha
    have hha : MemLp (fun x => φ x - sa12cc_rho a x * φ x) 2 volume := (hmem a ha).1
    have hpsi : MemLp (fun x => sa12cc_rho a x * φ x) 2 volume :=
      ((sa12cc_rho_contDiff (d := d) a).continuous.mul hφ.continuous).memLp_of_hasCompactSupport
        ((sa12cc_rho_compact (by linarith)).mul_right)
    have i1 : Integrable (fun x => u x * φ x) volume := hu.integrable_mul hφ2
    have i2 : Integrable (fun x => u x * (sa12cc_rho a x * φ x)) volume := hu.integrable_mul hpsi
    have i3 : Integrable (fun x => u x * (φ x - sa12cc_rho a x * φ x)) volume := hu.integrable_mul hha
    have e1 : ∫ x, u x * φ x = (∫ x, u x * (sa12cc_rho a x * φ x)) +
        ∫ x, u x * (φ x - sa12cc_rho a x * φ x) := by
      rw [← integral_add i2 i3]; congr 1; funext x; ring
    have hcs := sa12x_cs hu hha
    have hn : (eLpNorm (fun x => φ x - sa12cc_rho a x * φ x) 2 volume).toReal ≤ Real.sqrt (σ a) := by
      refine Real.le_sqrt_of_sq_le ?_
      rw [sa12l12_norm_sq hha]
      have h0 : ∫ x, (φ x - sa12cc_rho a x * φ x) ^ 2 =
          HRS.PDE.ToolboxRd.sobolevNormSq 0 (fun x => φ x - sa12cc_rho a x * φ x) := by
        rw [integral_sq_eq_norm_sq hha]
        unfold HRS.PDE.ToolboxRd.sobolevNormSq
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        simp
      rw [h0]
      exact sa12l12_S_mono (by positivity) (hmem a ha)
    calc |∫ x, u x * φ x| ≤ |∫ x, u x * (sa12cc_rho a x * φ x)| +
          |∫ x, u x * (φ x - sa12cc_rho a x * φ x)| := by rw [e1]; exact abs_add_le _ _
      _ ≤ _ := add_le_add le_rfl (hcs.trans (mul_le_mul_of_nonneg_left hn ENNReal.toReal_nonneg))
  -- pass to the limit in `a`, then in `t`
  have hσt : Tendsto σ atTop (𝓝 0) := htend
  have hlim : ∀ t : ℝ, 0 < t → |∫ x, u x * φ x| ≤ A * Real.sqrt ((1 + t) * S) := by
    intro t ht
    have hR : Tendsto (fun a : ℝ => A * Real.sqrt ((1 + t) * S + (1 + 1 / t) * σ a) +
        Cu * Real.sqrt (σ a)) atTop (𝓝 (A * Real.sqrt ((1 + t) * S) + Cu * Real.sqrt 0)) := by
      refine Tendsto.add ?_ ?_
      · exact ((Real.continuous_sqrt.tendsto _).comp
          (tendsto_const_nhds.add (hσt.const_mul (1 + 1 / t))) |>.const_mul A).congr'
          (Filter.Eventually.of_forall fun a => rfl) |> fun h => by simpa using h
      · exact ((Real.continuous_sqrt.tendsto _).comp hσt).const_mul Cu
    rw [Real.sqrt_zero, mul_zero, add_zero] at hR
    refine ge_of_tendsto hR ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    exact (hE a ha).trans (add_le_add (hpa t ht a ha) le_rfl)
  have hS0 : 0 ≤ S := sa12l12_S_nonneg q φ
  have hc : Tendsto (fun t : ℝ => A * Real.sqrt ((1 + t) * S)) (𝓝[>] 0)
      (𝓝 (A * Real.sqrt S)) := by
    have : Continuous fun t : ℝ => A * Real.sqrt ((1 + t) * S) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hc ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact hlim t ht

theorem sa12l12_phi_jets (h : mhn_Hc d) (j : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j (mhn_phi h) x‖ ^ 2) volume := by
  set U : SchwartzMap (Euc d) ℂ := mhn_U h with hU
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : Euc d, (1 + ‖x‖) ^ (d + 1) * ‖iteratedFDeriv ℝ j U x‖ ≤ C :=
    ⟨_, fun x => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (max (d + 1) j, max (d + 1) j))
      (le_max_left _ _) (le_max_right _ _) U x⟩
  have hφ : mhn_phi h = Complex.reCLM ∘ (U : Euc d → ℂ) := rfl
  have hUs : ContDiff ℝ ∞ (U : Euc d → ℂ) := U.smooth _
  have hnorm : ∀ x, ‖iteratedFDeriv ℝ j (mhn_phi h) x‖ ≤ ‖iteratedFDeriv ℝ j U x‖ := by
    intro x
    have h1 := Complex.reCLM.norm_iteratedFDeriv_comp_left (f := (U : Euc d → ℂ)) (x := x)
      (N := ∞) (n := j) hUs.contDiffAt (by exact_mod_cast le_top)
    have h2 : ‖(Complex.reCLM : ℂ →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
        simpa using Complex.abs_re_le_norm z
    rw [hφ]
    exact h1.trans (by nlinarith [norm_nonneg (iteratedFDeriv ℝ j U x), norm_nonneg (Complex.reCLM : ℂ →L[ℝ] ℝ)])
  have hr : (Module.finrank ℝ (Euc d) : ℝ) < 2 * ((d : ℝ) + 1) := by
    rw [finrank_euclideanSpace_fin]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hint := (integrable_one_add_norm (E := Euc d) (μ := volume) hr).const_mul (C ^ 2)
  have hcont : Continuous fun x => ‖iteratedFDeriv ℝ j (mhn_phi h) x‖ ^ 2 :=
    (((mhn_contDiff_phi h).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm).pow 2
  refine Integrable.mono' hint hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hpos : 0 < (1 + ‖x‖) := by positivity
  have h1 : ‖iteratedFDeriv ℝ j (mhn_phi h) x‖ ^ 2 ≤ ‖iteratedFDeriv ℝ j U x‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hnorm x) 2
  refine h1.trans ?_
  have h2 : ‖iteratedFDeriv ℝ j U x‖ * (1 + ‖x‖) ^ (d + 1) ≤ C := by
    rw [mul_comm]; exact hC x
  have h3 : (1 + ‖x‖) ^ (-(2 * ((d : ℝ) + 1))) = ((1 + ‖x‖) ^ (d + 1)) ⁻¹ ^ 2 := by
    rw [Real.rpow_neg hpos.le, show (2 * ((d : ℝ) + 1)) = ((2 * (d + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, inv_pow, ← pow_mul]
    congr 2; ring
  rw [h3]
  have hp : 0 < (1 + ‖x‖) ^ (d + 1) := by positivity
  have h4 : ‖iteratedFDeriv ℝ j U x‖ ≤ C * ((1 + ‖x‖) ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hp]; exact h2
  calc ‖iteratedFDeriv ℝ j U x‖ ^ 2 ≤ (C * ((1 + ‖x‖) ^ (d + 1))⁻¹) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h4 2
    _ = C ^ 2 * ((1 + ‖x‖) ^ (d + 1))⁻¹ ^ 2 := by rw [mul_pow]

-- BEGIN SA12.L12
theorem negative_norm_from_tests (hd : 1 ≤ d) (q A : ℝ) (hq : 0 ≤ q) (hA : 0 ≤ A)
    (u : Euc d → ℝ) (hu : MemLp u 2 volume)
    (hpair : ∀ ψ : Euc d → ℝ, IsCcInfty ψ →
      |∫ x, u x * ψ x| ≤ A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq q ψ)) :
    sobolevNormE (-q) u ≤ ENNReal.ofReal A := by
  obtain ⟨F, hFae, hint, hFnorm⟩ := sa12l12_element hq hu
  obtain ⟨s, hsR, hs1, hnorm⟩ := mhn_norming_abstract
    (LinearMap.range (mhn_rep (d := d) q)) (mhn_range_orth_bot q)
  have hFA : ‖F‖ ≤ A := by
    rw [hnorm F]
    refine ciSup_le fun n => ?_
    obtain ⟨h, hh⟩ := LinearMap.mem_range.1 (hsR n)
    rw [← hh, ← mhn_pairing_phi]
    have hpair' : HNeg.pairing (mhn_phi h) F = ∫ x, u x * mhn_phi h x := by
      unfold HNeg.pairing
      rw [integral_mul_eq_re_fourierL2 hu (mhn_memLp_phi h)]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hFae] with ξ hξ
      rw [hξ, mul_comm]
    rw [hpair']
    have hext := sa12l12_test_ext hq hA hu hpair (mhn_contDiff_phi h)
      (fun j _ => sa12l12_phi_jets h j) (mhn_memSobolev_phi q h)
    refine hext.trans ?_
    have hn1 : Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq q (mhn_phi h)) ≤ 1 := by
      have := hs1 n
      rw [← hh, mhn_norm_rep] at this
      exact this
    calc A * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq q (mhn_phi h)) ≤ A * 1 :=
          mul_le_mul_of_nonneg_left hn1 hA
      _ = A := mul_one A
  have hS : ∫ ξ, wt ξ ^ (-q) * ‖fourierL2 u ξ‖ ^ 2 ≤ A ^ 2 := by
    rw [← hFnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) hFA 2
  exact sa12x_sobE_of_le hA ⟨hu, hint⟩ hS

end HRS.MH.AdjointRd.Phase2SA12Limit
