import Mathlib
import HRS.MS.SuppU5Aux7

/-!
# Packet U5 (aux 8): existence of the `H^{-Γ}`-valued Gaussian field
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

open HRS HRS.Whole HRS.MP.RdProp HRS.MP.HNegInfra

variable {d : ℕ}

/-- Second moments of finite linear combinations of the bridge. -/
lemma u5_bridge_sq {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (η : Ω' → (Euc d → ℝ) → ℝ)
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : Ek p)) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)))
    {q : ℕ} (ψ : Fin q → Euc d → ℝ) (hψ : ∀ j, MemCb 1 (ψ j)) (u : Fin q → ℝ) :
    ∫⁻ ζ, ENNReal.ofReal ((∑ j, u j * η ζ (ψ j)) ^ 2) ∂P' =
      ENNReal.ofReal (∫ x, (∑ j, u j * (ψ j x - HRS.Whole.pair μ (ψ j))) ^ 2 ∂μ) := by
  set G : Ω' → Ek q := fun ζ => WithLp.toLp 2 fun a => η ζ (ψ a) with hG
  have hGm : Measurable G :=
    (MeasurableEquiv.toLp 2 (Fin q → ℝ)).measurable.comp (measurable_pi_iff.2 fun j => hηm _ (hψ j))
  set Lf : Ek q →L[ℝ] ℝ := ∑ j, u j • (EuclideanSpace.proj j : Ek q →L[ℝ] ℝ) with hLf
  have hLfapp : ∀ z, Lf z = ∑ j, u j * z j := fun z => by simp [hLf]
  set Sψ : Matrix (Fin q) (Fin q) ℝ := Matrix.of fun a b => iidCovW μ (ψ a) (ψ b) with hSg
  have hpsd : Sψ.PosSemidef := u5_cov_psd ψ hψ μ
  set γ := multivariateGaussian (0 : Ek q) Sψ with hγ
  have hlaw : P'.map G = γ := hη q ψ hψ
  have h2γ : Integrable (fun y : Ek q => ‖y‖ ^ 2) γ := Yurinskii.integrable_norm_pow_gauss 2 (by norm_num)
  have hf : Measurable fun z : Ek q => ENNReal.ofReal ((Lf z) ^ 2) :=
    ENNReal.measurable_ofReal.comp (Lf.continuous.measurable.pow_const 2)
  have e1 : ∫⁻ ζ, ENNReal.ofReal ((∑ j, u j * η ζ (ψ j)) ^ 2) ∂P' =
      ∫⁻ z, ENNReal.ofReal ((Lf z) ^ 2) ∂γ := by
    rw [← hlaw, lintegral_map hf hGm]
    refine lintegral_congr fun ζ => ?_
    rw [hLfapp]
  have hLi : Integrable (fun z => (Lf z) ^ 2) γ := by
    refine (h2γ.const_mul (‖Lf‖ ^ 2)).mono' (Lf.continuous.measurable.pow_const 2).aestronglyMeasurable
      (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_pow, ← mul_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using Lf.le_opNorm z) 2
  rw [e1, ← ofReal_integral_eq_lintegral_ofReal hLi (ae_of_all _ fun _ => sq_nonneg _)]
  congr 1
  rw [u5_int_sq_lin γ h2γ Lf]
  simp only [hγ, Yurinskii.integral_coord_mul hpsd]
  -- the right-hand side
  have hfm : ∀ j, MemCb 1 (ψ j) := hψ
  have hint : ∀ a b, Integrable (fun x => (ψ a x - HRS.Whole.pair μ (ψ a)) *
      (ψ b x - HRS.Whole.pair μ (ψ b))) μ := fun a b => by
    have e : (fun x => (ψ a x - HRS.Whole.pair μ (ψ a)) * (ψ b x - HRS.Whole.pair μ (ψ b))) =
        fun x => (ψ a x * ψ b x - HRS.Whole.pair μ (ψ b) * ψ a x) -
          (HRS.Whole.pair μ (ψ a) * ψ b x - HRS.Whole.pair μ (ψ a) * HRS.Whole.pair μ (ψ b)) := by
      ext x; ring
    rw [e]
    exact ((u5_prod_integrable (hψ a) (hψ b) μ).sub ((u5_cb_integrable (hψ a) μ).const_mul _)).sub
      (((u5_cb_integrable (hψ b) μ).const_mul _).sub (integrable_const _))
  have e2 : ∀ x, (∑ j, u j * (ψ j x - HRS.Whole.pair μ (ψ j))) ^ 2 =
      ∑ a, ∑ b, (u a * u b) * ((ψ a x - HRS.Whole.pair μ (ψ a)) * (ψ b x - HRS.Whole.pair μ (ψ b))) := fun x => by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  simp_rw [e2]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hint a b).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_const_mul, u5_cov_eq (hψ a) (hψ b) μ]
  simp [hLf, hSg]

/-- An orthogonal series with square-summable coefficients is summable. -/
lemma u5_series_summable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {g : ℕ → E} (hg0 : ∀ n, ‖g n‖ = 0 ∨ ‖g n‖ = 1) (hgo : ∀ m n, m ≠ n → ⟪g m, g n⟫ = 0)
    (c : ℕ → ℝ) (hc : Summable fun n => c n ^ 2) : Summable fun n => c n • g n := by
  let G : ℕ → Type _ := fun n => ↥(Submodule.span ℝ {g n})
  let V : ∀ n, G n →ₗᵢ[ℝ] E := fun n => (Submodule.span ℝ {g n}).subtypeₗᵢ
  have hV : OrthogonalFamily ℝ G V := by
    intro i j hij v w
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 v.2
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 w.2
    show ⟪(v : E), (w : E)⟫ = 0
    rw [← ha, ← hb, inner_smul_left, inner_smul_right, hgo i j hij]
    simp
  let f : ∀ n, G n := fun n => ⟨c n • g n, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)⟩
  have h := (hV.summable_iff_norm_sq_summable f).2 (by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hc
    show ‖(c n • g n)‖ ^ 2 ≤ c n ^ 2
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rcases hg0 n with h | h
    · rw [h]; simp; positivity
    · rw [h]; simp)
  exact h

lemma u5_comb_pair (μ : Measure (Euc d)) [IsProbabilityMeasure μ] {L : ℕ} (f : Euc d → ℝ)
    (hf : MemCb 1 f) (h : ℕ → Euc d → ℝ) (hh : ∀ n, MemCb 1 (h n)) (c : ℕ → ℝ) :
    HRS.Whole.pair μ (fun x => f x - ∑ n ∈ Finset.range L, c n * h n x) =
      HRS.Whole.pair μ f - ∑ n ∈ Finset.range L, c n * HRS.Whole.pair μ (h n) := by
  unfold HRS.Whole.pair
  rw [integral_sub (u5_cb_integrable hf μ)
    (integrable_finsetSum _ fun n _ => (u5_cb_integrable (hh n) μ).const_mul _),
    integral_finsetSum _ fun n _ => (u5_cb_integrable (hh n) μ).const_mul _]
  simp_rw [integral_const_mul]

set_option maxHeartbeats 1000000 in
/-- Existence of the `H^{-Γ}`-valued Gaussian field representing `φ ↦ A η°(ψ φ)`. -/
lemma u5_exists_I {Γ : ℝ} (K A : ℝ) (hA : 0 ≤ A) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (ψ : (Euc d → ℝ) → (Euc d → ℝ))
    (hψ : ∀ φ, IsSobolevTest Γ φ → MemCb 1 (ψ φ) ∧ cbNorm 1 (ψ φ) ≤ K * HRS.Whole.sobolevNorm Γ φ)
    (hlin : ∀ (φ₁ φ₂ : Euc d → ℝ) (c : ℝ), IsSobolevTest Γ φ₁ → IsSobolevTest Γ φ₂ →
      ψ (φ₁ + c • φ₂) = ψ φ₁ + c • ψ φ₂)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : Ω' → (Euc d → ℝ) → ℝ)
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : Ek p)) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b))) :
    ∃ I : Ω' → HNeg d Γ, Measurable I ∧
      ∀ φ, IsSobolevTest Γ φ → ∀ᵐ ζ ∂P', HNeg.pairing φ (I ζ) = A * η ζ (ψ φ) := by
  obtain ⟨J, hJ, hJb, hJL⟩ := u5_feature Γ K A hA μ ψ hψ hlin
  set b : ℝ := 2 * A * max K 0 with hb
  have hb0 : 0 ≤ b := by positivity
  have hJc : Continuous J :=
    (LipschitzWith.of_dist_le' (K := A * max K 0) fun x y => by
      simpa [dist_eq_norm] using hJL x y).continuous
  set Rm : Submodule ℝ (HNeg d Γ) := LinearMap.range (rpk_J Γ) with hRm
  have hRm0 : Rmᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro F hF
    refine hneg_eq_zero_of_pairing_zero F fun φ hφ => ?_
    rw [← rpk_J_inner (⟨φ, hφ⟩ : rpk_Tst d Γ) F]
    exact (Submodule.mem_orthogonal _ _).1 hF _ ⟨⟨φ, hφ⟩, rfl⟩
  obtain ⟨g, hgR, hg0, hgo, hpar⟩ := u5_orthoseq Rm hRm0
  choose θ hθ using fun n => LinearMap.mem_range.1 (hgR n)
  have hψn : ∀ n, MemCb 1 (ψ (θ n).1) := fun n => (hψ _ (θ n).2).1
  have hcoord : ∀ n x, inner ℝ (g n) (J x) =
      A * (ψ (θ n).1 x - HRS.Whole.pair μ (ψ (θ n).1)) := fun n x => by
    rw [← hθ n, rpk_J_inner, hJ x _ (θ n).2]
  set ξ : ℕ → Ω' → ℝ := fun n ζ => A * η ζ (ψ (θ n).1) with hξ
  have hξm : ∀ n, Measurable (ξ n) := fun n => (hηm _ (hψn n)).const_mul A
  -- second moments
  have hvar : ∀ n, ∫⁻ ζ, ENNReal.ofReal ((ξ n ζ) ^ 2) ∂P' =
      ENNReal.ofReal (∫ x, (inner ℝ (g n) (J x)) ^ 2 ∂μ) := fun n => by
    have := u5_bridge_sq P' μ η hηm hη (q := 1) (fun _ => ψ (θ n).1) (fun _ => hψn n) (fun _ => A)
    simp only [Finset.univ_unique, Finset.sum_singleton] at this
    simp only [hξ, hcoord]
    exact this
  -- partial sums of the variances
  have hJm : Measurable J := hJc.measurable
  have hcoordi : ∀ n, Integrable (fun x => (inner ℝ (g n) (J x)) ^ 2) μ := fun n =>
    Integrable.of_bound ((measurable_const.inner hJm).pow_const 2).aestronglyMeasurable (b ^ 2)
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        calc |inner ℝ (g n) (J x)| ≤ ‖g n‖ * ‖J x‖ := abs_real_inner_le_norm _ _
          _ ≤ 1 * b := by
              refine mul_le_mul ?_ (hJb x) (norm_nonneg _) zero_le_one
              rcases hg0 n with h | h <;> simp [h]
          _ = b := one_mul b)
  have hsum : ∀ L, ∑ n ∈ Finset.range L, ∫ x, (inner ℝ (g n) (J x)) ^ 2 ∂μ ≤ b ^ 2 := fun L => by
    rw [← integral_finsetSum _ fun n _ => hcoordi n]
    calc ∫ x, ∑ n ∈ Finset.range L, (inner ℝ (g n) (J x)) ^ 2 ∂μ ≤ ∫ _x, b ^ 2 ∂μ := by
          refine integral_mono (integrable_finsetSum _ fun n _ => hcoordi n) (integrable_const _) fun x => ?_
          rw [← u5_tau_sq_eq hpar]
          calc ‖u5_tau g L (J x)‖ ^ 2 ≤ ‖J x‖ ^ 2 := u5_tau_sq_le hpar L _
            _ ≤ b ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hJb x) 2
      _ = b ^ 2 := by simp
  -- almost sure square summability
  have hlint : ∫⁻ ζ, ∑' n, ENNReal.ofReal ((ξ n ζ) ^ 2) ∂P' ≤ ENNReal.ofReal (b ^ 2) := by
    rw [lintegral_tsum (fun n => (((hξm n).pow_const 2).ennreal_ofReal).aemeasurable)]
    simp_rw [hvar]
    refine ENNReal.tsum_le_of_sum_range_le fun L => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun n _ => integral_nonneg fun x => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hsum L)
  have hae : ∀ᵐ ζ ∂P', Summable (fun n => (ξ n ζ) ^ 2) := by
    have hmeas : Measurable fun ζ => ∑' n, ENNReal.ofReal ((ξ n ζ) ^ 2) :=
      Measurable.ennreal_tsum fun n => ((hξm n).pow_const 2).ennreal_ofReal
    have := ae_lt_top hmeas (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlint)
    filter_upwards [this] with ζ hζ
    have h2 := ENNReal.summable_toReal hζ.ne
    simpa [ENNReal.toReal_ofReal (sq_nonneg _)] using h2
  -- the series
  set Ξ : ℕ → Ω' → HNeg d Γ := fun L ζ => ∑ n ∈ Finset.range L, ξ n ζ • g n with hΞ
  have hΞm : ∀ L, Measurable (Ξ L) := fun L =>
    Finset.measurable_sum _ fun n _ => (hξm n).smul_const (g n)
  have hconv : ∀ᵐ ζ ∂P', ∃ l, Tendsto (fun L => Ξ L ζ) atTop (𝓝 l) := by
    filter_upwards [hae] with ζ hζ
    exact ⟨_, (u5_series_summable hg0 hgo (fun n => ξ n ζ) hζ).hasSum.tendsto_sum_nat⟩
  obtain ⟨I, hIm, hItend⟩ := measurable_limit_of_tendsto_metrizable_ae (L := atTop)
    (fun L => (hΞm L).aemeasurable) hconv
  refine ⟨I, hIm, fun φ hφ => ?_⟩
  set Φ0 : rpk_Tst d Γ := ⟨φ, hφ⟩ with hΦ0
  set c : ℕ → ℝ := fun n => inner ℝ (rpk_J Γ Φ0) (g n) with hc
  have hpair : ∀ F : HNeg d Γ, HNeg.pairing φ F = inner ℝ (rpk_J Γ Φ0) F := fun F =>
    (rpk_J_inner Φ0 F).symm
  have ha : ∀ L ζ, HNeg.pairing φ (Ξ L ζ) = ∑ n ∈ Finset.range L, c n * ξ n ζ := fun L ζ => by
    rw [hpair, hΞ]
    simp only []
    rw [inner_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_smul_right, hc]; ring
  have hlimit : ∀ᵐ ζ ∂P', Tendsto (fun L => ∑ n ∈ Finset.range L, c n * ξ n ζ) atTop
      (𝓝 (HNeg.pairing φ (I ζ))) := by
    filter_upwards [hItend] with ζ hζ
    have := ((mhn_continuous_pairing hφ).tendsto (I ζ)).comp hζ
    simpa [Function.comp_def, ha] using this
  -- the approximating tests
  set ΦL : ℕ → rpk_Tst d Γ := fun L => ∑ n ∈ Finset.range L, c n • θ n with hΦL
  have hJΦL : ∀ L, rpk_J Γ (ΦL L) = u5_iota g L (u5_tau g L (rpk_J Γ Φ0)) := fun L => by
    rw [hΦL]
    simp only [map_sum, map_smul, hθ]
    rw [u5_iota_apply, ← Fin.sum_univ_eq_sum_range (fun n => c n • g n) L]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [u5_tau_apply, real_inner_comm]
  have hψ0 : ψ 0 = 0 := by
    have h := hlin 0 0 1 (rpk_Tst d Γ).zero_mem (rpk_Tst d Γ).zero_mem
    simp only [smul_zero, add_zero] at h
    rw [one_smul] at h
    exact (left_eq_add.1 h)
  have hψsum : ∀ L, ψ (ΦL L).1 = ∑ n ∈ Finset.range L, c n • ψ (θ n).1 := fun L => by
    induction L with
    | zero => simp [hΦL, hψ0]
    | succ L ih =>
      have e : (ΦL (L + 1)).1 = (ΦL L).1 + c L • (θ L).1 := by
        simp [hΦL, Finset.sum_range_succ]
      rw [e, hlin _ _ _ (ΦL L).2 (θ L).2, ih, Finset.sum_range_succ]
  have hψdiff : ∀ L, ψ (Φ0 - ΦL L).1 = ψ φ - ∑ n ∈ Finset.range L, c n • ψ (θ n).1 := fun L => by
    have e : (Φ0 - ΦL L).1 = φ + (-1 : ℝ) • (ΦL L).1 := by
      simp [hΦ0, sub_eq_add_neg]
    rw [e, hlin _ _ _ hφ (ΦL L).2, hψsum]
    simp [sub_eq_add_neg]
  -- the `L²` distance to the approximations
  set δ : ℕ → ℝ := fun L => ‖rpk_J Γ Φ0 - u5_iota g L (u5_tau g L (rpk_J Γ Φ0))‖ with hδ
  have hδ0 : Tendsto δ atTop (𝓝 0) := u5_sub_iota_tau_tendsto hg0 hgo hpar _
  have hΦcb : ∀ L, MemCb 1 (ψ (Φ0 - ΦL L).1) ∧ cbNorm 1 (ψ (Φ0 - ΦL L).1) ≤ max K 0 * δ L := fun L => by
    have h := hψ _ (Φ0 - ΦL L).2
    refine ⟨h.1, h.2.trans ?_⟩
    have hn : HRS.Whole.sobolevNorm Γ (Φ0 - ΦL L).1 = δ L := by
      rw [← rpk_J_norm, map_sub, hJΦL]
    rw [hn]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hmain : ∀ L, ∫⁻ ζ, ENNReal.ofReal ((A * η ζ (ψ φ) - ∑ n ∈ Finset.range L, c n * ξ n ζ) ^ 2) ∂P' ≤
      ENNReal.ofReal ((A * (2 * (max K 0 * δ L))) ^ 2) := fun L => by
    set ψ' : Fin (L + 1) → Euc d → ℝ := Fin.cons (ψ φ) (fun n : Fin L => ψ (θ n).1) with hψ'
    set u : Fin (L + 1) → ℝ := Fin.cons A (fun n : Fin L => -(A * c n)) with hu
    have hψ'm : ∀ j, MemCb 1 (ψ' j) := by
      intro j
      refine Fin.cases ?_ (fun n => ?_) j
      · simpa [hψ'] using (hψ φ hφ).1
      · simpa [hψ'] using hψn n
    have key := u5_bridge_sq P' μ η hηm hη ψ' hψ'm u
    have e1 : ∀ ζ, ∑ j, u j * η ζ (ψ' j) =
        A * η ζ (ψ φ) - ∑ n ∈ Finset.range L, c n * ξ n ζ := fun ζ => by
      rw [Fin.sum_univ_succ]
      simp only [hu, hψ', Fin.cons_zero, Fin.cons_succ, neg_mul, Finset.sum_neg_distrib, hξ]
      rw [sub_eq_add_neg, ← Fin.sum_univ_eq_sum_range (fun n => c n * (A * η ζ (ψ (θ n).1))) L]
      congr 1
      congr 1
      refine Finset.sum_congr rfl fun n _ => by ring
    simp_rw [e1] at key
    rw [key]
    refine ENNReal.ofReal_le_ofReal ?_
    have e2 : ∀ x, ∑ j, u j * (ψ' j x - HRS.Whole.pair μ (ψ' j)) =
        A * ((ψ (Φ0 - ΦL L).1 x) - HRS.Whole.pair μ (ψ (Φ0 - ΦL L).1)) := fun x => by
      have hF : ψ (Φ0 - ΦL L).1 = fun x => ψ φ x - ∑ n ∈ Finset.range L, c n * ψ (θ n).1 x := by
        rw [hψdiff]; ext x; simp
      rw [hF, u5_comb_pair μ (ψ φ) (hψ φ hφ).1 (fun n => ψ (θ n).1) hψn c, Fin.sum_univ_succ]
      simp only [hu, hψ', Fin.cons_zero, Fin.cons_succ, neg_mul, Finset.sum_neg_distrib]
      rw [← Fin.sum_univ_eq_sum_range (fun n => c n * (ψ (θ n).1 x)) L,
        ← Fin.sum_univ_eq_sum_range (fun n => c n * HRS.Whole.pair μ (ψ (θ n).1)) L]
      simp only [Finset.mul_sum, mul_sub]
      simp only [mul_assoc, Finset.sum_sub_distrib]
      ring
    simp_rw [e2]
    have hFm := hΦcb L
    refine (integral_mono_of_nonneg (ae_of_all _ fun x => sq_nonneg _)
      (integrable_const ((A * (2 * (max K 0 * δ L))) ^ 2)) (ae_of_all _ fun x => ?_)).trans
      (le_of_eq (by simp))
    have h1 := u5_cb_sup hFm.1 x
    have h2 := u5_pair_abs_le hFm.1 μ
    have h3 : |A * (ψ (Φ0 - ΦL L).1 x - HRS.Whole.pair μ (ψ (Φ0 - ΦL L).1))| ≤
        A * (2 * (max K 0 * δ L)) := by
      rw [abs_mul, abs_of_nonneg hA]
      refine mul_le_mul_of_nonneg_left ?_ hA
      calc |ψ (Φ0 - ΦL L).1 x - HRS.Whole.pair μ (ψ (Φ0 - ΦL L).1)|
          ≤ |ψ (Φ0 - ΦL L).1 x| + |HRS.Whole.pair μ (ψ (Φ0 - ΦL L).1)| := abs_sub _ _
        _ ≤ 2 * (max K 0 * δ L) := by linarith [hFm.2]
    calc (A * (ψ (Φ0 - ΦL L).1 x - HRS.Whole.pair μ (ψ (Φ0 - ΦL L).1))) ^ 2
        = |A * (ψ (Φ0 - ΦL L).1 x - HRS.Whole.pair μ (ψ (Φ0 - ΦL L).1))| ^ 2 := (sq_abs _).symm
      _ ≤ (A * (2 * (max K 0 * δ L))) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
  -- conclusion by Fatou's lemma
  have hVm : Measurable fun ζ => HNeg.pairing φ (I ζ) :=
    (mhn_continuous_pairing hφ).measurable.comp hIm
  have hWm : Measurable fun ζ => A * η ζ (ψ φ) := (hηm _ (hψ φ hφ).1).const_mul A
  have hZm : ∀ L, Measurable fun ζ => ∑ n ∈ Finset.range L, c n * ξ n ζ := fun L =>
    Finset.measurable_sum _ fun n _ => (hξm n).const_mul _
  set f : ℕ → Ω' → ℝ≥0∞ := fun L ζ =>
    ENNReal.ofReal ((A * η ζ (ψ φ) - ∑ n ∈ Finset.range L, c n * ξ n ζ) ^ 2) with hf
  have hfm : ∀ L, Measurable (f L) := fun L =>
    ENNReal.measurable_ofReal.comp ((hWm.sub (hZm L)).pow_const 2)
  have hlim : ∀ᵐ ζ ∂P', Tendsto (fun L => f L ζ) atTop
      (𝓝 (ENNReal.ofReal ((A * η ζ (ψ φ) - HNeg.pairing φ (I ζ)) ^ 2))) := by
    filter_upwards [hlimit] with ζ hζ
    exact ENNReal.tendsto_ofReal ((tendsto_const_nhds.sub hζ).pow 2)
  have hfat : ∫⁻ ζ, ENNReal.ofReal ((A * η ζ (ψ φ) - HNeg.pairing φ (I ζ)) ^ 2) ∂P' ≤
      liminf (fun L => ∫⁻ ζ, f L ζ ∂P') atTop :=
    calc _ = ∫⁻ ζ, liminf (fun L => f L ζ) atTop ∂P' :=
          lintegral_congr_ae (hlim.mono fun ζ h => h.liminf_eq.symm)
      _ ≤ _ := lintegral_liminf_le hfm
  have hint0 : Tendsto (fun L => ∫⁻ ζ, f L ζ ∂P') atTop (𝓝 0) := by
    have hb : Tendsto (fun L => ENNReal.ofReal ((A * (2 * (max K 0 * δ L))) ^ 2)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun L => (A * (2 * (max K 0 * δ L))) ^ 2) atTop
          (𝓝 ((A * (2 * (max K 0 * 0))) ^ 2)) :=
        ((tendsto_const_nhds.mul (tendsto_const_nhds.mul (tendsto_const_nhds.mul hδ0))).pow 2)
      simpa using ENNReal.tendsto_ofReal h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun L => bot_le) hmain
  have hzero : ∫⁻ ζ, ENNReal.ofReal ((A * η ζ (ψ φ) - HNeg.pairing φ (I ζ)) ^ 2) ∂P' = 0 :=
    le_antisymm (by simpa [hint0.liminf_eq] using hfat) bot_le
  have hmeasD : Measurable fun ζ => ENNReal.ofReal ((A * η ζ (ψ φ) - HNeg.pairing φ (I ζ)) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hWm.sub hVm).pow_const 2)
  have hz := (lintegral_eq_zero_iff hmeasD).1 hzero
  filter_upwards [hz] with ζ hζ
  have h0 : (A * η ζ (ψ φ) - HNeg.pairing φ (I ζ)) ^ 2 ≤ 0 := by
    simpa using hζ
  have : (A * η ζ (ψ φ) - HNeg.pairing φ (I ζ)) = 0 := pow_eq_zero_iff (two_ne_zero) |>.1
    (le_antisymm h0 (sq_nonneg _))
  linarith

end HRS.U5
