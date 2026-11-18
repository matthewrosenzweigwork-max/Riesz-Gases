import HRS.MP.SelfSimP4MolH1

/-!
# MPP4MOL stage 5c (15): the cut-off error terms vanish in the limit
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

section
variable {θ T : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {V W : ℝ → EucConfig d N → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem P4MolData.cont_E (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v)
    {χ : EucConfig d N → ℝ} (hχ : ContDiff ℝ 1 χ) (hχs : HasCompactSupport χ) (k : Fin N × Fin d) :
    Continuous (fun s => ∫ x, p4m_Lam v θ (μ s) (V s) x * fderiv ℝ χ x (configBasis d N k) *
      (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) := by
  have hdχ : Continuous (fun x => fderiv ℝ χ x (configBasis d N k)) :=
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχs : HasCompactSupport (fun x => fderiv ℝ χ x (configBasis d N k)) := hχs.fderiv_apply ℝ _
  have hEc : Continuous (fun p : ℝ × EucConfig d N =>
      p4m_Lam v θ (μ p.1) (V p.1) p.2 * fderiv ℝ χ p.2 (configBasis d N k) *
        (θ * p4m_gu v (μ p.1) k p.2 - p4m_B v (μ p.1) (b p.1) k p.2)) :=
    ((h.cont_Lam hv).mul (hdχ.comp continuous_snd)).mul (h.cont_J hv k)
  exact p4m_cont_param_cs (f := fun s x => p4m_Lam v θ (μ s) (V s) x *
    fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) hEc
    hdχs (fun s x hx => by simp [hx])

theorem P4MolData.tendsto_E (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (hθ : 0 < θ) (t : ℝ) :
    Tendsto (fun n : ℕ => ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_Lam v θ (μ s) (V s) x *
      fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
      (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := by
    haveI := h.prob 0
    exact (integral_nonneg fun y => p4m_q_nonneg y).trans (h.hM 0)
  have hCV : 0 ≤ CV := by
    have := h.Vg 0 0
    have h0 : p4m_q (0 : EucConfig d N) = 0 := by simp [p4m_q]
    rw [h0] at this
    nlinarith [abs_nonneg (V 0 0)]
  obtain ⟨AE, hAE0, hAE⟩ := p4m_Ek_bound (d := d) (N := N) (v := v) (θ := θ) (B := B) (K := K) (M := M)
    (CV := CV) hv hθ h.hB h.hK hM0 hCV
  obtain ⟨L, hL0, hL⟩ := p4m_fderiv_chi_bound (d := d) (N := N)
  set b0 : ℝ := 1 / (4 * v) with hb0
  have hb0pos : 0 < b0 := by positivity
  set Cw : ℝ := (∫ w : EucConfig d N, p4m_E b0 w) + 2 * (∫ w : EucConfig d N, p4m_q w * p4m_E b0 w) +
    2 * (∫ w : EucConfig d N, p4m_E b0 w) * M with hCw
  have hI0 : 0 ≤ ∫ w : EucConfig d N, p4m_E b0 w := integral_nonneg fun w => (p4m_E_pos _ _).le
  -- the sum of the error terms, as a function of `s`
  set Ehat : ℕ → ℝ → ℝ := fun n s => ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ (μ s) (V s) x *
      fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
      (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) with hEhat
  have hEc : ∀ n : ℕ, Continuous (Ehat n) := fun n =>
    continuous_finset_sum _ fun k _ => h.cont_E hv (p4m_contDiff_chi (R := (n : ℝ) + 1))
      (p4m_hasCompactSupport_chi (by positivity)) k
  have hsum : ∀ n : ℕ, ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_Lam v θ (μ s) (V s) x *
      fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
      (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) = ∫ s in Set.Icc (0 : ℝ) t, Ehat n s := by
    intro n
    rw [integral_finset_sum]
    intro k _
    exact (h.cont_E hv (p4m_contDiff_chi (R := (n : ℝ) + 1))
      (p4m_hasCompactSupport_chi (by positivity)) k).integrableOn_Icc (μ := volume)
  simp_rw [hsum]
  -- pointwise bound
  have hbd : ∀ (n : ℕ) (s : ℝ), |Ehat n s| ≤ AE * L * ∫ x in {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x},
      (1 + p4m_q x) * ∫ y, p4m_E b0 (x - y) ∂(μ s) := by
    intro n s
    haveI := h.prob s
    have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hR0 : 0 < (n : ℝ) + 1 := by linarith
    exact hAE (μ s) (h.hm s) (h.hM s) (b s) (h.bg s) (h.bc.comp (Continuous.prodMk continuous_const continuous_id))
      (V s) (h.Vg s) ((n : ℝ) + 1) L hR hL0 (p4m_chi ((n : ℝ) + 1))
      (fun x k hk => p4m_fderiv_chi_ne_zero hR0 hk) (fun x k => hL _ hR0 x k)
  have hKle : ∀ (n : ℕ) (s : ℝ), (∫ x in {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x},
      (1 + p4m_q x) * ∫ y, p4m_E b0 (x - y) ∂(μ s)) ≤ Cw := by
    intro n s
    haveI := h.prob s
    have hi := p4m_integrable_weight (h.hm s) hb0pos
    have hnn : ∀ x : EucConfig d N, 0 ≤ (1 + p4m_q x) * ∫ y, p4m_E b0 (x - y) ∂(μ s) := fun x =>
      mul_nonneg (by have := p4m_q_nonneg x; linarith) (integral_nonneg fun y => (p4m_E_pos _ _).le)
    refine (setIntegral_le_integral hi (Filter.Eventually.of_forall hnn)).trans ?_
    refine (p4m_weight_integral_le (h.hm s) hb0pos).trans ?_
    have := h.hM s
    nlinarith
  have hKnn : ∀ (n : ℕ) (s : ℝ), 0 ≤ ∫ x in {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x},
      (1 + p4m_q x) * ∫ y, p4m_E b0 (x - y) ∂(μ s) := fun n s =>
    setIntegral_nonneg ((isClosed_le continuous_const p4m_continuous_q).measurableSet) fun x _ =>
      mul_nonneg (by have := p4m_q_nonneg x; linarith) (integral_nonneg fun y => (p4m_E_pos _ _).le)
  suffices key : Tendsto (fun n : ℕ => ∫ s in Set.Icc (0 : ℝ) t, Ehat n s) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) t, (0 : ℝ))) by simpa using key
  refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0 : ℝ) t))
    (fun _ => AE * L * Cw) ?_ (integrable_const _) ?_ ?_
  · intro n
    exact (hEc n).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact (hbd n s).trans (mul_le_mul_of_nonneg_left (hKle n s) (by positivity))
  · refine Filter.Eventually.of_forall fun s => ?_
    haveI := h.prob s
    have ht := (tendsto_add_atTop_iff_nat 1).2 (p4m_tail_tendsto (h.hm s) hb0pos)
    have ht' : Tendsto (fun n : ℕ => ∫ x in {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x},
        (1 + p4m_q x) * ∫ y, p4m_E b0 (x - y) ∂(μ s)) atTop (𝓝 0) := by
      refine ht.congr fun n => ?_
      simp
    have := ht'.const_mul (AE * L)
    rw [mul_zero] at this
    refine squeeze_zero_norm (fun n => ?_) this
    rw [Real.norm_eq_abs]
    exact hbd n s

end

end HRS.MP.SelfSimP4Mol
