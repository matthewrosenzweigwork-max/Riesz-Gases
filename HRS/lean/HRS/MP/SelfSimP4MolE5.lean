import HRS.MP.SelfSimP4MolE4

/-!
# MPP4MOL stage 5c (9): the time-integrated cut-off inequality
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

theorem P4MolData.time_ineq (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (hθ : 0 < θ) {δ : ℝ}
    (hδ : 0 < δ) {χ : EucConfig d N → ℝ} (hχ : ContDiff ℝ 1 χ) (hχs : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ x, χ x * p4m_Phi v θ μ V t x ≤ (∫ x, χ x * p4m_Phi v θ μ V 0 x) -
      (θ * (1 - δ)) * (∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ x *
        (p4Mol v (μ s) x * ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2)) +
      t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ)) -
      ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_Lam v θ (μ s) (V s) x *
        fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) := by
  have ht0 : 0 ≤ t := ht.1
  have hcu := h.cont_u hv
  have hca := h.cont_a hv
  have hcΛ := h.cont_Lam hv
  have hcW : Continuous (fun p : ℝ × EucConfig d N => W p.1 p.2) := h.Wc
  have hcχ : Continuous χ := hχ.continuous
  have hdχ : ∀ k : Fin N × Fin d, Continuous (fun x => fderiv ℝ χ x (configBasis d N k)) := fun k =>
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχs : ∀ k : Fin N × Fin d, HasCompactSupport (fun x => fderiv ℝ χ x (configBasis d N k)) :=
    fun k => hχs.fderiv_apply ℝ _
  have hcχ2 : Continuous (fun p : ℝ × EucConfig d N => χ p.2) := hcχ.comp continuous_snd
  -- the integrand of the time derivative
  have hg : Continuous (fun p : ℝ × EucConfig d N =>
      χ p.2 * (p4m_a v θ (μ p.1) (b p.1) p.2 * p4m_Lam v θ (μ p.1) (V p.1) p.2 +
        p4Mol v (μ p.1) p.2 * W p.1 p.2 / θ)) :=
    hcχ2.mul ((hca.mul hcΛ).add ((hcu.mul hcW).div_const θ))
  have hgz : ∀ s x, χ x = 0 → χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
        p4Mol v (μ s) x * W s x / θ) = 0 := fun s x hx => by simp [hx]
  -- pointwise fundamental theorem of calculus
  have hftc : ∀ x, p4m_Phi v θ μ V t x - p4m_Phi v θ μ V 0 x =
      ∫ s in Set.Icc (0 : ℝ) t, (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
        p4Mol v (μ s) x * W s x / θ) := by
    intro x
    have hPc : Continuous (fun s => p4m_Phi v θ μ V s x) :=
      (h.cont_Phi hv).comp (Continuous.prodMk continuous_id continuous_const)
    have hfc : Continuous (fun s => p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
        p4Mol v (μ s) x * W s x / θ) :=
      ((hca.mul hcΛ).add ((hcu.mul hcW).div_const θ)).comp
        (Continuous.prodMk continuous_id (continuous_const (y := x)))
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht0 hPc.continuousOn
      (f' := fun s => p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
        p4Mol v (μ s) x * W s x / θ)
      (fun s hs => (h.hasDerivAt_Phi hv x ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩).hasDerivWithinAt)
      (hfc.intervalIntegrable 0 t)
    rw [intervalIntegral.integral_of_le ht0, ← integral_Icc_eq_integral_Ioc] at this
    exact this.symm
  have hΦi : ∀ s, Integrable (fun x => χ x * p4m_Phi v θ μ V s x) := fun s =>
    p4m_int_of_supp (hcχ.mul ((h.cont_Phi hv).comp (Continuous.prodMk continuous_const continuous_id)))
      hχs fun x hx => by simp [hx]
  have hF : (∫ x, χ x * p4m_Phi v θ μ V t x) - (∫ x, χ x * p4m_Phi v θ μ V 0 x) =
      ∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
        p4Mol v (μ s) x * W s x / θ) := by
    rw [← integral_sub (hΦi t) (hΦi 0)]
    have e : ∀ x, χ x * p4m_Phi v θ μ V t x - χ x * p4m_Phi v θ μ V 0 x =
        ∫ s in Set.Icc (0 : ℝ) t, χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
          p4Mol v (μ s) x * W s x / θ) := by
      intro x
      rw [integral_const_mul, ← hftc x]
      ring
    simp_rw [e]
    exact (p4m_swap_time (f := fun s x => χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
      p4Mol v (μ s) x * W s x / θ)) hg hχs hgz t).symm
  -- continuity in time of the three parametric integrals
  have hcg := p4m_cont_param_cs (f := fun s x => χ x * (p4m_a v θ (μ s) (b s) x *
    p4m_Lam v θ (μ s) (V s) x + p4Mol v (μ s) x * W s x / θ)) hg hχs hgz
  have hDc : Continuous (fun p : ℝ × EucConfig d N =>
      χ p.2 * (p4Mol v (μ p.1) p.2 * ∑ k : Fin N × Fin d, p4m_ell v θ (μ p.1) (b p.1) k p.2 ^ 2)) :=
    hcχ2.mul (hcu.mul (continuous_finset_sum _ fun k _ => (h.cont_ell hv k).pow 2))
  have hcD := p4m_cont_param_cs (f := fun s x => χ x * (p4Mol v (μ s) x *
    ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2)) hDc hχs (fun s x hx => by simp [hx])
  have hEc : ∀ k : Fin N × Fin d, Continuous (fun p : ℝ × EucConfig d N =>
      p4m_Lam v θ (μ p.1) (V p.1) p.2 * fderiv ℝ χ p.2 (configBasis d N k) *
        (θ * p4m_gu v (μ p.1) k p.2 - p4m_B v (μ p.1) (b p.1) k p.2)) := fun k =>
    (hcΛ.mul ((hdχ k).comp continuous_snd)).mul (h.cont_J hv k)
  have hcE := fun k : Fin N × Fin d => p4m_cont_param_cs (f := fun s x => p4m_Lam v θ (μ s) (V s) x *
    fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) (hEc k)
    (hdχs k) (fun s x hx => by simp [hx])
  -- the fixed-time inequality at every time
  have hfix : ∀ s, ∫ x, χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
        p4Mol v (μ s) x * W s x / θ) ≤
      -(θ * (1 - δ)) * (∫ x, χ x * (p4Mol v (μ s) x *
        ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2)) +
      N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ) -
      ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ (μ s) (V s) x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) := by
    intro s
    haveI := h.prob s
    have hfx := p4m_fixed_time hv (h.hm s) hθ hδ (h.bl s) h.hB h.hK (h.bg s) (h.grad s) hχ hχs hχ0 hχ1
    have hA : Integrable (fun x => χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x)) :=
      p4m_int_of_supp (hcχ.mul ((hca.comp (Continuous.prodMk continuous_const continuous_id)).mul
        (hcΛ.comp (Continuous.prodMk continuous_const continuous_id)))) hχs fun x hx => by simp [hx]
    have hWi : Integrable (fun x => χ x * (p4Mol v (μ s) x * W s x / θ)) :=
      p4m_int_of_supp (hcχ.mul (((hcu.comp (Continuous.prodMk continuous_const continuous_id)).mul
        (hcW.comp (Continuous.prodMk continuous_const continuous_id))).div_const θ)) hχs
        fun x hx => by simp [hx]
    have hWle : ∫ x, χ x * (p4Mol v (μ s) x * W s x / θ) ≤ 0 := by
      refine integral_nonpos fun x => ?_
      have := h.pos_u hv s x
      have := h.Wle s x
      have := hχ0 x
      have : p4Mol v (μ s) x * W s x / θ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (h.pos_u hv s x).le (h.Wle s x)) hθ.le
      exact mul_nonpos_of_nonneg_of_nonpos (hχ0 x) this
    have e : ∫ x, χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x +
        p4Mol v (μ s) x * W s x / θ) =
        (∫ x, χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (V s) x)) +
          ∫ x, χ x * (p4Mol v (μ s) x * W s x / θ) := by
      rw [← integral_add hA hWi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [e]
    linarith
  have hRc : Continuous (fun s : ℝ => -(θ * (1 - δ)) * (∫ x, χ x * (p4Mol v (μ s) x *
        ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2)) +
      N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ) -
      ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ (μ s) (V s) x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) :=
    ((continuous_const.mul hcD).add continuous_const).sub (continuous_finset_sum _ fun k _ => hcE k)
  have hmono := setIntegral_mono_on (hcg.integrableOn_Icc (μ := volume) (a := 0) (b := t))
    (hRc.integrableOn_Icc (μ := volume) (a := 0) (b := t)) measurableSet_Icc
    (fun s _ => hfix s)
  have hRint : ∫ s in Set.Icc (0 : ℝ) t, (-(θ * (1 - δ)) * (∫ x, χ x * (p4Mol v (μ s) x *
        ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2)) +
      N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ) -
      ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ (μ s) (V s) x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) =
      -(θ * (1 - δ)) * (∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ x *
        (p4Mol v (μ s) x * ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2)) +
      t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ)) -
      ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_Lam v θ (μ s) (V s) x *
        fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) := by
    have i1 : IntegrableOn (fun s : ℝ => -(θ * (1 - δ)) * (∫ x, χ x * (p4Mol v (μ s) x *
        ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2))) (Set.Icc (0 : ℝ) t) :=
      (continuous_const.mul hcD).integrableOn_Icc (μ := volume)
    have i2 : IntegrableOn (fun s : ℝ => N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ))
        (Set.Icc (0 : ℝ) t) := continuous_const.integrableOn_Icc (μ := volume)
    have i3 : ∀ k : Fin N × Fin d, IntegrableOn (fun s : ℝ => ∫ x, p4m_Lam v θ (μ s) (V s) x *
        fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x))
        (Set.Icc (0 : ℝ) t) := fun k => (hcE k).integrableOn_Icc (μ := volume)
    have i12 : IntegrableOn (fun s : ℝ => -(θ * (1 - δ)) * (∫ x, χ x * (p4Mol v (μ s) x *
        ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2)) +
        N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ)) (Set.Icc (0 : ℝ) t) := i1.add i2
    rw [integral_sub i12 (integrable_finset_sum _ fun k _ => i3 k), integral_add i1 i2,
      integral_const_mul, integral_finset_sum _ fun k _ => i3 k, setIntegral_const]
    simp [Measure.real, Real.volume_Icc, ht0]
  have h1 := hF.trans_le hmono
  rw [hRint] at h1
  linarith

end

end HRS.MP.SelfSimP4Mol
