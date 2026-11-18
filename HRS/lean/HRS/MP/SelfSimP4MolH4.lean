import HRS.MP.SelfSimP4MolH3

/-!
# MPP4MOL stage 5c (17): the abstract mollified dissipation inequality
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

theorem P4MolData.diss_eq (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (s : ℝ) :
    p4Diss θ (V s) (p4Mol v (μ s)) = ∫⁻ x, ENNReal.ofReal (p4Mol v (μ s) x *
      ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2) := by
  haveI := h.prob s
  unfold p4Diss
  refine lintegral_congr fun x => ?_
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [p4m_fderiv_mol_basis hv, (h.grad s x).fderiv]
  simp only [ContinuousLinearMap.neg_apply]
  rw [p4m_inner_single]
  unfold p4m_ell
  rw [div_eq_inv_mul, div_eq_inv_mul]
  ring

theorem P4MolData.cont_Dpt (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) :
    Continuous (Function.uncurry fun (s : ℝ) (x : EucConfig d N) =>
      p4Mol v (μ s) x * ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2) :=
  (h.cont_u hv).mul (continuous_finset_sum _ fun k _ => (h.cont_ell hv k).pow 2)

theorem P4MolData.measurable_diss (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) :
    Measurable (fun s => p4Diss θ (V s) (p4Mol v (μ s))) := by
  have : (fun s => p4Diss θ (V s) (p4Mol v (μ s))) = fun s => ∫⁻ x, ENNReal.ofReal (p4Mol v (μ s) x *
      ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2) := funext fun s => h.diss_eq hv s
  rw [this]
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × EucConfig d N =>
    ENNReal.ofReal (p4Mol v (μ p.1) p.2 * ∑ k : Fin N × Fin d, p4m_ell v θ (μ p.1) (b p.1) k p.2 ^ 2))
    (ENNReal.measurable_ofReal.comp (h.cont_Dpt hv).measurable)

theorem P4MolData.main (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (hθ : 0 < θ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ s in Set.Icc (0 : ℝ) t, p4Diss θ (V s) (p4Mol v (μ s)) ≠ ⊤ ∧
      p4Free θ (V t) (p4Mol v (μ t)) +
        θ * (1 - δ) * (∫⁻ s in Set.Icc (0 : ℝ) t, p4Diss θ (V s) (p4Mol v (μ s))).toReal ≤
      p4Free θ (V 0) (p4Mol v (μ 0)) +
        t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ)) := by
  have hκ : 0 < θ * (1 - δ) := mul_pos hθ (by linarith)
  have ht0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  set c : ℝ := N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ) with hc
  set Dpt : ℝ → EucConfig d N → ℝ := fun s x => p4Mol v (μ s) x *
    ∑ k : Fin N × Fin d, p4m_ell v θ (μ s) (b s) k x ^ 2 with hDpt
  have hDnn : ∀ s x, 0 ≤ Dpt s x := fun s x =>
    mul_nonneg (h.pos_u hv s x).le (Finset.sum_nonneg fun k _ => sq_nonneg _)
  set χ : ℕ → EucConfig d N → ℝ := fun n => p4m_chi ((n : ℝ) + 1) with hχ
  have hχc : ∀ n, Continuous (χ n) := fun n => (p4m_contDiff_chi (R := (n : ℝ) + 1)).continuous
  have hχs : ∀ n, HasCompactSupport (χ n) := fun n => p4m_hasCompactSupport_chi (by positivity)
  have hχlim : ∀ x, ∀ᶠ n in atTop, χ n x = 1 := by
    intro x
    obtain ⟨n0, hn0⟩ := exists_nat_gt (p4m_q x)
    filter_upwards [Filter.eventually_ge_atTop n0] with n hn
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
    have hq := p4m_q_nonneg x
    have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact p4m_chi_eq_one (R := (n : ℝ) + 1) (by positivity) (by nlinarith)
  -- the quantities along the cut-off sequence
  set Sig : ℕ → ℝ := fun n => ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x,
    p4m_Lam v θ (μ s) (V s) x * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
    (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) with hSig
  set Y : ℕ → ℝ := fun n => (∫ x, χ n x * p4m_Phi v θ μ V 0 x) - (∫ x, χ n x * p4m_Phi v θ μ V t x) +
    t * c - Sig n with hY
  set Yinf : ℝ := (∫ x, p4m_Phi v θ μ V 0 x) - (∫ x, p4m_Phi v θ μ V t x) + t * c with hYinf
  have hYlim : Tendsto Y atTop (𝓝 Yinf) := by
    have h0 := h.tendsto_free hv hθ 0
    have h1 := h.tendsto_free hv hθ t
    have h2 := h.tendsto_E hv hθ t
    have := ((h0.sub h1).add_const (t * c)).sub h2
    simpa using this
  set a : ℕ → ℝ := fun n => Y n / (θ * (1 - δ)) with ha
  have halim : Tendsto a atTop (𝓝 (Yinf / (θ * (1 - δ)))) := hYlim.div_const _
  have hbound : ∀ n, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ n x * Dpt s x ≤ a n := by
    intro n
    have hti := h.time_ineq hv hθ hδ (p4m_contDiff_chi (R := (n : ℝ) + 1))
      (hχs n) (fun x => p4m_chi_nonneg _ _) (fun x => p4m_chi_le_one _ _) ht
    show _ ≤ Y n / (θ * (1 - δ))
    rw [le_div_iff₀ hκ]
    have : (∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ n x * Dpt s x) * (θ * (1 - δ)) =
        (θ * (1 - δ)) * (∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ n x * Dpt s x) := mul_comm _ _
    rw [this]
    simp only [hY, hSig, hχ]
    linarith
  -- the limit is nonnegative
  have hI0 : ∀ n, 0 ≤ ∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ n x * Dpt s x := fun n =>
    setIntegral_nonneg measurableSet_Icc fun s _ =>
      integral_nonneg fun x => mul_nonneg (p4m_chi_nonneg _ _) (hDnn s x)
  have hLr0 : 0 ≤ Yinf / (θ * (1 - δ)) :=
    ge_of_tendsto halim (Filter.Eventually.of_forall fun n => (hI0 n).trans (hbound n))
  have hF := p4m_fatou_chain (D := Dpt) (h.cont_Dpt hv) hDnn hχc hχs (fun n x => p4m_chi_nonneg _ _) hχlim t
    halim hbound
  have hdiss : ∀ s, p4Diss θ (V s) (p4Mol v (μ s)) = ∫⁻ x, ENNReal.ofReal (Dpt s x) := fun s => h.diss_eq hv s
  simp only [hdiss]
  have hle : ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ x, ENNReal.ofReal (Dpt s x) ≤
      ENNReal.ofReal (Yinf / (θ * (1 - δ))) := hF
  refine ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle, ?_⟩
  have htr := ENNReal.toReal_le_of_le_ofReal hLr0 hle
  have hfin : θ * (1 - δ) * (∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ x, ENNReal.ofReal (Dpt s x)).toReal ≤ Yinf := by
    have := mul_le_mul_of_nonneg_left htr hκ.le
    rwa [mul_div_cancel₀ _ hκ.ne'] at this
  have e1 : p4Free θ (V t) (p4Mol v (μ t)) = ∫ x, p4m_Phi v θ μ V t x := rfl
  have e2 : p4Free θ (V 0) (p4Mol v (μ 0)) = ∫ x, p4m_Phi v θ μ V 0 x := rfl
  rw [e1, e2]
  simp only [hYinf] at hfin
  linarith

end

end HRS.MP.SelfSimP4Mol
