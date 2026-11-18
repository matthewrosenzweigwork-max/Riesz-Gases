import HRS.Commutator.Whole.XNRSAux3
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# Packet X-NRS, part 4: the regularised Gagliardo kernel `N_δ(z) = (|z|²+δ²)^{-(d+2σ)/2}`

Facts: positivity, evenness, integrability, the gradient bound `|z||∇N_δ(z)| ≤ (d+2σ) N_δ(z)`.
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

/-- `N_δ(z) = (|z|²+δ²)^{-(d+2σ)/2}`. -/
def xN (d : ℕ) (σ δ : ℝ) (z : Euc d) : ℝ := (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2)

/-- `P_δ(z) = (|z|²+δ²)^{-(d+2σ)/2-1}`, so that `∇N_δ(z) = -(d+2σ) P_δ(z) z`. -/
def xP (d : ℕ) (σ δ : ℝ) (z : Euc d) : ℝ := (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2 - 1)

lemma xN_pos {σ δ : ℝ} (hδ : 0 < δ) (z : Euc d) : 0 < xN d σ δ z :=
  Real.rpow_pos_of_pos (by positivity) _

lemma xP_pos {σ δ : ℝ} (hδ : 0 < δ) (z : Euc d) : 0 < xP d σ δ z :=
  Real.rpow_pos_of_pos (by positivity) _

lemma xN_neg (σ δ : ℝ) (z : Euc d) : xN d σ δ (-z) = xN d σ δ z := by simp [xN]

lemma continuous_xN (σ δ : ℝ) (hδ : 0 < δ) : Continuous (xN d σ δ) := by
  unfold xN
  refine Continuous.rpow_const (by fun_prop) (fun z => Or.inl (by positivity))

lemma continuous_xP (σ δ : ℝ) (hδ : 0 < δ) : Continuous (xP d σ δ) := by
  unfold xP
  refine Continuous.rpow_const (by fun_prop) (fun z => Or.inl (by positivity))

/-- `‖z‖² P ≤ N`. -/
lemma xP_mul_sq_le {σ δ : ℝ} (hδ : 0 < δ) (z : Euc d) : ‖z‖ ^ 2 * xP d σ δ z ≤ xN d σ δ z := by
  unfold xP xN
  have hb : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
  have : (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2 - 1) =
      (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) * (‖z‖ ^ 2 + δ ^ 2)⁻¹ := by
    rw [Real.rpow_sub hb, Real.rpow_one, div_eq_mul_inv]
  rw [this, ← mul_assoc]
  have h1 : ‖z‖ ^ 2 * (‖z‖ ^ 2 + δ ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hb]; nlinarith [sq_nonneg δ]
  have h2 : 0 < (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) := Real.rpow_pos_of_pos hb _
  calc ‖z‖ ^ 2 * ((‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2)) * (‖z‖ ^ 2 + δ ^ 2)⁻¹
      = ((‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2)) * (‖z‖ ^ 2 * (‖z‖ ^ 2 + δ ^ 2)⁻¹) := by ring
    _ ≤ ((‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2)) * 1 := by gcongr
    _ = _ := mul_one _

/-- `(‖z‖²+δ²)^{-r/2}` is integrable for `r > d`. -/
lemma integrable_xrpow {r δ : ℝ} (hδ : 0 < δ) (hr : (d : ℝ) < r) :
    Integrable (fun z : Euc d => (‖z‖ ^ 2 + δ ^ 2) ^ (-r / 2)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := Euc d) (μ := (volume : Measure (Euc d))) (r := r) (by simpa using hr)
  have h2 := (Integrable.comp_smul (μ := (volume : Measure (Euc d))) h (inv_ne_zero hδ.ne')).const_mul (δ ^ (-r))
  refine h2.congr (Eventually.of_forall fun z => ?_)
  simp only
  have hb : 0 < 1 + ‖δ⁻¹ • z‖ ^ 2 := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hδ), mul_pow, inv_pow]
  have : ‖z‖ ^ 2 + δ ^ 2 = δ ^ 2 * (1 + (δ ^ 2)⁻¹ * ‖z‖ ^ 2) := by
    field_simp
    ring
  rw [this, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast δ 2,
    ← Real.rpow_mul hδ.le]
  congr 2
  push_cast
  ring_nf

lemma integrable_xN {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) : Integrable (xN d σ δ) := by
  have := integrable_xrpow (d := d) (r := (d : ℝ) + 2 * σ) hδ (by linarith)
  exact this


lemma hasFDerivAt_xN {σ δ : ℝ} (hδ : 0 < δ) (z : Euc d) :
    HasFDerivAt (xN d σ δ)
      ((-((d : ℝ) + 2 * σ) * xP d σ δ z) • innerSL ℝ z) z := by
  have h1 : HasFDerivAt (fun z : Euc d => ‖z‖ ^ 2 + δ ^ 2) ((2 : ℕ) • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const _
  have hb : (‖z‖ ^ 2 + δ ^ 2) ≠ 0 := by positivity
  have h2 := h1.rpow_const (p := -((d : ℝ) + 2 * σ) / 2) (Or.inl hb)
  have h3 : (-((d : ℝ) + 2 * σ) * xP d σ δ z) • innerSL ℝ z =
      (-((d : ℝ) + 2 * σ) / 2 * (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2 - 1)) •
        ((2 : ℕ) • innerSL ℝ z) := by
    ext u
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, xP, nsmul_eq_mul]
    push_cast
    ring
  rw [h3]
  exact h2

lemma fderiv_xN_apply {σ δ : ℝ} (hδ : 0 < δ) (z u : Euc d) :
    fderiv ℝ (xN d σ δ) z u = -((d : ℝ) + 2 * σ) * xP d σ δ z * inner ℝ z u := by
  rw [(hasFDerivAt_xN hδ z).fderiv]
  exact rfl

lemma integrable_norm_xP {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) :
    Integrable (fun z : Euc d => ‖z‖ * xP d σ δ z) := by
  have h := integrable_xrpow (d := d) (r := (d : ℝ) + 2 * σ + 1) hδ (by linarith)
  refine h.mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact (continuous_norm.mul (continuous_xP σ δ hδ)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (xP_pos hδ z).le)]
    unfold xP
    have hb : 0 < ‖z‖ ^ 2 + δ ^ 2 := by positivity
    have e1 : (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2 - 1) *
        (‖z‖ ^ 2 + δ ^ 2) ^ ((1 : ℝ) / 2) = (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ + 1) / 2) := by
      rw [← Real.rpow_add hb]; congr 1; ring
    have e2 : ‖z‖ ≤ (‖z‖ ^ 2 + δ ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg δ])
    rw [← e1, mul_comm]
    exact mul_le_mul_of_nonneg_left e2 (Real.rpow_nonneg hb.le _)


/-! ### The multipliers `m_δ` and `m_0` -/

/-- `1 - cos(2π⟨z,ξ⟩)`. -/
def xph (ξ z : Euc d) : ℝ := 1 - Real.cos (2 * Real.pi * inner ℝ z ξ)

lemma xph_nonneg (ξ z : Euc d) : 0 ≤ xph ξ z := by
  unfold xph; linarith [Real.cos_le_one (2 * Real.pi * inner ℝ z ξ)]

lemma xph_le_two (ξ z : Euc d) : xph ξ z ≤ 2 := by
  unfold xph; linarith [Real.neg_one_le_cos (2 * Real.pi * inner ℝ z ξ)]

lemma xph_le_sq (ξ z : Euc d) : xph ξ z ≤ 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖z‖ ^ 2 := by
  unfold xph
  have h1 := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * inner ℝ z ξ)
  have h2 : (inner ℝ z ξ) ^ 2 ≤ ‖z‖ ^ 2 * ‖ξ‖ ^ 2 := by
    have := abs_real_inner_le_norm z ξ
    calc (inner ℝ z ξ) ^ 2 = |inner ℝ z ξ| ^ 2 := (sq_abs _).symm
      _ ≤ (‖z‖ * ‖ξ‖) ^ 2 := by gcongr
      _ = _ := by ring
  nlinarith [Real.pi_pos]

lemma continuous_xph (ξ : Euc d) : Continuous (xph ξ) := by
  unfold xph; fun_prop

lemma xph_zero (z : Euc d) : xph (0 : Euc d) z = 0 := by simp [xph]

lemma xph_neg_left (ξ z : Euc d) : xph (-ξ) z = xph ξ z := by simp [xph]

/-- `m_δ(ξ) = ∫ N_δ(z)(1 - cos 2π⟨z,ξ⟩) dz`. -/
def xm (d : ℕ) (σ δ : ℝ) (ξ : Euc d) : ℝ := ∫ z : Euc d, xN d σ δ z * xph ξ z

/-- `m_0(ξ) = ∫ |z|^{-(d+2σ)}(1 - cos 2π⟨z,ξ⟩) dz`. -/
def xm0 (d : ℕ) (σ : ℝ) (ξ : Euc d) : ℝ := ∫ z : Euc d, ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * xph ξ z

lemma integrable_xm_integrand {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) (ξ : Euc d) :
    Integrable (fun z : Euc d => xN d σ δ z * xph ξ z) := by
  refine ((integrable_xN hσ hδ).mul_const 2).mono' ?_ (Eventually.of_forall fun z => ?_)
  · exact ((continuous_xN σ δ hδ).mul (continuous_xph ξ)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (xN_pos hδ z).le (xph_nonneg ξ z))]
    exact mul_le_mul_of_nonneg_left (xph_le_two ξ z) (xN_pos hδ z).le |>.trans (le_of_eq (by ring))

lemma xm_nonneg {σ δ : ℝ} (hδ : 0 < δ) (ξ : Euc d) : 0 ≤ xm d σ δ ξ :=
  integral_nonneg fun z => mul_nonneg (xN_pos hδ z).le (xph_nonneg ξ z)

lemma integrable_xm0_integrand (hd : 1 ≤ d) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ξ : Euc d) :
    Integrable (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * xph ξ z) := by
  have hmeas : AEStronglyMeasurable (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * xph ξ z) volume := by
    refine (Measurable.aestronglyMeasurable ?_)
    exact (measurable_norm.pow_const _).mul (continuous_xph ξ).measurable
  rw [← integrableOn_univ]
  have hu : (Set.univ : Set (Euc d)) = ball 0 1 ∪ (ball 0 1)ᶜ := (Set.union_compl_self _).symm
  rw [hu]
  refine IntegrableOn.union ?_ ?_
  · refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2)
      (α := (d : ℝ) + 2 * σ - 2) (r := 1) (by simpa using hd) (by simp; linarith) ?_ hmeas
    refine Filter.Eventually.of_forall fun z => ?_
    have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
    rcases eq_or_lt_of_le hz0 with h0 | h0
    · rw [← h0]
      simp only [Real.zero_rpow (by linarith : (-((d : ℝ) + 2 * σ)) ≠ 0), zero_mul, norm_zero]
      have : (0 : ℝ) ≤ 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * (0 : ℝ) ^ (-((d : ℝ) + 2 * σ - 2)) := by positivity
      simpa using this
    · rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hz0 _) (xph_nonneg ξ z))]
      calc ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * xph ξ z
          ≤ ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * (2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖z‖ ^ 2) :=
            mul_le_mul_of_nonneg_left (xph_le_sq ξ z) (Real.rpow_nonneg hz0 _)
        _ = 2 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * ‖z‖ ^ (-((d : ℝ) + 2 * σ - 2)) := by
            rw [← Real.rpow_natCast ‖z‖ 2]
            have : ‖z‖ ^ (-((d : ℝ) + 2 * σ - 2)) = ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * ‖z‖ ^ ((2 : ℕ) : ℝ) := by
              rw [← Real.rpow_add h0]; congr 1; push_cast; ring
            rw [this]; ring
  · have hint := integrable_xrpow (d := d) (r := (d : ℝ) + 2 * σ) (δ := 1) one_pos (by linarith)
    have hI : IntegrableOn (fun z : Euc d => (2 * 2 ^ (((d : ℝ) + 2 * σ) / 2)) *
        (‖z‖ ^ 2 + 1 ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2)) ((ball (0 : Euc d) 1)ᶜ) :=
      (hint.const_mul _).integrableOn
    refine hI.mono' hmeas.restrict ?_
    filter_upwards [ae_restrict_mem (measurableSet_ball.compl)] with z hz
    have hz1 : 1 ≤ ‖z‖ := by simpa using hz
    have hz0 : 0 < ‖z‖ := by linarith
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hz0.le _) (xph_nonneg ξ z))]
    have hb : 0 < ‖z‖ ^ 2 + 1 ^ 2 := by positivity
    have h1 : (2 : ℝ) ^ (((d : ℝ) + 2 * σ) / 2) * (‖z‖ ^ 2 + 1 ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) ≥
        ‖z‖ ^ (-((d : ℝ) + 2 * σ)) := by
      have hle : (2 * ‖z‖ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) ≤ (‖z‖ ^ 2 + 1 ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) := by
        apply Real.rpow_le_rpow_of_nonpos hb (by nlinarith) (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      rw [Real.mul_rpow (by norm_num) (by positivity)] at hle
      have e1 : (‖z‖ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) = ‖z‖ ^ (-((d : ℝ) + 2 * σ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hz0.le]; congr 1; push_cast; ring
      rw [e1] at hle
      have e2 : (2 : ℝ) ^ (-((d : ℝ) + 2 * σ) / 2) * (2 : ℝ) ^ (((d : ℝ) + 2 * σ) / 2) = 1 := by
        rw [← Real.rpow_add (by norm_num)]
        have : -((d : ℝ) + 2 * σ) / 2 + ((d : ℝ) + 2 * σ) / 2 = 0 := by ring
        rw [this]; simp
      calc ‖z‖ ^ (-((d : ℝ) + 2 * σ)) = (2 : ℝ) ^ (((d : ℝ) + 2 * σ) / 2) *
            ((2 : ℝ) ^ (-((d : ℝ) + 2 * σ) / 2) * ‖z‖ ^ (-((d : ℝ) + 2 * σ))) := by
              rw [← mul_assoc, mul_comm ((2 : ℝ) ^ (((d : ℝ) + 2 * σ) / 2)), e2, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left hle (by positivity)
    calc ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * xph ξ z ≤ ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * 2 :=
          mul_le_mul_of_nonneg_left (xph_le_two ξ z) (Real.rpow_nonneg hz0.le _)
      _ ≤ _ := by nlinarith


lemma xN_le_pow {σ δ : ℝ} (hσ : 0 < σ) (hδ : 0 < δ) {z : Euc d} (hz : z ≠ 0) :
    xN d σ δ z ≤ ‖z‖ ^ (-((d : ℝ) + 2 * σ)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h : (‖z‖ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) = ‖z‖ ^ (-((d : ℝ) + 2 * σ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; congr 1; push_cast; ring
  rw [← h]
  unfold xN
  apply Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg δ])
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma xm_le_xm0 (hd : 1 ≤ d) {σ δ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (hδ : 0 < δ) (ξ : Euc d) :
    xm d σ δ ξ ≤ xm0 d σ ξ := by
  unfold xm xm0
  refine integral_mono (integrable_xm_integrand hσ0 hδ ξ) (integrable_xm0_integrand hd hσ0 hσ1 ξ)
    fun z => ?_
  by_cases hz : z = 0
  · subst hz; simp [xph]
  · exact mul_le_mul_of_nonneg_right (xN_le_pow hσ0 hδ hz) (xph_nonneg ξ z)

lemma tendsto_xm (hd : 1 ≤ d) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (ξ : Euc d) :
    Tendsto (fun δ : ℝ => xm d σ δ ξ) (𝓝[>] 0) (𝓝 (xm0 d σ ξ)) := by
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  unfold xm xm0
  refine tendsto_integral_filter_of_dominated_convergence
    (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * xph ξ z) ?_ ?_
    (integrable_xm0_integrand hd hσ0 hσ1 ξ) ?_
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact ((integrable_xm_integrand hσ0 hδ ξ).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with δ hδ
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (xN_pos hδ z).le (xph_nonneg ξ z))]
    by_cases hz : z = 0
    · subst hz; simp [xph]
    · exact mul_le_mul_of_nonneg_right (xN_le_pow hσ0 hδ hz) (xph_nonneg ξ z)
  · have hz : ∀ᵐ z : Euc d, z ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [hz] with z hz
    refine Tendsto.mul ?_ tendsto_const_nhds
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hc : ContinuousAt (fun δ : ℝ => (‖z‖ ^ 2 + δ ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2)) 0 := by
      apply ContinuousAt.rpow_const (by fun_prop) (Or.inl (by positivity))
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hlim : (‖z‖ ^ 2 + (0 : ℝ) ^ 2) ^ (-((d : ℝ) + 2 * σ) / 2) = ‖z‖ ^ (-((d : ℝ) + 2 * σ)) := by
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; congr 1; push_cast; ring
    rw [hlim] at this
    exact this


lemma xm0_smul {σ : ℝ} (t : ℝ) (ht : 0 < t) (ξ : Euc d) :
    xm0 d σ (t • ξ) = t ^ (2 * σ) * xm0 d σ ξ := by
  unfold xm0
  set G : Euc d → ℝ := fun w => ‖w‖ ^ (-((d : ℝ) + 2 * σ)) * xph ξ w with hG
  have h1 : ∀ z : Euc d, ‖z‖ ^ (-((d : ℝ) + 2 * σ)) * xph (t • ξ) z =
      t ^ ((d : ℝ) + 2 * σ) * G (t • z) := by
    intro z
    simp only [hG, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    rw [Real.mul_rpow ht.le (norm_nonneg z), Real.rpow_neg ht.le]
    have : xph (t • ξ) z = xph ξ (t • z) := by
      simp [xph, inner_smul_right, inner_smul_left, mul_comm]
    rw [this]
    have hp : 0 < t ^ ((d : ℝ) + 2 * σ) := Real.rpow_pos_of_pos ht _
    field_simp
  simp_rw [h1]
  rw [integral_const_mul, Measure.integral_comp_smul volume G t]
  have hfin : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  rw [hfin, abs_of_nonneg (inv_nonneg.2 (pow_nonneg ht.le _)), smul_eq_mul]
  have : t ^ ((d : ℝ) + 2 * σ) * (t ^ d)⁻¹ = t ^ (2 * σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]; congr 1; ring
  rw [← mul_assoc, this]

lemma xm0_rot {σ : ℝ} (T : Euc d ≃ₗᵢ[ℝ] Euc d) (ξ : Euc d) : xm0 d σ (T ξ) = xm0 d σ ξ := by
  unfold xm0
  have hmp : MeasurePreserving T volume volume := T.measurePreserving
  have hme : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  rw [← hmp.integral_comp hme]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [xph, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.inner_map_map]

lemma xm0_eq (hd : 1 ≤ d) {σ : ℝ} (hσ : 0 < σ) (ξ : Euc d) :
    xm0 d σ ξ = xm0 d σ (xe ⟨0, hd⟩) * ‖ξ‖ ^ (2 * σ) := by
  by_cases hξ : ξ = 0
  · subst hξ
    simp [xm0, xph_zero, Real.zero_rpow (by linarith : 2 * σ ≠ 0)]
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    set η : Euc d := ‖ξ‖⁻¹ • ξ with hη
    have hηn : ‖η‖ = 1 := by
      rw [hη, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have he0 : ‖(xe ⟨0, hd⟩ : Euc d)‖ = 1 := by simp [xe]
    have hξη : ξ = ‖ξ‖ • η := by rw [hη, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    set T : Euc d ≃ₗᵢ[ℝ] Euc d := Submodule.reflection (ℝ ∙ (η - xe ⟨0, hd⟩))ᗮ with hT
    have hTη : T η = xe ⟨0, hd⟩ := Submodule.reflection_sub (by rw [hηn, he0])
    have : xm0 d σ η = xm0 d σ (xe ⟨0, hd⟩) := by rw [← hTη, xm0_rot]
    conv_lhs => rw [hξη]
    rw [xm0_smul _ hn, this]; ring

lemma xm0_pos (hd : 1 ≤ d) {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    0 < xm0 d σ (xe ⟨0, hd⟩) := by
  unfold xm0
  have hint := integrable_xm0_integrand hd hσ0 hσ1 (xe (⟨0, hd⟩ : Fin d))
  rw [integral_pos_iff_support_of_nonneg (fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg z) _)
    (xph_nonneg _ z)) hint]
  set U : Set (Euc d) := {z | 0 < inner ℝ z (xe (⟨0, hd⟩ : Fin d)) ∧ inner ℝ z (xe (⟨0, hd⟩ : Fin d)) < 1 / 2}
  have hUo : IsOpen U := by
    have hc : Continuous (fun z : Euc d => inner ℝ z (xe (⟨0, hd⟩ : Fin d))) :=
      continuous_id.inner continuous_const
    exact IsOpen.inter (isOpen_lt continuous_const hc) (isOpen_lt hc continuous_const)
  have hUne : U.Nonempty := by
    refine ⟨(1 / 4 : ℝ) • xe (⟨0, hd⟩ : Fin d), ?_⟩
    simp [U, inner_smul_left, xe]
    norm_num
  have hsub : U ⊆ Function.support (fun z : Euc d => ‖z‖ ^ (-((d : ℝ) + 2 * σ)) *
      xph (xe (⟨0, hd⟩ : Fin d)) z) := by
    intro z hz
    obtain ⟨h1, h2⟩ := hz
    have hz0 : z ≠ 0 := by
      rintro rfl; simp at h1
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
    refine ⟨(Real.rpow_pos_of_pos hn _).ne', ?_⟩
    unfold xph
    have : Real.cos (2 * Real.pi * inner ℝ z (xe (⟨0, hd⟩ : Fin d))) < 1 := by
      rw [← Real.cos_zero]
      apply Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0)
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    linarith
  exact lt_of_lt_of_le (hUo.measure_pos volume hUne) (measure_mono hsub)

end HRS.Commutator.Whole.XNRS
