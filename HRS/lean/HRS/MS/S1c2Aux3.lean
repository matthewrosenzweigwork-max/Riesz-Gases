import HRS.MS.S1c2Aux2
import HRS.Whole.Adjoint

/-!
# S1C2 aux 3: `fracLp_rep`, the `L^p` fractional derivative by central differences

For `r > 0`, `ℓ = ⌊r⌋ + 1`, `1 < p < ∞` and `v ∈ C^ℓ` with `v, D^ℓ v ∈ L^p` there is `w ∈ L^p` with
`IsFracDerivRep r v w` and `‖w‖_p ≤ C(d, r, p) (‖v‖_p + ‖D^ℓ v‖_p)`.  (The `L^p` analogue of `HRS.U8.u8_core`.)
Documented adjustment: the exponent range is `1 < p < ∞` (not `1 ≤ p`): the two uses have `p > 2`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace HRS.S1C2

open HRS.U8

variable {d : ℕ}

theorem s1c2_fd_memLp {p : ℝ} (hp : 1 ≤ p) (L : List (EuclideanSpace ℝ (Fin d)))
    (f : EuclideanSpace ℝ (Fin d) → ℂ) (hc : Continuous f)
    (hf : MemLp f (ENNReal.ofReal p) volume) : MemLp (u8_fd L f) (ENNReal.ofReal p) volume := by
  exact lt_of_le_of_lt (s1c2_fd_lp_crude hp L f hc)
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (by simp)) hf)

/-- The adjoint identity for iterated differences, in `L^p × L^q`. -/
theorem s1c2_fd_adjoint {p q : ℝ} (hpq : p.HolderConjugate q) (L : List (EuclideanSpace ℝ (Fin d))) :
    ∀ (f g : EuclideanSpace ℝ (Fin d) → ℂ), Continuous f → MemLp f (ENNReal.ofReal p) volume →
      Continuous g → MemLp g (ENNReal.ofReal q) volume →
      ∫ x, f x * u8_fd L g x = ∫ x, u8_fd (L.map Neg.neg) f x * g x := by
  have := hpq.ennrealOfReal
  induction L with
  | nil => intro f g _ _ _ _; rfl
  | cons h hs ih =>
    intro f g hf hfp hg hgq
    rw [u8_fd_cons]
    have hg' : Continuous (fun x => g (x + h) - g x) :=
      (hg.comp (continuous_id.add continuous_const)).sub hg
    have hgs : MemLp (fun x => g (x + h)) (ENNReal.ofReal q) volume :=
      hgq.comp_measurePreserving (measurePreserving_add_right volume h)
    have hgq' : MemLp (fun x => g (x + h) - g x) (ENNReal.ofReal q) volume := hgs.sub hgq
    rw [ih f _ hf hfp hg' hgq']
    set F := u8_fd (hs.map Neg.neg) f with hF
    have hFc : Continuous F := s1c2_fd_cont _ hf
    have hFp : MemLp F (ENNReal.ofReal p) volume := s1c2_fd_memLp hpq.lt.le _ f hf hfp
    have hFs : MemLp (fun x => F (x + -h)) (ENNReal.ofReal p) volume :=
      hFp.comp_measurePreserving (measurePreserving_add_right volume (-h))
    have hcomm : u8_fd ((h :: hs).map Neg.neg) f = fun x => F (x + -h) - F x := by
      rw [List.map_cons, u8_fd_cons]
      exact u8_fd_comm _ f (-h)
    rw [hcomm]
    have i1 : Integrable (fun x => F x * g (x + h)) := hFp.integrable_mul hgs
    have i2 : Integrable (fun x => F x * g x) := hFp.integrable_mul hgq
    have i3 : Integrable (fun x => F (x + -h) * g x) := hFs.integrable_mul hgq
    have e1 : ∫ x, F x * (g (x + h) - g x) = (∫ x, F x * g (x + h)) - ∫ x, F x * g x := by
      rw [← integral_sub i1 i2]
      congr 1; funext x; ring
    have e2 : ∫ x, (F (x + -h) - F x) * g x = (∫ x, F (x + -h) * g x) - ∫ x, F x * g x := by
      rw [← integral_sub i3 i2]
      congr 1; funext x; ring
    have e3 : ∫ x, F x * g (x + h) = ∫ x, F (x + -h) * g x := by
      have := integral_add_right_eq_self (μ := volume) (fun x => F (x + -h) * g x) h
      simp only [add_neg_cancel_right] at this
      exact this
    rw [e1, e2, e3]

/-- The singular integral `Λ u x = ∫ |y|^{-d-r} Δ_y^{(2ℓ)} u (x) dy` (Bochner). -/
def s1c2_Lam (d : ℕ) (r : ℝ) (ℓ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : EuclideanSpace ℝ (Fin d) → E) (x : EuclideanSpace ℝ (Fin d)) : E :=
  ∫ y, ‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) u x

theorem s1c2_enorm_term (r : ℝ) (ℓ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : EuclideanSpace ℝ (Fin d) → E) (x y : EuclideanSpace ℝ (Fin d)) :
    ‖‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) u x‖ₑ =
      pw (-((d : ℝ) + r)) y * ‖u8_fd (u8_L ℓ y) u x‖ₑ := by
  rw [enorm_smul, Real.enorm_eq_ofReal (Real.rpow_nonneg (norm_nonneg _) _)]
  rfl

theorem s1c2_term_aesm (r : ℝ) (ℓ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : EuclideanSpace ℝ (Fin d) → E} (hu : Continuous u) (x : EuclideanSpace ℝ (Fin d)) :
    AEStronglyMeasurable (fun y : EuclideanSpace ℝ (Fin d) =>
      ‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) u x) volume :=
  (measurable_norm.pow_const _).aestronglyMeasurable.smul (u8_L_cont ℓ hu x).aestronglyMeasurable

theorem s1c2_W_meas (r : ℝ) (ℓ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : EuclideanSpace ℝ (Fin d) → E} (hu : Continuous u) : Measurable (s1c2_W d r ℓ u) := by
  have : Measurable (fun q : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) =>
      pw (-((d : ℝ) + r)) q.2 * ‖u8_fd (u8_L ℓ q.2) u q.1‖ₑ) :=
    ((pw_measurable _).comp measurable_snd).mul (s1c2_G_meas ℓ hu)
  exact this.lintegral_prod_right'

theorem s1c2_Lam_norm_le (r : ℝ) (ℓ : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : EuclideanSpace ℝ (Fin d) → E} (hu : Continuous u) (x : EuclideanSpace ℝ (Fin d)) :
    ‖s1c2_Lam d r ℓ u x‖ ≤ (s1c2_W d r ℓ u x).toReal := by
  unfold s1c2_Lam
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [integral_norm_eq_lintegral_enorm (s1c2_term_aesm r ℓ hu x)]
  refine le_of_eq (congrArg ENNReal.toReal ?_)
  unfold s1c2_W
  refine lintegral_congr (fun y => ?_)
  exact s1c2_enorm_term r ℓ u x y

theorem s1c2_W_lt_top (hd : 1 ≤ d) {r p : ℝ} (hr : 0 < r) (hp : 1 < p) (ℓ : ℕ) (hrℓ : r < ℓ)
    {v : EuclideanSpace ℝ (Fin d) → ℂ} (hv : ContDiff ℝ ℓ v)
    (hv0 : MemLp v (ENNReal.ofReal p) volume)
    (hv1 : MemLp (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume) :
    ∫⁻ x, (s1c2_W d r ℓ v x) ^ p < ∞ := by
  have hp0 : 0 < p := by linarith
  obtain ⟨c₁, c₂, h1, h2, h⟩ := s1c2_W_bound hd hr hp ℓ hrℓ
  refine lt_of_le_of_lt (h ℂ v hv) ?_
  have i0 : Ip volume p v < ∞ := by
    rw [s1c2_Ip_eq _ hp0 _ hv0.aestronglyMeasurable]
    exact ENNReal.rpow_lt_top_of_nonneg hp0.le hv0.ne
  have i1 : Ip volume p (iteratedFDeriv ℝ ℓ v) < ∞ := by
    rw [s1c2_Ip_eq _ hp0 _ hv1.aestronglyMeasurable]
    exact ENNReal.rpow_lt_top_of_nonneg hp0.le hv1.ne
  exact ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top h1.lt_top i1, ENNReal.mul_lt_top h2.lt_top i0⟩

theorem s1c2_Wr_memLp (hd : 1 ≤ d) {r p : ℝ} (hr : 0 < r) (hp : 1 < p) (ℓ : ℕ) (hrℓ : r < ℓ)
    {v : EuclideanSpace ℝ (Fin d) → ℂ} (hv : ContDiff ℝ ℓ v)
    (hv0 : MemLp v (ENNReal.ofReal p) volume)
    (hv1 : MemLp (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume) :
    MemLp (fun x => (s1c2_W d r ℓ v x).toReal) (ENNReal.ofReal p) volume := by
  have hp0 : 0 < p := by linarith
  have hfin := s1c2_W_lt_top hd hr hp ℓ hrℓ hv hv0 hv1
  have hm : Measurable (fun x => (s1c2_W d r ℓ v x).toReal) :=
    (s1c2_W_meas r ℓ hv.continuous).ennreal_toReal
  unfold MemLp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
    hm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
  refine ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_of_lt (lt_of_le_of_lt ?_ hfin))
  refine lintegral_mono (fun x => ENNReal.rpow_le_rpow ?_ hp0.le)
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

theorem s1c2_duality (hd : 1 ≤ d) {r p : ℝ} (hr : 0 < r) (hp : 1 < p) (ℓ : ℕ) (hrℓ : r < ℓ)
    (hℓ : 1 ≤ ℓ) {v : EuclideanSpace ℝ (Fin d) → ℂ} (hv : ContDiff ℝ ℓ v)
    (hv0 : MemLp v (ENNReal.ofReal p) volume)
    (hv1 : MemLp (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume)
    (φ : SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ) :
    Integrable (fun x => v x * s1c2_Lam d r ℓ φ x) ∧
      Integrable (fun x => s1c2_Lam d r ℓ v x * φ x) ∧
      ∫ x, v x * s1c2_Lam d r ℓ φ x = ∫ x, s1c2_Lam d r ℓ v x * φ x := by
  have hpq := Real.HolderConjugate.conjExponent hp
  set q := Real.conjExponent p with hq
  have hq1 : 1 < q := hpq.symm.lt
  have hq0 : 0 < q := by linarith
  have hp0 : 0 < p := by linarith
  have hpqE := hpq.ennrealOfReal
  have hvc : Continuous v := hv.continuous
  obtain ⟨b2, hb2, hb2d, hb2r⟩ := u8_d_param hd r hr
  obtain ⟨C2, hC2nn, hC2⟩ := u8_pointwise hd r b2 hr hb2 hb2d ℓ ℓ hℓ hrℓ (by omega)
  obtain ⟨Bφ, hBφ, hφ0, hφ1⟩ := u8_schwartz_bounds φ ℓ b2 hb2.le
  have hφs : ContDiff ℝ ℓ (⇑φ) := by exact_mod_cast φ.smooth ℓ
  have hPφ := fun x => hC2 ℂ (⇑φ) Bφ hBφ hφs hφ0 hφ1 x
  have hdec : MemLp (fun x : EuclideanSpace ℝ (Fin d) => (1 + ‖x‖) ^ (-(b2 + r)))
      (ENNReal.ofReal q) volume := by
    refine u8_decay_memLp (b2 + r) q hq0 ?_
    have : (0 : ℝ) < b2 + r := by linarith
    nlinarith
  have hmaj1 : Integrable (fun x => ‖v x‖ * (C2 * Bφ * (1 + ‖x‖) ^ (-(b2 + r)))) :=
    hv0.norm.integrable_mul (hdec.const_mul (C2 * Bφ))
  have hmaj2 : Integrable (fun x => (s1c2_W d r ℓ v x).toReal * ‖φ x‖) :=
    (s1c2_Wr_memLp hd hr hp ℓ hrℓ hv hv0 hv1).integrable_mul (φ.memLp (ENNReal.ofReal q) volume).norm
  have hIA : Integrable (Function.uncurry fun x y => v x * (‖y‖ ^ (-((d : ℝ) + r)) •
      u8_fd (u8_L ℓ y) (⇑φ) x)) ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
    have hmφ : Measurable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) y =>
        ‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) (⇑φ) x) :=
      ((measurable_norm.pow_const _).comp measurable_snd).smul
        ((u8_L_cont_joint ℓ φ.continuous).comp continuous_swap).measurable
    have hm : AEStronglyMeasurable (Function.uncurry fun x y => v x * (‖y‖ ^ (-((d : ℝ) + r)) •
        u8_fd (u8_L ℓ y) (⇑φ) x)) ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) :=
      ((hvc.measurable.comp measurable_fst).mul hmφ).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨Filter.Eventually.of_forall (fun x => (hPφ x).1.const_mul (v x)), ?_⟩
    refine Integrable.mono' hmaj1 hm.norm.integral_prod_right' (Filter.Eventually.of_forall
      (fun x => ?_))
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    simp only [Function.uncurry, norm_mul]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hPφ x).2.1 (norm_nonneg _)
  have hIB : Integrable (Function.uncurry fun x y => (‖y‖ ^ (-((d : ℝ) + r)) •
      u8_fd (u8_L ℓ y) v x) * φ x) ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) := by
    have hmv : Measurable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) y =>
        ‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) v x) :=
      ((measurable_norm.pow_const _).comp measurable_snd).smul
        ((u8_L_cont_joint ℓ hvc).comp continuous_swap).measurable
    have hm : AEStronglyMeasurable (Function.uncurry fun x y => (‖y‖ ^ (-((d : ℝ) + r)) •
        u8_fd (u8_L ℓ y) v x) * φ x) ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume) :=
      (hmv.mul (φ.continuous.measurable.comp measurable_fst)).aestronglyMeasurable
    rw [integrable_prod_iff hm]
    refine ⟨?_, ?_⟩
    · have hWm := s1c2_W_meas r ℓ hvc
      have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), s1c2_W d r ℓ v x < ∞ := by
        have h1 := ae_lt_top (hWm.pow_const p)
          (s1c2_W_lt_top hd hr hp ℓ hrℓ hv hv0 hv1).ne
        filter_upwards [h1] with x hx
        exact (ENNReal.rpow_lt_top_iff_of_pos hp0).1 hx
      filter_upwards [hae] with x hx
      have hint : Integrable (fun y => ‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) v x) := by
        refine ⟨s1c2_term_aesm r ℓ hvc x, ?_⟩
        unfold HasFiniteIntegral
        calc ∫⁻ y, ‖‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) v x‖ₑ = s1c2_W d r ℓ v x :=
              lintegral_congr (fun y => s1c2_enorm_term r ℓ v x y)
          _ < ∞ := hx
      exact hint.mul_const (φ x)
    · refine Integrable.mono' hmaj2 hm.norm.integral_prod_right' (Filter.Eventually.of_forall
        (fun x => ?_))
      rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
      simp only [Function.uncurry, norm_mul]
      rw [integral_mul_const]
      refine mul_le_mul_of_nonneg_right (le_of_eq ?_) (norm_nonneg _)
      rw [integral_norm_eq_lintegral_enorm (s1c2_term_aesm r ℓ hvc x)]
      refine congrArg ENNReal.toReal ?_
      exact lintegral_congr (fun y => s1c2_enorm_term r ℓ v x y)
  have e1 : ∀ x, v x * s1c2_Lam d r ℓ φ x =
      ∫ y, v x * (‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) (⇑φ) x) :=
    fun x => (integral_const_mul _ _).symm
  have e2 : ∀ x, s1c2_Lam d r ℓ v x * φ x =
      ∫ y, (‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) v x) * φ x :=
    fun x => (integral_mul_const _ _).symm
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [e1]
    exact hIA.integral_prod_left
  · simp_rw [e2]
    exact hIB.integral_prod_left
  · simp_rw [e1, e2]
    rw [integral_integral_swap hIA, integral_integral_swap hIB]
    congr 1; funext y
    have hadj := s1c2_fd_adjoint hpq (u8_L ℓ y) v (⇑φ) hvc hv0 φ.continuous (φ.memLp (ENNReal.ofReal q) volume)
    rw [u8_fd_perm (u8_L_neg_perm ℓ y) v] at hadj
    have s1 : ∀ x, v x * (‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) (⇑φ) x) =
        ‖y‖ ^ (-((d : ℝ) + r)) • (v x * u8_fd (u8_L ℓ y) (⇑φ) x) := fun x => mul_smul_comm _ _ _
    have s2 : ∀ x, (‖y‖ ^ (-((d : ℝ) + r)) • u8_fd (u8_L ℓ y) v x) * φ x =
        ‖y‖ ^ (-((d : ℝ) + r)) • (u8_fd (u8_L ℓ y) v x * φ x) := fun x => smul_mul_assoc _ _ _
    simp_rw [s1, s2]
    rw [integral_smul, integral_smul, hadj]

theorem s1c2_rpow_add_inv_le {p : ℝ} (hp : 1 ≤ p) (x y : ℝ≥0∞) :
    (x + y) ^ (1 / p) ≤ x ^ (1 / p) + y ^ (1 / p) := by
  have hp0 : 0 < p := by linarith
  have h := ENNReal.add_rpow_le_rpow_add (x ^ (1 / p)) (y ^ (1 / p)) hp
  rw [← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h
  have e : 1 / p * p = 1 := by field_simp
  rw [e, ENNReal.rpow_one, ENNReal.rpow_one] at h
  calc (x + y) ^ (1 / p) ≤ ((x ^ (1 / p) + y ^ (1 / p)) ^ p) ^ (1 / p) :=
        ENNReal.rpow_le_rpow h (by positivity)
    _ = _ := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]

/-- **`fracLp_rep`**: the `L^p` analogue of `HRS.U8.u8_core`.  For `r > 0`, `ℓ = ⌊r⌋ + 1`, `1 < p < ∞`
and `v ∈ C^ℓ` with `v, D^ℓ v ∈ L^p` there is `w ∈ L^p` with `IsFracDerivRep r v w`
(both integrability conclusions included) and `‖w‖_p ≤ C(d,r,p) (‖v‖_p + ‖D^ℓ v‖_p)`. -/
theorem fracLp_rep (hd : 1 ≤ d) {r p : ℝ} (hr : 0 < r) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ((⌊r⌋₊ + 1 : ℕ) : WithTop ℕ∞) v →
      MemLp v (ENNReal.ofReal p) volume →
      MemLp (iteratedFDeriv ℝ (⌊r⌋₊ + 1) v) (ENNReal.ofReal p) volume →
      ∃ w : EuclideanSpace ℝ (Fin d) → ℝ, AEStronglyMeasurable w volume ∧
        HRS.Whole.IsFracDerivRep r v w ∧ MemLp w (ENNReal.ofReal p) volume ∧
        eLpNorm w (ENNReal.ofReal p) volume ≤ ENNReal.ofReal C *
          (eLpNorm v (ENNReal.ofReal p) volume +
            eLpNorm (iteratedFDeriv ℝ (⌊r⌋₊ + 1) v) (ENNReal.ofReal p) volume) := by
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℕ, ℓ = ⌊r⌋₊ + 1 := ⟨_, rfl⟩
  rw [← hℓ]
  have hrℓ : r < ℓ := by rw [hℓ]; exact_mod_cast Nat.lt_floor_add_one r
  have hm : 1 ≤ ℓ := by omega
  have hαm : r < 2 * (ℓ : ℝ) := by
    have : (1 : ℝ) ≤ ℓ := by exact_mod_cast hm
    linarith
  have hp0 : 0 < p := by linarith
  obtain ⟨M, hM0, hM⟩ := u8_sym_eq hd ℓ hm r hr hαm
  obtain ⟨c₁, c₂, hc₁, hc₂, hW⟩ := s1c2_W_bound hd hr hp ℓ hrℓ
  have ha1t : c₁ ^ (1 / p) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hc₁
  have ha2t : c₂ ^ (1 / p) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hc₂
  refine ⟨M⁻¹ * ((c₁ ^ (1 / p)).toReal + (c₂ ^ (1 / p)).toReal), by positivity, ?_⟩
  intro v hv hv0 hv1
  have hvc : Continuous v := hv.continuous
  have hMi : (0 : ℝ) ≤ M⁻¹ := inv_nonneg.2 hM0.le
  have hΛm : AEStronglyMeasurable (fun x => M⁻¹ * s1c2_Lam d r ℓ v x) volume :=
    (u8_Lam_aesm ℓ r v hvc).const_mul M⁻¹
  -- the `L^p` bound
  have hpt : ∀ x, ‖M⁻¹ * s1c2_Lam d r ℓ v x‖ₑ ≤ ENNReal.ofReal M⁻¹ * s1c2_W d r ℓ v x := by
    intro x
    rw [enorm_mul, Real.enorm_eq_ofReal hMi]
    refine mul_le_mul_right ?_ _
    unfold s1c2_Lam
    exact (enorm_integral_le_lintegral_enorm _).trans
      (le_of_eq (lintegral_congr (fun y => s1c2_enorm_term r ℓ v x y)))
  have hlp : ∫⁻ x, ‖M⁻¹ * s1c2_Lam d r ℓ v x‖ₑ ^ p ≤ ENNReal.ofReal M⁻¹ ^ p *
      (c₁ * Ip volume p (iteratedFDeriv ℝ ℓ v) + c₂ * Ip volume p v) := by
    calc ∫⁻ x, ‖M⁻¹ * s1c2_Lam d r ℓ v x‖ₑ ^ p
        ≤ ∫⁻ x, (ENNReal.ofReal M⁻¹ * s1c2_W d r ℓ v x) ^ p :=
          lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt x) hp0.le)
      _ = ENNReal.ofReal M⁻¹ ^ p * ∫⁻ x, s1c2_W d r ℓ v x ^ p := by
          simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
          rw [lintegral_const_mul'' _ ((s1c2_W_meas r ℓ hvc).pow_const p).aemeasurable]
      _ ≤ _ := mul_le_mul_right (hW ℝ v hv) _
  have hI0 : Ip volume p v ^ (1 / p) = eLpNorm v (ENNReal.ofReal p) volume := by
    rw [s1c2_Ip_eq _ hp0 _ hv0.aestronglyMeasurable, ← ENNReal.rpow_mul,
      mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  have hI1 : Ip volume p (iteratedFDeriv ℝ ℓ v) ^ (1 / p) =
      eLpNorm (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume := by
    rw [s1c2_Ip_eq _ hp0 _ hv1.aestronglyMeasurable, ← ENNReal.rpow_mul,
      mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
  have hbound : eLpNorm (fun x => M⁻¹ * s1c2_Lam d r ℓ v x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (M⁻¹ * ((c₁ ^ (1 / p)).toReal + (c₂ ^ (1 / p)).toReal)) *
        (eLpNorm v (ENNReal.ofReal p) volume +
          eLpNorm (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne'
      ENNReal.ofReal_ne_top hΛm, ENNReal.toReal_ofReal hp0.le]
    have h1 := ENNReal.rpow_le_rpow hlp (by positivity : (0 : ℝ) ≤ 1 / p)
    refine h1.trans ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p), ← ENNReal.rpow_mul,
      mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
    have h2 := s1c2_rpow_add_inv_le hp.le (c₁ * Ip volume p (iteratedFDeriv ℝ ℓ v))
      (c₂ * Ip volume p v)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity : (0 : ℝ) ≤ 1 / p), hI0, hI1] at h2
    rw [ENNReal.ofReal_mul hMi, ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal ha1t, ENNReal.ofReal_toReal ha2t, mul_assoc]
    refine mul_le_mul_right (h2.trans ?_) _
    set A := eLpNorm v (ENNReal.ofReal p) volume
    set B := eLpNorm (iteratedFDeriv ℝ ℓ v) (ENNReal.ofReal p) volume
    calc c₁ ^ (1 / p) * B + c₂ ^ (1 / p) * A
        ≤ c₁ ^ (1 / p) * (A + B) + c₂ ^ (1 / p) * (A + B) :=
          add_le_add (mul_le_mul_right le_add_self _) (mul_le_mul_right le_self_add _)
      _ = _ := by ring
  refine ⟨fun x => M⁻¹ * s1c2_Lam d r ℓ v x, hΛm, ?_, ?_, hbound⟩
  · -- the distributional identity
    obtain ⟨vC, hvCdef⟩ : ∃ vC : EuclideanSpace ℝ (Fin d) → ℂ, vC = fun x => ((v x : ℝ) : ℂ) :=
      ⟨_, rfl⟩
    have e : ∀ x, ((v x : ℝ) : ℂ) = vC x := fun x => by rw [hvCdef]
    have hvCs : ContDiff ℝ ℓ vC := by
      rw [hvCdef]; exact Complex.ofRealCLM.contDiff.comp hv
    have hnormD : ∀ z, ‖iteratedFDeriv ℝ ℓ vC z‖ = ‖iteratedFDeriv ℝ ℓ v z‖ := by
      intro z
      have := LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI
        (hv.contDiffAt (x := z)) (i := ℓ) le_rfl
      have e2 : vC = ⇑Complex.ofRealLI ∘ v := by rw [hvCdef]; rfl
      rw [e2, this]
    have hvC0 : MemLp vC (ENNReal.ofReal p) volume := by
      unfold MemLp at hv0 ⊢
      rwa [eLpNorm_congr_norm_ae hvCs.continuous.aestronglyMeasurable hvc.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun x => by rw [hvCdef]; simp))]
    have hvC1 : MemLp (iteratedFDeriv ℝ ℓ vC) (ENNReal.ofReal p) volume := by
      unfold MemLp at hv1 ⊢
      rwa [eLpNorm_congr_norm_ae
        (hvCs.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
        (hv.continuous_iteratedFDeriv le_rfl).aestronglyMeasurable
        (Filter.Eventually.of_forall hnormD)]
    have hLam : ∀ x, s1c2_Lam d r ℓ vC x = ((s1c2_Lam d r ℓ v x : ℝ) : ℂ) := by
      intro x
      unfold s1c2_Lam
      rw [← integral_complex_ofReal]
      congr 1; funext y
      rw [hvCdef, u8_fd_ofReal, Complex.real_smul]
      simp only [smul_eq_mul, Complex.ofReal_mul]
    intro φ
    obtain ⟨hdu1, hdu2, hdu3⟩ := s1c2_duality hd hr hp ℓ hrℓ hm hvCs hvC0 hvC1 φ
    have hΨ : ∀ x, 𝓕⁻ (fun ξ : EuclideanSpace ℝ (Fin d) =>
        (((2 * Real.pi * ‖ξ‖) ^ r : ℝ) : ℂ) * 𝓕 (⇑φ) ξ) x =
        ((M⁻¹ : ℝ) : ℂ) * s1c2_Lam d r ℓ φ x := by
      intro x
      have := u8_Lam_eq hd ℓ hm r hr hαm M hM φ x
      unfold s1c2_Lam
      rw [this]
      have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM0.ne'
      push_cast
      field_simp
    simp only [e]
    simp_rw [hΨ]
    refine ⟨?_, ?_, ?_⟩
    · exact (hdu1.const_mul ((M⁻¹ : ℝ) : ℂ)).congr (Filter.Eventually.of_forall (fun x => by
        simp only; ring))
    · refine (hdu2.const_mul ((M⁻¹ : ℝ) : ℂ)).congr (Filter.Eventually.of_forall (fun x => ?_))
      simp only
      rw [hLam]; push_cast; ring
    · have h1 : ∀ x, vC x * (((M⁻¹ : ℝ) : ℂ) * s1c2_Lam d r ℓ φ x) =
          ((M⁻¹ : ℝ) : ℂ) * (vC x * s1c2_Lam d r ℓ φ x) := fun x => by ring
      have h2 : ∀ x, (((M⁻¹ * s1c2_Lam d r ℓ v x : ℝ)) : ℂ) * φ x =
          ((M⁻¹ : ℝ) : ℂ) * (s1c2_Lam d r ℓ vC x * φ x) := fun x => by
        rw [hLam]; push_cast; ring
      simp_rw [h1, h2]
      rw [integral_const_mul, integral_const_mul, hdu3]
  · show eLpNorm _ _ _ < ⊤
    exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨hv0, hv1⟩))

end HRS.S1C2
