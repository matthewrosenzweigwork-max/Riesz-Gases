import HRS.MC.D3T3Aux1

/-!
# Packet D3T3, auxiliary facts: joint measurability of `(x,t) ↦ Pφ_t(x)` and Fubini for Fourier
coefficients of `t`-integrals.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

/-- A jointly measurable version of `(x, t) ↦ Pφ_t(x)` (equal to it for `t > 0`). -/
def perJ (ψ : Euc d → ℝ) (p : Torus d × ℝ) : ℝ :=
  (∑' n : Lattice d, ENNReal.ofReal (fdlPhiScale ψ p.2 (Torus.rep p.1 + Lattice.toEuc n))).toReal

lemma d3f_perJ_measurable {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) : Measurable (perJ ψ) := by
  have hφm : Measurable (fdlPhi ψ) := (fdle_phi_cont hψ).measurable
  have hrep := d3t_measurable_rep d
  have hmG : Measurable (fun p : Torus d × ℝ =>
      ∑' n : Lattice d, ENNReal.ofReal (fdlPhiScale ψ p.2 (Torus.rep p.1 + Lattice.toEuc n))) := by
    refine Measurable.ennreal_tsum fun n => ?_
    refine Measurable.ennreal_ofReal ?_
    unfold fdlPhiScale
    exact ((measurable_snd.pow_const d).inv).mul
      (hφm.comp (measurable_snd.inv.smul ((hrep.comp measurable_fst).add_const _)))
  exact hmG.ennreal_toReal

lemma d3f_perJ_eq {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    perJ ψ (x, t) = fdlPer (fdlPhiScale ψ t) x := by
  unfold perJ
  simp only
  rw [← d3t_ofReal_per hψ ht x, ENNReal.toReal_ofReal (d3t_per_nonneg hψ ht x)]

lemma d3f_perJ_nonneg (ψ : Euc d → ℝ) (p : Torus d × ℝ) : 0 ≤ perJ ψ p := ENNReal.toReal_nonneg

/-- Fubini for the Fourier coefficient of a `t`-integral. -/
lemma d3f_fubini {ψ : Euc d → ℝ} (k : Lattice d) {S : Set ℝ} (κ : ℝ → ℝ) (c : ℝ)
    (hint : Integrable (fun p : Torus d × ℝ =>
      Torus.mode (-k) p.1 * ((κ p.2 * (perJ ψ p - c) : ℝ) : ℂ))
      ((volume : Measure (Torus d)).prod (volume.restrict S))) :
    Torus.fcoef (fun x => ∫ t in S, κ t * (perJ ψ (x, t) - c)) k
      = ∫ t in S, ((κ t : ℝ) : ℂ) * Torus.fcoef (fun x => perJ ψ (x, t) - c) k := by
  unfold Torus.fcoef
  have h1 : ∀ x : Torus d, Torus.mode (-k) x * ((∫ t in S, κ t * (perJ ψ (x, t) - c) : ℝ) : ℂ)
      = ∫ t in S, Torus.mode (-k) x * ((κ t * (perJ ψ (x, t) - c) : ℝ) : ℂ) := by
    intro x
    rw [integral_const_mul]
    congr 1
    exact integral_ofReal.symm
  simp_rw [h1]
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  push_cast
  ring


/-- The weight `κ(t) = b t^{d-s}/t`. -/
def kap (d : ℕ) (s b : ℝ) (t : ℝ) : ℝ := b * (t ^ ((d : ℝ) - s) / t)

lemma d3f_kap_nonneg {s b : ℝ} (hb : 0 ≤ b) {t : ℝ} (ht : 0 < t) : 0 ≤ kap d s b t :=
  mul_nonneg hb (div_nonneg (Real.rpow_nonneg ht.le _) ht.le)

lemma d3f_kap_measurable (s b : ℝ) : Measurable (kap d s b) := by
  unfold kap
  exact ((measurable_id.pow_const _).div measurable_id).const_mul b

lemma d3f_kap_integrableOn {s : ℝ} (hsd : s < d) (b : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (kap d s b) (Ioc 0 lam) := by
  have hiv : IntervalIntegrable (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) volume 0 lam :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hlam.le] at hiv
  refine IntegrableOn.congr_fun (Integrable.const_mul hiv b) ?_ measurableSet_Ioc
  intro t ht
  simp only [kap]
  rw [Real.rpow_sub_one ht.1.ne']

lemma d3f_meas_f {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (k : Lattice d) (κ : ℝ → ℝ)
    (hκ : Measurable κ) (c : ℝ) :
    Measurable (fun p : Torus d × ℝ => Torus.mode (-k) p.1 * ((κ p.2 * (perJ ψ p - c) : ℝ) : ℂ)) :=
  (((Torus.continuous_mode _).measurable.comp measurable_fst).mul
    (Complex.measurable_ofReal.comp ((hκ.comp measurable_snd).mul
      ((d3f_perJ_measurable hψ).sub_const c))))

lemma d3f_norm_mode_mul (k : Lattice d) (x : Torus d) (r : ℝ) :
    ‖Torus.mode (-k) x * (r : ℂ)‖ = |r| := by
  rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]

lemma d3f_int_a {s : ℝ} (hsd : s < d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (k : Lattice d)
    {b lam : ℝ} (hb0 : 0 < b) (hlam : 0 < lam) :
    Integrable (fun p : Torus d × ℝ =>
      Torus.mode (-k) p.1 * ((kap d s b p.2 * (perJ ψ p - 0) : ℝ) : ℂ))
      ((volume : Measure (Torus d)).prod (volume.restrict (Ioc 0 lam))) := by
  have hm := d3f_meas_f hψ k (kap d s b) (d3f_kap_measurable s b) 0
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨?_, ?_⟩
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Eventually.of_forall fun t ht => ?_
    have hcont : Continuous (fun x : Torus d => Torus.mode (-k) x *
        ((kap d s b t * (perJ ψ (x, t) - 0) : ℝ) : ℂ)) := by
      have h' : ∀ x : Torus d, perJ ψ (x, t) = fdlPer (fdlPhiScale ψ t) x :=
        fun x => d3f_perJ_eq hψ ht.1 x
      simp only [h']
      exact (Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp
        (continuous_const.mul ((per_fdlPer_continuous hψ ht.1).sub continuous_const)))
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hae : (fun t => ∫ x, ‖Torus.mode (-k) x * ((kap d s b t * (perJ ψ (x, t) - 0) : ℝ) : ℂ)‖)
        =ᵐ[volume.restrict (Ioc 0 lam)] fun t => kap d s b t * ∫ y, fdlPhi ψ y := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
      refine Eventually.of_forall fun t ht => ?_
      have hk := d3f_kap_nonneg (d := d) (s := s) hb0.le ht.1
      have : ∀ x : Torus d, ‖Torus.mode (-k) x * ((kap d s b t * (perJ ψ (x, t) - 0) : ℝ) : ℂ)‖
          = kap d s b t * fdlPer (fdlPhiScale ψ t) x := by
        intro x
        rw [d3f_norm_mode_mul, d3f_perJ_eq hψ ht.1 x, sub_zero,
          abs_of_nonneg (mul_nonneg hk (d3t_per_nonneg hψ ht.1 x))]
      simp_rw [this]
      rw [integral_const_mul, d3t_per_integral hψ ht.1]
    exact ((d3f_kap_integrableOn hsd b hlam).mul_const _).congr hae.symm

end HRS.MC.D3T3
