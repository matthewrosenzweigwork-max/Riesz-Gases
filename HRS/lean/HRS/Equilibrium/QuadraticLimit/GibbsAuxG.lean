import HRS.Equilibrium.QuadraticLimit.Features
import HRS.Equilibrium.QuadraticLimit.GibbsAuxF

/-!
# Lemma 7.5, `q08_gibbs_approx`: the Gibbs weights, concretely (prefix `q08gl_`)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

variable {d : ℕ} (D : Q08Data d)

/-- The unnormalised Gibbs weight `exp(-β N F_N^g)`. -/
def q08gl_a (N : ℕ) (X : Config d N) : ℝ :=
  Real.exp (-D.β * N * modulatedEnergyKernel (periodicRiesz d D.s) X D.μ)

/-- The scaled energy `N F_N^g`. -/
def q08gl_x (N : ℕ) (X : Config d N) : ℝ :=
  (N : ℝ) * modulatedEnergyKernel (periodicRiesz d D.s) X D.μ

theorem q08gl_a_eq (N : ℕ) (X : Config d N) : q08gl_a D N X = Real.exp (-D.β * q08gl_x D N X) := by
  unfold q08gl_a q08gl_x; rw [mul_assoc]

theorem q08gl_a_pos (N : ℕ) (X : Config d N) : 0 < q08gl_a D N X := Real.exp_pos _

theorem q08gl_x_meas (N : ℕ) : Measurable (q08gl_x D N) :=
  measurable_const.mul (q08f_measurable_energyKernel D N)

theorem q08gl_a_meas (N : ℕ) : Measurable (q08gl_a D N) := by
  have : q08gl_a D N = fun X => Real.exp (-D.β * q08gl_x D N X) := funext (q08gl_a_eq D N)
  rw [this]; exact Real.measurable_exp.comp (measurable_const.mul (q08gl_x_meas D N))

/-- Powers of the weight are the weights at a multiple of `β`. -/
theorem q08gl_a_pow (N : ℕ) (q : ℕ) (X : Config d N) :
    q08gl_a D N X ^ q = Real.exp (-(q * D.β) * N * modulatedEnergyKernel (periodicRiesz d D.s) X D.μ) := by
  unfold q08gl_a
  rw [← Real.exp_nat_mul]
  congr 1; ring

/-- Pressure bounds for `b ∈ {β, 2β, 3β}`. -/
theorem q08gl_pressure : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ q : ℕ, 1 ≤ q → q ≤ 3 →
    ENNReal.ofReal (Real.exp (-C)) ≤ ProdTransfer.Jint d D.s N (q * D.β) D.μ ∧
      ProdTransfer.Jint d D.s N (q * D.β) D.μ ≤ ENNReal.ofReal (Real.exp C) := by
  obtain ⟨C, hC0, H⟩ := q08f_pressure D D.β (3 * D.β) D.hβ
  refine ⟨C, hC0, fun N hN q hq1 hq3 => H N hN (q * D.β) ⟨?_, ?_⟩⟩
  · have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    nlinarith [D.hβ]
  · have : (q : ℝ) ≤ 3 := by exact_mod_cast hq3
    nlinarith [D.hβ]

theorem q08gl_Jint_eq (N q : ℕ) :
    ProdTransfer.Jint d D.s N (q * D.β) D.μ = ∫⁻ X, ENNReal.ofReal (q08gl_a D N X ^ q) ∂(D.prodLaw N) := by
  unfold ProdTransfer.Jint
  simp_rw [q08gl_a_pow]
  rfl

instance q08gl_prodLaw_prob (N : ℕ) : IsProbabilityMeasure (D.prodLaw N) := by
  haveI := q08_isProb_μ D
  unfold Q08Data.prodLaw; infer_instance

/-- Integrability and two-sided bounds of the moments of the weight. -/
theorem q08gl_pow_facts (C : ℝ) (hC : ∀ N : ℕ, 1 ≤ N → ∀ q : ℕ, 1 ≤ q → q ≤ 3 →
    ENNReal.ofReal (Real.exp (-C)) ≤ ProdTransfer.Jint d D.s N (q * D.β) D.μ ∧
      ProdTransfer.Jint d D.s N (q * D.β) D.μ ≤ ENNReal.ofReal (Real.exp C))
    (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (hq1 : 1 ≤ q) (hq3 : q ≤ 3) :
    Integrable (fun X => q08gl_a D N X ^ q) (D.prodLaw N) ∧
      Real.exp (-C) ≤ ∫ X, q08gl_a D N X ^ q ∂(D.prodLaw N) ∧
      ∫ X, q08gl_a D N X ^ q ∂(D.prodLaw N) ≤ Real.exp C := by
  obtain ⟨hl, hu⟩ := hC N hN q hq1 hq3
  rw [q08gl_Jint_eq] at hl hu
  have hmeas : Measurable (fun X => q08gl_a D N X ^ q) := (q08gl_a_meas D N).pow_const q
  have hfin : ∫⁻ X, ENNReal.ofReal (q08gl_a D N X ^ q) ∂(D.prodLaw N) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  have hint : Integrable (fun X => q08gl_a D N X ^ q) (D.prodLaw N) :=
    (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
      (Eventually.of_forall fun X => (pow_pos (q08gl_a_pos D N X) q).le)).1 hfin
  have heq : ∫ X, q08gl_a D N X ^ q ∂(D.prodLaw N) =
      (∫⁻ X, ENNReal.ofReal (q08gl_a D N X ^ q) ∂(D.prodLaw N)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X => (pow_pos (q08gl_a_pos D N X) q).le)
      hmeas.aestronglyMeasurable
  refine ⟨hint, ?_, ?_⟩
  · rw [heq]
    have := ENNReal.toReal_mono hfin hl
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this
  · rw [heq]
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
    rwa [ENNReal.toReal_ofReal (Real.exp_pos _).le] at this

/-- The Gibbs integral as a weighted product-law integral. -/
theorem q08gl_gibbs_int {N : ℕ} (hZ : 0 < ∫ X, q08gl_a D N X ∂(D.prodLaw N)) (G : Config d N → ℝ) :
    ∫ X, G X ∂(D.Gibbs N) = (1 / ∫ X, q08gl_a D N X ∂(D.prodLaw N)) *
      ∫ X, G X * q08gl_a D N X ∂(D.prodLaw N) := by
  have hG : D.Gibbs N = (ENNReal.ofReal (∫ X, q08gl_a D N X ∂(D.prodLaw N)))⁻¹ •
      (D.prodLaw N).withDensity (fun X => ENNReal.ofReal (q08gl_a D N X)) := rfl
  rw [hG, integral_smul_measure, integral_withDensity_eq_integral_toReal_smul]
  · rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le, smul_eq_mul, one_div]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (q08gl_a_pos D N X).le, mul_comm]
  · exact ENNReal.measurable_ofReal.comp (q08gl_a_meas D N)
  · exact Eventually.of_forall fun X => ENNReal.ofReal_lt_top

/-- Exchangeability of the Gibbs law: all one-body marginals coincide. -/
theorem q08gl_exch_integral {N : ℕ} (hN : 1 ≤ N) (φ : Torus d → ℝ) (hφ : Measurable φ) (i : Fin N) :
    ∫ X, φ (X i) ∂(D.Gibbs N) = pair (firstMarginal (D.Gibbs N)) φ := by
  have h0 : 0 < N := hN
  have hex : IsExchangeable (D.Gibbs N) :=
    modulatedGibbs_isExchangeable (periodicRiesz d D.s) D.β D.μ (fun x => periodicRiesz_neg x)
  have hpair : pair (firstMarginal (D.Gibbs N)) φ = ∫ X, φ (X ⟨0, h0⟩) ∂(D.Gibbs N) := by
    unfold pair firstMarginal
    rw [dif_pos h0, integral_map (measurable_pi_apply (⟨0, h0⟩ : Fin N)).aemeasurable hφ.aestronglyMeasurable]
  rw [hpair]
  have hσ := hex (Equiv.swap (⟨0, h0⟩ : Fin N) i)
  have hm : Measurable (fun X : Config d N => X ∘ (Equiv.swap (⟨0, h0⟩ : Fin N) i)) :=
    (permMeasEquiv _).measurable
  have := integral_map (μ := D.Gibbs N) hm.aemeasurable
    (f := fun X : Config d N => φ (X ⟨0, h0⟩))
    (hφ.comp (measurable_pi_apply (⟨0, h0⟩ : Fin N))).aestronglyMeasurable
  rw [hσ] at this
  rw [this]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp [Function.comp_def]

/-- The centred pair energy `N F_N^h + ½ ∬ h`. -/
def q08gl_Th (N : ℕ) (X : Config d N) : ℝ := q08e_Z D.μ D.h X

/-- The normalised linear statistic `N^{-1/2} ∑_i (φ_b(X_i) - μ φ_b)`. -/
def q08gl_Lin (N : ℕ) (b : Fin D.p) (X : Config d N) : ℝ :=
  (Real.sqrt N)⁻¹ * ∑ i, (D.φ b (X i) - pair D.μ (D.φ b))

/-- The vector of true statistics. -/
def q08gl_V (N : ℕ) (o : Option (Fin D.p)) (X : Config d N) : ℝ :=
  Option.elim o (q08gl_Th D N X) (fun b => q08gl_Lin D N b X)

theorem q08gl_stat_eq {N : ℕ} (hN : 1 ≤ N) (X : Config d N) :
    ((N : ℝ) * (modulatedEnergy D.h X D.μ - ∫ Y, modulatedEnergy D.h Y D.μ ∂(D.Gibbs N)),
      fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, D.φ a (X i) -
        pair (firstMarginal (D.Gibbs N)) (D.φ a))) =
    (q08gl_V D N none X - ∫ Y, q08gl_V D N none Y ∂(D.Gibbs N),
      fun b => q08gl_V D N (some b) X - ∫ Y, q08gl_V D N (some b) Y ∂(D.Gibbs N)) := by
  haveI := q08gl_prodLaw_prob D N
  haveI := q08f_gibbs_isProb D N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine Prod.ext ?_ ?_
  · show (N : ℝ) * (modulatedEnergy D.h X D.μ - ∫ Y, modulatedEnergy D.h Y D.μ ∂(D.Gibbs N)) =
      q08gl_Th D N X - ∫ Y, q08gl_Th D N Y ∂(D.Gibbs N)
    have hZ : ∀ Y : Config d N, q08gl_Th D N Y =
        (N : ℝ) * modulatedEnergy D.h Y D.μ + (1 / 2) * ∫ x, ∫ y, D.h x y ∂D.μ ∂D.μ := fun Y => rfl
    simp_rw [hZ]
    rw [integral_add ((q08_integrable_energy D N hN).const_mul _) (integrable_const _), integral_const_mul]
    simp
    ring
  · funext b
    show Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, D.φ b (X i) - pair (firstMarginal (D.Gibbs N)) (D.φ b)) =
      q08gl_Lin D N b X - ∫ Y, q08gl_Lin D N b Y ∂(D.Gibbs N)
    obtain ⟨hφm, M, hM⟩ := D.hφ b
    have hint : ∀ i : Fin N, Integrable (fun Y : Config d N => D.φ b (Y i)) (D.Gibbs N) := fun i =>
      Integrable.of_bound (hφm.comp (measurable_pi_apply i)).aestronglyMeasurable M
        (Eventually.of_forall fun Y => by simpa [Real.norm_eq_abs] using hM _)
    have h1 : ∫ Y, q08gl_Lin D N b Y ∂(D.Gibbs N) =
        (Real.sqrt N)⁻¹ * ∑ i : Fin N, (pair (firstMarginal (D.Gibbs N)) (D.φ b) - pair D.μ (D.φ b)) := by
      unfold q08gl_Lin
      rw [integral_const_mul]
      congr 1
      have hint2 : ∀ i : Fin N, Integrable (fun Y : Config d N => D.φ b (Y i) - pair D.μ (D.φ b))
          (D.Gibbs N) := fun i => (hint i).sub (integrable_const _)
      rw [integral_finsetSum _ fun i _ => hint2 i]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_sub (hint i) (integrable_const _), q08gl_exch_integral D hN (D.φ b) hφm i]
      simp
    rw [h1]
    unfold q08gl_Lin
    have e1 : (Real.sqrt N)⁻¹ * (N : ℝ) = Real.sqrt N := by
      have : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
      have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
      field_simp
      linarith
    have e2 : Real.sqrt N * (1 / (N : ℝ)) = (Real.sqrt N)⁻¹ := by
      have : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
      have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
      field_simp
      linarith
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [mul_sub, mul_sub, mul_sub, ← mul_assoc, e2]
    have : (Real.sqrt N)⁻¹ * ((N : ℝ) * pair (firstMarginal (D.Gibbs N)) (D.φ b)) =
        Real.sqrt N * pair (firstMarginal (D.Gibbs N)) (D.φ b) := by rw [← mul_assoc, e1]
    rw [this]
    have : (Real.sqrt N)⁻¹ * ((N : ℝ) * pair D.μ (D.φ b)) = Real.sqrt N * pair D.μ (D.φ b) := by
      rw [← mul_assoc, e1]
    rw [this]
    ring

/-- The Gibbs expectation of a test function of the statistic is the tilted functional of the true
statistics under the product law. -/
theorem q08gl_gibbs_Phi {N : ℕ} (hN : 1 ≤ N) (hZ : 0 < ∫ X, q08gl_a D N X ∂(D.prodLaw N))
    (F : ℝ × (Fin D.p → ℝ) → ℝ) :
    ∫ X, F ((N : ℝ) * (modulatedEnergy D.h X D.μ - ∫ Y, modulatedEnergy D.h Y D.μ ∂(D.Gibbs N)),
        fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, D.φ a (X i) -
          pair (firstMarginal (D.Gibbs N)) (D.φ a))) ∂(D.Gibbs N) =
      q08gl_Phi (D.prodLaw N) (q08gl_Ft F) (q08gl_a D N) (q08gl_V D N)
        (∫ X, q08gl_a D N X ∂(D.prodLaw N)) := by
  have hc : ∀ o, ∫ Y, q08gl_V D N o Y ∂(D.Gibbs N) =
      (1 / ∫ X, q08gl_a D N X ∂(D.prodLaw N)) * ∫ Y, q08gl_V D N o Y * q08gl_a D N Y ∂(D.prodLaw N) :=
    fun o => q08gl_gibbs_int D hZ _
  have h1 : ∀ X : Config d N, F ((N : ℝ) * (modulatedEnergy D.h X D.μ - ∫ Y, modulatedEnergy D.h Y D.μ ∂(D.Gibbs N)),
        fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, D.φ a (X i) -
          pair (firstMarginal (D.Gibbs N)) (D.φ a))) =
      q08gl_Ft F (fun o => q08gl_V D N o X - ∫ Y, q08gl_V D N o Y ∂(D.Gibbs N)) := by
    intro X
    rw [q08gl_stat_eq D hN X]
    rfl
  simp_rw [h1, hc]
  rw [q08gl_gibbs_int D hZ]
  rfl

section Bounds

/-- `q08e_Z` is `L²` under the product law. -/
theorem q08gl_Z_memLp {T : Type*} [MeasurableSpace T] (μ : Measure T) [IsProbabilityMeasure μ]
    (k : T → T → ℝ) (hm : Measurable (Function.uncurry k))
    (hk : Integrable (fun z : T × T => k z.1 z.2 ^ 2) (μ.prod μ)) (hs : ∀ x y, k x y = k y x)
    (N : ℕ) (hN : 1 ≤ N) : MemLp (q08e_Z μ k : (Fin N → T) → ℝ) 2 (Measure.pi fun _ : Fin N => μ) := by
  obtain ⟨hDmem, -⟩ := q08e_DD_second μ (q08e_kt μ k) (q08e_kt_meas μ k hm hk) (q08e_kt_symm μ k hs)
    (q08e_kt_degenerate μ k hm hk) (q08e_kt_memLp μ k hm hk) N
  obtain ⟨hl2, hl0, -⟩ := q08e_ell_facts μ k hm hk
  have hlm : Measurable (fun x => q08e_a μ k x - q08e_m μ k) :=
    (q08e_a_meas' μ k hm hk).sub measurable_const
  obtain ⟨hLmem, -⟩ := q08e_lin_second μ (fun x => q08e_a μ k x - q08e_m μ k) hlm hl2 hl0 N
  have : (q08e_Z μ k : (Fin N → T) → ℝ) = fun X => (1 / (2 * (N : ℝ))) * q08e_DD (q08e_kt μ k) X -
      (1 / (N : ℝ)) * ∑ i, (q08e_a μ k (X i) - q08e_m μ k) := funext fun X => q08e_Z_eq μ k hN X
  rw [this]
  exact (hDmem.const_mul _).sub (hLmem.const_mul _)

theorem q08gl_h_sq_int : Integrable (fun z : Torus d × Torus d => D.h z.1 z.2 ^ 2) (D.μ.prod D.μ) :=
  (q08s_h_memLp D).integrable_sq

theorem q08gl_g_sq_int : Integrable (fun z : Torus d × Torus d =>
    (fun x y => periodicRiesz d D.s (x - y)) z.1 z.2 ^ 2) (D.μ.prod D.μ) := q08s_g_sq_int D

theorem q08gl_kg_meas : Measurable (Function.uncurry (fun x y : Torus d => periodicRiesz d D.s (x - y))) :=
  (q08s_g_meas D).comp (measurable_fst.sub measurable_snd)

theorem q08gl_kg_symm (x y : Torus d) :
    periodicRiesz d D.s (x - y) = periodicRiesz d D.s (y - x) := by
  rw [← periodicRiesz_neg (y - x), neg_sub]

theorem q08gl_Th_eq (N : ℕ) (X : Config d N) : q08gl_Th D N X =
    (N : ℝ) * modulatedEnergy D.h X D.μ + (1 / 2) * ∫ x, ∫ y, D.h x y ∂D.μ ∂D.μ := rfl

theorem q08gl_Th_meas (N : ℕ) : Measurable (q08gl_Th D N) := by
  have : q08gl_Th D N = fun X => (N : ℝ) * modulatedEnergy D.h X D.μ + (1 / 2) * ∫ x, ∫ y, D.h x y ∂D.μ ∂D.μ :=
    funext (q08gl_Th_eq D N)
  rw [this]
  exact (measurable_const.mul (q08_measurable_energy D N)).add measurable_const

theorem q08gl_Lin_meas (N : ℕ) (b : Fin D.p) : Measurable (q08gl_Lin D N b) := by
  unfold q08gl_Lin
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)
  exact ((D.hφ b).1.comp (measurable_pi_apply i)).sub measurable_const

theorem q08gl_V_meas (N : ℕ) (o : Option (Fin D.p)) : Measurable (q08gl_V D N o) := by
  cases o
  · exact q08gl_Th_meas D N
  · exact q08gl_Lin_meas D N _

/-- A bound of the test functions. -/
def q08gl_Mphi (b : Fin D.p) : ℝ := (D.hφ b).2.choose

theorem q08gl_Mphi_spec (b : Fin D.p) (x : Torus d) : |D.φ b x| ≤ q08gl_Mphi D b :=
  (D.hφ b).2.choose_spec x

theorem q08gl_Mphi_nonneg (b : Fin D.p) : 0 ≤ q08gl_Mphi D b :=
  (abs_nonneg _).trans (q08gl_Mphi_spec D b 0)

/-- The uniform `L²` bound of the true statistics. -/
def q08gl_BV : ℝ :=
  Real.sqrt (3 * ∫ z : Torus d × Torus d, D.h z.1 z.2 ^ 2 ∂(D.μ.prod D.μ)) + ∑ b, 2 * q08gl_Mphi D b

theorem q08gl_BV_nonneg : 0 ≤ q08gl_BV D :=
  add_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun b _ => by have := q08gl_Mphi_nonneg D b; positivity)

theorem q08gl_pair_bdd (b : Fin D.p) : |pair D.μ (D.φ b)| ≤ q08gl_Mphi D b := by
  haveI := q08_isProb_μ D
  unfold pair
  have := norm_integral_le_of_norm_le_const (μ := D.μ) (f := D.φ b) (C := q08gl_Mphi D b)
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using q08gl_Mphi_spec D b x)
  simpa using this

theorem q08gl_V_memLp (N : ℕ) (hN : 1 ≤ N) (o : Option (Fin D.p)) :
    MemLp (q08gl_V D N o) 2 (D.prodLaw N) := by
  haveI := q08_isProb_μ D
  cases o
  · exact q08gl_Z_memLp D.μ D.h D.hmeas (q08gl_h_sq_int D) D.hsymm N hN
  · rename_i b
    obtain ⟨hφm, -⟩ := D.hφ b
    refine (q08gl_lin_L2 (μ := D.μ) (fun x => D.φ b x - pair D.μ (D.φ b)) (hφm.sub_const _)
      (2 * q08gl_Mphi D b) (fun x => ?_) ?_ N hN).1
    · have := q08gl_Mphi_spec D b x
      have := q08gl_pair_bdd D b
      calc |D.φ b x - pair D.μ (D.φ b)| ≤ |D.φ b x| + |pair D.μ (D.φ b)| := abs_sub _ _
        _ ≤ 2 * q08gl_Mphi D b := by linarith
    · have hint : Integrable (D.φ b) D.μ := by
        obtain ⟨M, hM⟩ := (D.hφ b).2
        exact Integrable.of_bound hφm.aestronglyMeasurable M
          (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
      rw [integral_sub hint (integrable_const _)]
      simp [pair]

theorem q08gl_V_L2 (N : ℕ) (hN : 1 ≤ N) (o : Option (Fin D.p)) :
    Real.sqrt (∫ X, q08gl_V D N o X ^ 2 ∂(D.prodLaw N)) ≤ q08gl_BV D := by
  haveI := q08_isProb_μ D
  cases o
  · have h := q08e_main D.μ D.h D.hmeas (q08gl_h_sq_int D) D.hsymm hN
    have h2 : ∫ X, q08gl_V D N none X ^ 2 ∂(D.prodLaw N) ≤ 3 * ∫ z : Torus d × Torus d, D.h z.1 z.2 ^ 2 ∂(D.μ.prod D.μ) := h
    unfold q08gl_BV
    refine (Real.sqrt_le_sqrt h2).trans ?_
    have : 0 ≤ ∑ b, 2 * q08gl_Mphi D b := Finset.sum_nonneg fun b _ => by have := q08gl_Mphi_nonneg D b; positivity
    linarith
  · rename_i b
    obtain ⟨hφm, -⟩ := D.hφ b
    have hr0 : ∫ x, (D.φ b x - pair D.μ (D.φ b)) ∂D.μ = 0 := by
      have hint : Integrable (D.φ b) D.μ := by
        obtain ⟨M, hM⟩ := (D.hφ b).2
        exact Integrable.of_bound hφm.aestronglyMeasurable M
          (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
      rw [integral_sub hint (integrable_const _)]
      simp [pair]
    have hC : ∀ x, |D.φ b x - pair D.μ (D.φ b)| ≤ 2 * q08gl_Mphi D b := fun x => by
      have := q08gl_Mphi_spec D b x
      have := q08gl_pair_bdd D b
      calc |D.φ b x - pair D.μ (D.φ b)| ≤ |D.φ b x| + |pair D.μ (D.φ b)| := abs_sub _ _
        _ ≤ 2 * q08gl_Mphi D b := by linarith
    obtain ⟨-, hint⟩ := q08gl_lin_L2 (μ := D.μ) (fun x => D.φ b x - pair D.μ (D.φ b)) (hφm.sub_const _)
      (2 * q08gl_Mphi D b) hC hr0 N hN
    have h2 : ∫ X, q08gl_V D N (some b) X ^ 2 ∂(D.prodLaw N) ≤ (2 * q08gl_Mphi D b) ^ 2 := by
      have e : ∫ X, q08gl_V D N (some b) X ^ 2 ∂(D.prodLaw N) =
          ∫ x, (D.φ b x - pair D.μ (D.φ b)) ^ 2 ∂D.μ := hint
      rw [e]
      have h1 : ∫ x, (D.φ b x - pair D.μ (D.φ b)) ^ 2 ∂D.μ ≤ ∫ _x, (2 * q08gl_Mphi D b) ^ 2 ∂D.μ :=
        integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) (integrable_const _)
          (Eventually.of_forall fun x => by
            have := hC x
            nlinarith [abs_nonneg (D.φ b x - pair D.μ (D.φ b)), sq_abs (D.φ b x - pair D.μ (D.φ b))])
      simpa using h1
    unfold q08gl_BV
    have hMb := q08gl_Mphi_nonneg D b
    refine (Real.sqrt_le_sqrt h2).trans ?_
    rw [Real.sqrt_sq (by positivity)]
    have : 2 * q08gl_Mphi D b ≤ ∑ b', 2 * q08gl_Mphi D b' :=
      Finset.single_le_sum (f := fun b' => 2 * q08gl_Mphi D b') (fun b' _ => by have := q08gl_Mphi_nonneg D b'; positivity)
        (Finset.mem_univ b)
    linarith [Real.sqrt_nonneg (3 * ∫ z : Torus d × Torus d, D.h z.1 z.2 ^ 2 ∂(D.μ.prod D.μ))]

end Bounds

end HRS.Q08

end
