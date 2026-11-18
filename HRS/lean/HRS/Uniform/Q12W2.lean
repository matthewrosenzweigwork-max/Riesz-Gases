import HRS.Uniform.Q12W1
import HRS.PDE.MeanFieldAprioriHeat
import HRS.PDE.Toolbox.Kernel

/-!
# Q12, part W2: the heat-kernel measure, smeared measures and the smearing coupling
-/

noncomputable section

open HRS MeasureTheory Filter Topology
open HRS.CoercAux
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- `heatK d s = heatKer (s / 4π²)`. -/
lemma q12_heatK_eq (s : ℝ) (y : Torus d) :
    heatK d s y = PDE.MFApriori.heatKer (s / (4 * Real.pi ^ 2)) y := by
  unfold heatK PDE.MFApriori.heatKer PDE.MFApriori.heatMult
  refine tsum_congr fun k => ?_
  congr 2
  have : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-- The Fourier coefficient of the heat kernel: `∫ e_{-k} K_s = e^{-s|k|²}`. -/
lemma q12_integral_mode_heatK {s : ℝ} (hs : 0 < s) (k : Lattice d) :
    ∫ x, Torus.mode (-k) x * (heatK d s x : ℂ) = (Real.exp (-s * Lattice.enorm k ^ 2) : ℂ) := by
  have ht : 0 < s / (4 * Real.pi ^ 2) := by positivity
  have := PDE.MFApriori.integral_mode_heatKer (d := d) ht k
  simp_rw [q12_heatK_eq s]
  rw [this]
  unfold PDE.MFApriori.heatMult
  congr 2
  have : (4 * Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-- The heat-kernel probability measure on the torus. -/
def kerMeasure (d : ℕ) (t : ℝ) : Measure (Torus d) :=
  volume.withDensity fun ξ => ENNReal.ofReal (heatK d t ξ)

lemma q12_integrable_heatK {t : ℝ} (ht : 0 < t) : Integrable (heatK d t) :=
  (continuous_heatK ht).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma q12_kerMeasure_apply {t : ℝ} (ht : 0 < t) {A : Set (Torus d)} (hA : MeasurableSet A) :
    kerMeasure d t A = ENNReal.ofReal (∫ x in A, heatK d t x) := by
  unfold kerMeasure
  rw [withDensity_apply _ hA,
    ofReal_integral_eq_lintegral_ofReal (q12_integrable_heatK ht).integrableOn
      (Filter.Eventually.of_forall fun x => heatK_nonneg ht x)]

theorem q12_kerMeasure_prob {t : ℝ} (ht : 0 < t) : IsProbabilityMeasure (kerMeasure d t) := by
  refine ⟨?_⟩
  rw [q12_kerMeasure_apply ht MeasurableSet.univ, Measure.restrict_univ, integral_heatK ht]
  simp


lemma q12_enorm_neg (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  unfold Lattice.enorm Lattice.toEuc
  rw [← norm_neg]
  congr 1
  ext i
  simp

lemma q12_enorm_eI (i : Fin d) : Lattice.enorm (PDE.Kern.eI i : Lattice d) = 1 := by
  unfold Lattice.enorm
  have : Lattice.toEuc (PDE.Kern.eI i : Lattice d) = EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Lattice.toEuc, PDE.Kern.eI, Pi.single_apply, EuclideanSpace.single_apply]
  rw [this, EuclideanSpace.norm_single]
  simp

lemma q12_qf_eq (i : Fin d) (ξ : Torus d) :
    PDE.Kern.qf i ξ = 2 - 2 * (Torus.mode (PDE.Kern.eI i) ξ).re := by
  unfold PDE.Kern.qf
  have h1 := norm_mode (PDE.Kern.eI i : Lattice d) ξ
  rw [Complex.sq_norm, Complex.normSq_apply]
  have h2 : (Torus.mode (PDE.Kern.eI i) ξ).re * (Torus.mode (PDE.Kern.eI i) ξ).re +
      (Torus.mode (PDE.Kern.eI i) ξ).im * (Torus.mode (PDE.Kern.eI i) ξ).im = 1 := by
    have := h1
    rw [Complex.norm_def, Real.sqrt_eq_one, Complex.normSq_apply] at this
    exact this
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith

lemma q12_integral_K_qf {t : ℝ} (ht : 0 < t) (i : Fin d) :
    ∫ ξ, heatK d t ξ * PDE.Kern.qf i ξ = 2 - 2 * Real.exp (-t) := by
  have hK := q12_integrable_heatK (d := d) ht
  have hmode : Integrable (fun ξ : Torus d => heatK d t ξ * (Torus.mode (PDE.Kern.eI i) ξ).re) := by
    refine ((continuous_heatK ht).mul (Complex.continuous_re.comp (Torus.continuous_mode _))
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcoef := q12_integral_mode_heatK ht (-(PDE.Kern.eI i) : Lattice d)
  simp only [neg_neg] at hcoef
  have hre : ∫ ξ, heatK d t ξ * (Torus.mode (PDE.Kern.eI i) ξ).re = Real.exp (-t) := by
    have hc : Integrable (fun ξ : Torus d => Torus.mode (PDE.Kern.eI i) ξ * (heatK d t ξ : ℂ)) :=
      ((Torus.continuous_mode _).mul (Complex.continuous_ofReal.comp (continuous_heatK ht))
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have h1 := integral_re hc
    rw [hcoef] at h1
    simp only [RCLike.re_to_complex, Complex.ofReal_re] at h1
    have e : ∀ ξ : Torus d, (Torus.mode (PDE.Kern.eI i) ξ * (heatK d t ξ : ℂ)).re =
        heatK d t ξ * (Torus.mode (PDE.Kern.eI i) ξ).re := fun ξ => by
      rw [mul_comm, Complex.re_ofReal_mul]
    simp_rw [e] at h1
    rw [h1, q12_enorm_neg, q12_enorm_eI]
    simp
  have e : ∀ ξ : Torus d, heatK d t ξ * PDE.Kern.qf i ξ =
      2 * heatK d t ξ - 2 * (heatK d t ξ * (Torus.mode (PDE.Kern.eI i) ξ).re) := fun ξ => by
    rw [q12_qf_eq]; ring
  simp_rw [e]
  rw [integral_sub (hK.const_mul 2) (hmode.const_mul 2), integral_const_mul, integral_const_mul,
    integral_heatK ht, hre]
  ring


lemma q12_continuous_tdist0 : Continuous fun ξ : Torus d => Torus.tdist ξ 0 := by
  have h := Continuous.comp (g := fun p : Torus d × Torus d => Torus.tdist p.1 p.2)
    Uniform.Q14.q14_continuous_tdist (f := fun ξ : Torus d => (ξ, (0 : Torus d)))
    (continuous_id.prodMk continuous_const)
  exact h

lemma q12_second_moment {t : ℝ} (ht : 0 < t) :
    ∫ ξ, heatK d t ξ * Torus.tdist ξ 0 ^ 2 ≤ d * t / 8 := by
  have hK := continuous_heatK (d := d) ht
  have hqf : ∀ i : Fin d, Continuous fun ξ : Torus d => PDE.Kern.qf i ξ := fun i => by
    unfold PDE.Kern.qf
    exact (continuous_norm.comp ((Torus.continuous_mode _).sub continuous_const)).pow 2
  have hint1 : Integrable (fun ξ : Torus d => heatK d t ξ * Torus.tdist ξ 0 ^ 2) :=
    (hK.mul (q12_continuous_tdist0.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint2 : ∀ i : Fin d, Integrable (fun ξ : Torus d => heatK d t ξ * PDE.Kern.qf i ξ) :=
    fun i => (hK.mul (hqf i)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hint3 : Integrable (fun ξ : Torus d => ∑ i : Fin d, heatK d t ξ * PDE.Kern.qf i ξ) :=
    integrable_finset_sum _ fun i _ => hint2 i
  have hpt : ∀ ξ : Torus d, heatK d t ξ * Torus.tdist ξ 0 ^ 2 ≤
      (∑ i : Fin d, heatK d t ξ * PDE.Kern.qf i ξ) / 16 := fun ξ => by
    rw [← Finset.mul_sum, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (PDE.Kern.tdist_sq_le ξ) (heatK_nonneg ht ξ)
  calc ∫ ξ, heatK d t ξ * Torus.tdist ξ 0 ^ 2
      ≤ ∫ ξ, (∑ i : Fin d, heatK d t ξ * PDE.Kern.qf i ξ) / 16 :=
        integral_mono hint1 (hint3.div_const 16) hpt
    _ = (∑ i : Fin d, ∫ ξ, heatK d t ξ * PDE.Kern.qf i ξ) / 16 := by
        rw [integral_div, integral_finset_sum _ fun i _ => hint2 i]
    _ = d * (2 - 2 * Real.exp (-t)) / 16 := by
        simp_rw [q12_integral_K_qf ht]
        simp
        ring
    _ ≤ d * t / 8 := by
        have := Real.add_one_le_exp (-t)
        have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith

/-- The smeared measure `ν * K_t`. -/
def smearM (d : ℕ) (t : ℝ) (ν : Measure (Torus d)) : Measure (Torus d) :=
  (ν.prod (kerMeasure d t)).map fun p => p.1 + p.2

/-- The smearing coupling of `ν` and `ν * K_t`. -/
def smearCoupling (d : ℕ) (t : ℝ) (ν : Measure (Torus d)) : Measure (Torus d × Torus d) :=
  (ν.prod (kerMeasure d t)).map fun p => (p.1, p.1 + p.2)

lemma q12_smearCoupling_fst {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    (smearCoupling d t ν).map Prod.fst = ν := by
  haveI := q12_kerMeasure_prob (d := d) ht
  have hm : Measurable fun p : Torus d × Torus d => (p.1, p.1 + p.2) := by fun_prop
  unfold smearCoupling
  rw [Measure.map_map measurable_fst hm]
  have : (Prod.fst ∘ fun p : Torus d × Torus d => (p.1, p.1 + p.2)) = Prod.fst := rfl
  rw [this, Measure.map_fst_prod]
  simp

lemma q12_smearCoupling_snd (t : ℝ) (ν : Measure (Torus d)) :
    (smearCoupling d t ν).map Prod.snd = smearM d t ν := by
  have hm : Measurable fun p : Torus d × Torus d => (p.1, p.1 + p.2) := by fun_prop
  unfold smearCoupling smearM
  rw [Measure.map_map measurable_snd hm]
  rfl


lemma q12_tdist_add_left (y ξ : Torus d) : Torus.tdist y (y + ξ) = Torus.tdist ξ 0 := by
  have h1 : Torus.tdist y (y + ξ) = KernelGrad.tdist y (y + ξ) := rfl
  rw [h1, HRS.Commutator.EnergyAux.tdist_def, show y - (y + ξ) = -ξ by abel,
    HRS.Commutator.EnergyAux.tdist_neg_zero]
  rfl

lemma q12_smear_cost {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    ∫⁻ z, ENNReal.ofReal (Torus.tdist z.1 z.2 ^ (2 : ℝ)) ∂(smearCoupling d t ν) ≤
      ENNReal.ofReal (d * t / 8) := by
  haveI := q12_kerMeasure_prob (d := d) ht
  have hm : Measurable fun p : Torus d × Torus d => (p.1, p.1 + p.2) := by fun_prop
  have hf : Measurable fun z : Torus d × Torus d => ENNReal.ofReal (Torus.tdist z.1 z.2 ^ (2 : ℝ)) :=
    (q12_measurable_tdist.pow_const (2 : ℝ)).ennreal_ofReal
  have hG : Measurable fun ξ : Torus d => ENNReal.ofReal (Torus.tdist ξ 0 ^ 2) :=
    ((q12_continuous_tdist0.pow 2).measurable).ennreal_ofReal
  unfold smearCoupling
  rw [lintegral_map hf hm]
  have e : ∀ p : Torus d × Torus d, ENNReal.ofReal (Torus.tdist (p.1, p.1 + p.2).1 (p.1, p.1 + p.2).2 ^ (2 : ℝ)) =
      ENNReal.ofReal (Torus.tdist p.2 0 ^ 2) := fun p => by
    show ENNReal.ofReal (Torus.tdist p.1 (p.1 + p.2) ^ (2 : ℝ)) = _
    rw [q12_tdist_add_left, Real.rpow_two]
  simp_rw [e]
  have hG2 : Measurable fun p : Torus d × Torus d => ENNReal.ofReal (Torus.tdist p.2 0 ^ 2) :=
    hG.comp measurable_snd
  rw [lintegral_prod _ hG2.aemeasurable]
  simp only [lintegral_const, measure_univ, mul_one]
  unfold kerMeasure
  rw [lintegral_withDensity_eq_lintegral_mul _ (continuous_heatK ht).measurable.ennreal_ofReal hG]
  have hint : Integrable (fun ξ : Torus d => heatK d t ξ * Torus.tdist ξ 0 ^ 2) :=
    ((continuous_heatK ht).mul (q12_continuous_tdist0.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have e2 : ∀ ξ : Torus d, ENNReal.ofReal (heatK d t ξ) * ENNReal.ofReal (Torus.tdist ξ 0 ^ 2) =
      ENNReal.ofReal (heatK d t ξ * Torus.tdist ξ 0 ^ 2) := fun ξ => by
    rw [ENNReal.ofReal_mul (heatK_nonneg ht ξ)]
  simp only [Pi.mul_apply]
  simp_rw [e2]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ξ => mul_nonneg (heatK_nonneg ht ξ) (sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (q12_second_moment ht)

/-- `W_2(ν, ν * K_t) ≤ √(d t / 8)`. -/
theorem q12_W_smear {t : ℝ} (ht : 0 < t) (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    torusWassersteinE 2 ν (smearM d t ν) ≤ ENNReal.ofReal (Real.sqrt (d * t / 8)) := by
  refine (q12_W_le_cost (q12_smearCoupling_fst ht ν) (q12_smearCoupling_snd t ν)).trans ?_
  have h := ENNReal.rpow_le_rpow (q12_smear_cost ht ν) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  refine h.trans (le_of_eq ?_)
  have hd : (0 : ℝ) ≤ d * t / 8 := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hd (by norm_num), Real.sqrt_eq_rpow]

end HRS.Uniform.Q12
