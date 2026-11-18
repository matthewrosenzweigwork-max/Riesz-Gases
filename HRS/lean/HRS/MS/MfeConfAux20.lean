import HRS.MS.MfeConfAux19

/-!
# S.B.1, packet F3 (part 1): Gibbs integrals in Lebesgue form

For a probability density `ρ` on `ℝ^d` and a measurable kernel `k`:

* `sb1_integral_wd`, `sb1_integral_pi`: integrals against `ρ dx` and against `(ρ dx)^{⊗N}` are Lebesgue integrals against
  `ρ`, resp. `∏ ρ(x_i)`;
* `sb1PG h ρ x = ∫ ρ(y) h(x,y) dy`, `sb1_pairEnergy_eq`: the pair energy `𝖥_N^h(X, ρ dx)` written with these (no integrability
  assumption: the identity only rewrites the Bochner integrals);
* `sb1G k ρ`, `sb1c k ρ`, `sb1En k ρ`: the modulated energy of the kernel `k` (`sb1_modEnergy_eq`);
* `sb1_integral_modGibbs`: `∫ f dQ = K⁻¹ ∫ ∏ρ(x_i) e^{-βN F} f`, and `K = ∫ ∏ρ(x_i) e^{-βN F}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_integral_wd_gen {α : Type*} [MeasurableSpace α] (μ : Measure α) {h : α → ℝ}
    (hh : Measurable h) (h0 : ∀ x, 0 ≤ h x) (f : α → ℝ) :
    ∫ x, f x ∂(μ.withDensity fun x => ENNReal.ofReal (h x)) = ∫ x, h x * f x ∂μ := by
  have : (fun x => ENNReal.ofReal (h x)) = fun x => ((h x).toNNReal : ENNReal) := rfl
  rw [this, integral_withDensity_eq_integral_smul hh.real_toNNReal f]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (h0 x)]

theorem sb1_integral_wd {ρ : Euc d → ℝ} (hρ : Measurable ρ) (h0 : ∀ x, 0 ≤ ρ x) (f : Euc d → ℝ) :
    ∫ y, f y ∂(Whole.withDensityReal ρ) = ∫ y, ρ y * f y :=
  sb1_integral_wd_gen volume hρ h0 f

theorem sb1_integral_pi {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (g : Whole.EucConfig d N → ℝ) :
    ∫ X, g X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ) =
      ∫ X : Whole.EucConfig d N, (∏ i, ρ (X i)) * g X := by
  have hi : Integrable ρ := HRS.MS.Canon.cn_integrable_of_prob ρ hρ
  rw [HRS.MS.Canon.cn_pi_withDensityReal ρ hρ.nonneg hi]
  exact sb1_integral_wd_gen _ (Finset.measurable_prod _ fun i _ => hρ.measurable.comp (measurable_pi_apply i))
    (fun X => Finset.prod_nonneg fun i _ => hρ.nonneg _) g

/-- `x ↦ ∫ ρ(y) h(x,y) dy`. -/
def sb1PG (h : Euc d → Euc d → ℝ) (ρ : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y, ρ y * h x y

/-- `G(x) = ∫ ρ(y) k(x-y) dy`. -/
def sb1G (k : Euc d → ℝ) (ρ : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y, ρ y * k (x - y)

/-- `c = ∬ ρ(x) ρ(y) k(x-y)`. -/
def sb1c (k : Euc d → ℝ) (ρ : Euc d → ℝ) : ℝ := ∫ x, ρ x * sb1G k ρ x

/-- the modulated energy of the kernel `k` for the density `ρ`, written with `G` and `c`. -/
def sb1En (k : Euc d → ℝ) (ρ : Euc d → ℝ) (X : Whole.EucConfig d N) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i - X j)
    - (1 / (N : ℝ)) * ∑ i, sb1G k ρ (X i) + (1 / 2) * sb1c k ρ

theorem sb1_pairEnergy_eq {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (h : Euc d → Euc d → ℝ)
    (X : Whole.EucConfig d N) :
    Whole.pairEnergy h X (Whole.withDensityReal ρ) =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)
        - (1 / (N : ℝ)) * ∑ i, sb1PG h ρ (X i) + (1 / 2) * ∫ x, ρ x * sb1PG h ρ x := by
  unfold Whole.pairEnergy sb1PG
  simp_rw [sb1_integral_wd hρ.measurable hρ.nonneg]

theorem sb1_modEnergy_eq {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (k : Euc d → ℝ)
    (X : Whole.EucConfig d N) :
    Whole.modulatedEnergy k X (Whole.withDensityReal ρ) = sb1En k ρ X := by
  rw [← Whole.pairEnergy_diff, sb1_pairEnergy_eq hρ]
  rfl

theorem sb1_gibbsNormalizer_eq {k : Euc d → ℝ} {β : ℝ} {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) :
    Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ) =
      ∫ X : Whole.EucConfig d N, (∏ i, ρ (X i)) * Real.exp (-β * N * sb1En k ρ X) := by
  unfold Whole.gibbsNormalizer
  rw [sb1_integral_pi hρ]
  simp_rw [sb1_modEnergy_eq hρ]

theorem sb1_gibbsNormalizer_nonneg {k : Euc d → ℝ} {β : ℝ} {ρ : Euc d → ℝ} (_hρ : Whole.IsProbDensity ρ) :
    0 ≤ Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ) := by
  unfold Whole.gibbsNormalizer
  exact integral_nonneg fun X => (Real.exp_pos _).le

theorem sb1_integral_modGibbs {k : Euc d → ℝ} (hk : Measurable k) {β : ℝ} {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (f : Whole.EucConfig d N → ℝ) :
    ∫ X, f X ∂(Whole.modulatedGibbs k N β (Whole.withDensityReal ρ)) =
      (Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ))⁻¹ *
        ∫ X : Whole.EucConfig d N, (∏ i, ρ (X i)) * (Real.exp (-β * N * sb1En k ρ X) * f X) := by
  have : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  unfold Whole.modulatedGibbs
  rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal (sb1_gibbsNormalizer_nonneg hρ),
    smul_eq_mul]
  congr 1
  have hm : Measurable fun X : Whole.EucConfig d N =>
      Real.exp (-β * N * Whole.modulatedEnergy k X (Whole.withDensityReal ρ)) :=
    Real.measurable_exp.comp ((sb1_measurable_modulatedEnergy hk _).const_mul _)
  rw [sb1_integral_wd_gen _ hm (fun X => (Real.exp_pos _).le), sb1_integral_pi hρ]
  simp_rw [sb1_modEnergy_eq hρ]

/-- measurability of parametric convolution integrals `x ↦ ∫ f(y) k(x-y) dy`. -/
theorem sb1_meas_conv {f k : Euc d → ℝ} (hf : Measurable f) (hk : Measurable k) :
    Measurable (fun x => ∫ y, f y * k (x - y)) := by
  have h : StronglyMeasurable (fun p : Euc d × Euc d => f p.2 * k (p.1 - p.2)) :=
    ((hf.comp measurable_snd).mul (hk.comp (measurable_fst.sub measurable_snd))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume)).measurable

end HRS.MS.MfeConf
