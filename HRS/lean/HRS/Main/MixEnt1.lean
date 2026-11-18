import HRS.Main.ThermAux1

/-!
# MIXENT 1: density form of the mixture preparation (lemma M1)

Example 2.6 / Proposition 5.9 (TeX L6781-6800; proof of `iid_field_mixture_proof` and the entropy
computation after TeX L6952): the mixture preparation `mixturePrep μ° b a₀ N` is absolutely continuous
with respect to `π = (μ°)^{⊗N}` with the explicit density
`R_N(X) = (r₊(X) + r₋(X))/2`, `r_±(X) = ∏ᵢ (1 ± a₀ b(xᵢ)/√N)`.

Helpers carry the prefix `mx_`; they live in `HRS.Main`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- `Measure.pi` of density-modified measures is the density `∏ᵢ f(xᵢ)` of the product measure
(rectangle formula; independence of coordinates under `Measure.pi`). -/
theorem mx_pi_withDensity {ι : Type*} [Fintype ι] {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ≥0∞) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    Measure.pi (fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity (fun x => ∏ i, f (x i)) := by
  refine Measure.pi_eq (μ := fun _ : ι => μ.withDensity f) fun s hs => ?_
  have hms : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hms, ← lintegral_indicator hms]
  have h1 : (Set.univ.pi s).indicator (fun X : ι → α => ∏ i, f (X i)) =
      fun X => ∏ i, (s i).indicator f (X i) := by
    funext X
    by_cases h : ∀ i, X i ∈ s i
    · rw [Set.indicator_of_mem (by simpa using h)]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (h i) f).symm
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Set.indicator_of_notMem (by simpa using ⟨i, hi⟩)]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [h1]
  have hmeas : ∀ i, Measurable ((s i).indicator f) := fun i => hf.indicator (hs i)
  have hind : iIndepFun (fun (i : ι) (X : ι → α) => (s i).indicator f (X i))
      (Measure.pi fun _ : ι => μ) :=
    iIndepFun_pi (μ := fun _ : ι => μ) (X := fun i => (s i).indicator f)
      fun i => (hmeas i).aemeasurable
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hmeas i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : ∫⁻ X : ι → α, (s i).indicator f (X i) ∂(Measure.pi fun _ : ι => μ) =
      ∫⁻ y, (s i).indicator f y ∂μ :=
    (measurePreserving_eval (fun _ : ι => μ) i).lintegral_comp (hmeas i)
  rw [h2, lintegral_indicator (hs i), withDensity_apply _ (hs i)]

/-- The density (relative to `π = μ^{⊗N}`) of the mixture preparation, in `ℝ≥0∞`:
`(∏ᵢ ofReal(1 + a₀ b(xᵢ)/√N) + ∏ᵢ ofReal(1 - a₀ b(xᵢ)/√N)) / 2`. -/
def mxDens (b : Torus d → ℝ) (a₀ : ℝ) (N : ℕ) (X : Config d N) : ℝ≥0∞ :=
  (2 : ℝ≥0∞)⁻¹ * (∏ i, ENNReal.ofReal (1 + a₀ * b (X i) / Real.sqrt N) +
    ∏ i, ENNReal.ofReal (1 - a₀ * b (X i) / Real.sqrt N))

/-- The real product densities `r_±(X) = ∏ᵢ (1 ± a₀ b(xᵢ)/√N)`. -/
def mxRp (b : Torus d → ℝ) (a₀ : ℝ) (N : ℕ) (X : Config d N) : ℝ :=
  ∏ i, (1 + a₀ * b (X i) / Real.sqrt N)

/-- `r₋(X) = ∏ᵢ (1 - a₀ b(xᵢ)/√N)`. -/
def mxRm (b : Torus d → ℝ) (a₀ : ℝ) (N : ℕ) (X : Config d N) : ℝ :=
  ∏ i, (1 - a₀ * b (X i) / Real.sqrt N)

/-- The real mixture density `R = (r₊ + r₋)/2`. -/
def mxR (b : Torus d → ℝ) (a₀ : ℝ) (N : ℕ) (X : Config d N) : ℝ :=
  (mxRp b a₀ N X + mxRm b a₀ N X) / 2

theorem mx_measurable_mxDens {b : Torus d → ℝ} (hb : Measurable b) (a₀ : ℝ) (N : ℕ) :
    Measurable (mxDens b a₀ N) := by
  unfold mxDens
  refine Measurable.const_mul (Measurable.add ?_ ?_) _
  · exact Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp (by fun_prop)
  · exact Finset.measurable_prod _ fun i _ =>
      ENNReal.measurable_ofReal.comp (by fun_prop)

/-- **M1** (density form of the mixture preparation; TeX L6781-6800 with the proof after L6952).
For every probability measure `μ` (in particular `μ°`), every measurable `b` and every `N`,
the mixture preparation equals `μ^{⊗N}` with density `mxDens b a₀ N = (r₊ + r₋)/2`.  No
positivity hypothesis is needed (all densities are `ofReal`). -/
theorem mx_mixturePrep_eq_withDensity (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (b : Torus d → ℝ) (hb : Measurable b) (a₀ : ℝ) (N : ℕ) :
    mixturePrep μ b a₀ N = (Measure.pi fun _ : Fin N => μ).withDensity (mxDens b a₀ N) := by
  have hp : Measurable fun x => ENNReal.ofReal (1 + a₀ * b x / Real.sqrt N) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hm : Measurable fun x => ENNReal.ofReal (1 - a₀ * b x / Real.sqrt N) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have s1 : SigmaFinite (μ.withDensity fun x => ENNReal.ofReal (1 + a₀ * b x / Real.sqrt N)) := by
    infer_instance
  have s2 : SigmaFinite (μ.withDensity fun x => ENNReal.ofReal (1 - a₀ * b x / Real.sqrt N)) := by
    infer_instance
  have hP : Measurable fun X : Config d N =>
      ∏ i, ENNReal.ofReal (1 + a₀ * b (X i) / Real.sqrt N) :=
    Finset.measurable_prod _ fun i _ => hp.comp (measurable_pi_apply i)
  have hM : Measurable fun X : Config d N =>
      ∏ i, ENNReal.ofReal (1 - a₀ * b (X i) / Real.sqrt N) :=
    Finset.measurable_prod _ fun i _ => hm.comp (measurable_pi_apply i)
  unfold mixturePrep
  rw [mx_pi_withDensity μ _ hp, mx_pi_withDensity μ _ hm]
  have e : mxDens b a₀ N = (fun X : Config d N => (2⁻¹ : ℝ≥0∞) *
        (∏ i, ENNReal.ofReal (1 + a₀ * b (X i) / Real.sqrt N))) +
      (fun X : Config d N => (2⁻¹ : ℝ≥0∞) * ∏ i, ENNReal.ofReal (1 - a₀ * b (X i) / Real.sqrt N)) := by
    funext X; simp only [mxDens, mul_add, Pi.add_apply]
  rw [e, withDensity_add_left (hP.const_mul _)]
  have h1 := withDensity_smul (μ := Measure.pi fun _ : Fin N => μ) (2⁻¹ : ℝ≥0∞) hP
  have h2 := withDensity_smul (μ := Measure.pi fun _ : Fin N => μ) (2⁻¹ : ℝ≥0∞) hM
  simp only [Pi.smul_def, smul_eq_mul] at h1 h2
  rw [h1, h2, one_div]


/-- Under `|a₀ b| ≤ √N/2` the one-factor densities `1 ± a₀ b/√N` lie in `[1/2, 3/2]`. -/
theorem mx_factor_bounds {b : Torus d → ℝ} {a₀ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) (x : Torus d) :
    1 / 2 ≤ 1 + a₀ * b x / Real.sqrt N ∧ 1 + a₀ * b x / Real.sqrt N ≤ 3 / 2 ∧
      1 / 2 ≤ 1 - a₀ * b x / Real.sqrt N ∧ 1 - a₀ * b x / Real.sqrt N ≤ 3 / 2 := by
  have hN0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have h := abs_le.1 ((hB x))
  have h1 : a₀ * b x / Real.sqrt N ≤ 1 / 2 := by
    rw [div_le_iff₀ hN0]; linarith [h.2]
  have h2 : -(1 / 2) ≤ a₀ * b x / Real.sqrt N := by
    rw [le_div_iff₀ hN0]; linarith [h.1]
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem mx_Rp_pos {b : Torus d → ℝ} {a₀ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) (X : Config d N) : 0 < mxRp b a₀ N X :=
  Finset.prod_pos fun i _ => by linarith [(mx_factor_bounds hN hB (X i)).1]

theorem mx_Rm_pos {b : Torus d → ℝ} {a₀ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) (X : Config d N) : 0 < mxRm b a₀ N X :=
  Finset.prod_pos fun i _ => by linarith [(mx_factor_bounds hN hB (X i)).2.2.1]

theorem mx_R_pos {b : Torus d → ℝ} {a₀ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) (X : Config d N) : 0 < mxR b a₀ N X := by
  unfold mxR
  have := mx_Rp_pos hN hB X
  have := mx_Rm_pos hN hB X
  positivity

/-- Real form of the density: `mxDens = ofReal ∘ mxR` once the factors are positive. -/
theorem mx_dens_eq_ofReal {b : Torus d → ℝ} {a₀ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) (X : Config d N) :
    mxDens b a₀ N X = ENNReal.ofReal (mxR b a₀ N X) := by
  unfold mxDens mxR mxRp mxRm
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [(mx_factor_bounds hN hB (X i)).1]),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => by linarith [(mx_factor_bounds hN hB (X i)).2.2.1]),
    ← ENNReal.ofReal_add (Finset.prod_nonneg fun i _ => by linarith [(mx_factor_bounds hN hB (X i)).1])
      (Finset.prod_nonneg fun i _ => by linarith [(mx_factor_bounds hN hB (X i)).2.2.1]),
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos (by norm_num), ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; ring

/-- **M1, real form**: under `|a₀ b| ≤ √N/2` the mixture preparation is `μ^{⊗N}` with the
positive real density `R = (r₊ + r₋)/2`. -/
theorem mx_mixturePrep_eq_withDensity_real (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (b : Torus d → ℝ) (hb : Measurable b) (a₀ : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hB : ∀ x, |a₀ * b x| ≤ Real.sqrt N / 2) :
    mixturePrep μ b a₀ N =
      (Measure.pi fun _ : Fin N => μ).withDensity (fun X => ENNReal.ofReal (mxR b a₀ N X)) := by
  rw [mx_mixturePrep_eq_withDensity μ b hb]
  congr 1
  funext X
  exact mx_dens_eq_ofReal hN hB X

end Main

end HRS
