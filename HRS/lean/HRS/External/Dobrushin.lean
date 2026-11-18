/-
# HRS.External.Dobrushin -- one-site specifications and the Dobrushin contraction (EXT-1, E0 + E1)

Abstract setting only: a finite product `Fin n → E` of a measurable space `E`.

* `Spec E n` (E0): a probability measure `P` on `Fin n → E` with one-site Markov kernels `G i`
  (law of coordinate `i` given the rest; `G i x` does not depend on `x i`) such that resampling
  coordinate `i` from `G i` preserves `P`. Operators `Spec.site i` (`G_i` acting on functions),
  `Spec.scan` (random scan `n⁻¹ ∑ᵢ G_i`), `Spec.siteVar i F x` (`Var_i F(x)`, an `evariance`).
  Basic algebra: reversibility `∫ f · G_i g = ∫ G_i f · g` (`integral_mul_site`).
* `Spec.ofDensity` (E0): the explicit instance `P = (μ^n).withDensity W` for `μ` a probability
  measure and `W` measurable, strictly positive, bounded with `∫ W d(μ^n) = 1`; the kernel is
  `siteKernel μ W i`, with `μ`-density `z ↦ W(x^{i ← z}) / ∫ W(x^{i ← z'}) μ(dz')`.
* Dobrushin core (E1): `IsDobrushin S c` (interdependence coefficients, discrete-metric Wasserstein
  distance of one-site kernels), the oscillation estimate
  `δ_j(P g) ≤ (1 - 1/n) δ_j g + n⁻¹ ∑_i c_ij δ_i g` (`abs_site_sub_le`, `exists_osc_scan`),
  telescoping and the geometric decay of `‖P^k g - ∫ g dP‖_∞`
  (`abs_scan_iterate_sub_integral_le`).
-/
import Mathlib

open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

section PiUpdate

/-- Resampling one coordinate from `μ` does not change the product measure. -/
lemma pi_map_update (μ : Measure E) [IsProbabilityMeasure μ] (i : Fin n) :
    ((Measure.pi fun _ : Fin n => μ).prod μ).map
      (fun p : (Fin n → E) × E => update p.1 i p.2) = Measure.pi fun _ : Fin n => μ := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hs)]
  have : (fun p : (Fin n → E) × E => update p.1 i p.2) ⁻¹' (Set.univ.pi s)
      = (Set.univ.pi (update s i Set.univ)) ×ˢ (s i) := by
    ext ⟨x, w⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun k => ?_, by simpa using h i⟩
      by_cases hk : k = i
      · subst hk; simp
      · simpa [hk] using h k
    · rintro ⟨h1, h2⟩ k
      by_cases hk : k = i
      · subst hk; simpa using h2
      · simpa [hk] using h1 k
  rw [this, Measure.prod_prod, Measure.pi_pi]
  have h1 : ∀ k, μ (update s i Set.univ k) = update (fun k => μ (s k)) i 1 k := by
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  simp_rw [h1]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i), ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp [Finset.sdiff_singleton_eq_erase]
  ring

/-- Resampling identity for the product measure. -/
lemma lintegral_pi_update (μ : Measure E) [IsProbabilityMeasure μ] (i : Fin n)
    {φ : (Fin n → E) → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, φ x ∂(Measure.pi fun _ : Fin n => μ)
      = ∫⁻ x, ∫⁻ w, φ (update x i w) ∂μ ∂(Measure.pi fun _ : Fin n => μ) := by
  conv_lhs => rw [← pi_map_update μ i]
  rw [lintegral_map hφ measurable_update']
  exact lintegral_prod (fun p : (Fin n → E) × E => φ (update p.1 i p.2))
    (hφ.comp measurable_update').aemeasurable

end PiUpdate

section TV

/-- Layer-cake estimate: if two probability measures differ by at most `c` on every measurable
set, then every measurable function of oscillation `≤ D` has means differing by at most `c * D`. -/
lemma abs_integral_sub_le_of_tv (ν ν' : Measure E) [IsProbabilityMeasure ν]
    [IsProbabilityMeasure ν'] {c D : ℝ} (hD : 0 ≤ D)
    (hc : ∀ A, MeasurableSet A → |ν.real A - ν'.real A| ≤ c) {h : E → ℝ} (hh : Measurable h)
    (hosc : ∀ z z', |h z - h z'| ≤ D) :
    |(∫ z, h z ∂ν) - ∫ z, h z ∂ν'| ≤ c * D := by
  have hne : Nonempty E := Measure.nonempty_of_neZero ν
  obtain ⟨z0⟩ := hne
  have : Nonempty E := ⟨z0⟩
  have hbdd : BddBelow (Set.range h) := ⟨h z0 - D, by
    rintro _ ⟨z, rfl⟩
    have := hosc z z0
    rw [abs_le] at this
    linarith⟩
  set m := ⨅ z, h z with hm
  have hmle : ∀ z, m ≤ h z := fun z => ciInf_le hbdd z
  have hle : ∀ z, h z ≤ m + D := by
    intro z
    have : h z - D ≤ m := le_ciInf fun z' => by
      have := hosc z z'
      rw [abs_le] at this
      linarith
    linarith
  set k : E → ℝ := fun z => h z - m with hk
  have hkm : Measurable k := hh.sub_const m
  have hk0 : ∀ z, 0 ≤ k z := fun z => sub_nonneg.mpr (hmle z)
  have hkD : ∀ z, k z ≤ D := fun z => by simp only [hk]; linarith [hle z]
  have hint : ∀ (ρ : Measure E) [IsProbabilityMeasure ρ], Integrable k ρ := fun ρ _ =>
    Integrable.of_bound hkm.aestronglyMeasurable D (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_of_nonneg (hk0 z)]; exact hkD z)
  have hlayer : ∀ (ρ : Measure E) [IsProbabilityMeasure ρ],
      ∫ z, k z ∂ρ = ∫ t in Set.Ioc 0 D, ρ.real {a | t ≤ k a} :=
    fun ρ _ => Integrable.integral_eq_integral_Ioc_meas_le (hint ρ)
      (Filter.Eventually.of_forall hk0) (Filter.Eventually.of_forall hkD)
  have hintOn : ∀ (ρ : Measure E) [IsProbabilityMeasure ρ],
      IntegrableOn (fun t => ρ.real {a | t ≤ k a}) (Set.Ioc 0 D) := by
    intro ρ _
    refine Measure.integrableOn_of_bounded (M := 1) (by simp) ?_ ?_
    · refine (Antitone.measurable ?_).aestronglyMeasurable
      intro s t hst
      exact measureReal_mono (fun a ha => le_trans hst ha)
    · refine Filter.Eventually.of_forall fun t => ?_
      rw [Real.norm_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hdiff : (∫ z, h z ∂ν) - ∫ z, h z ∂ν' = (∫ z, k z ∂ν) - ∫ z, k z ∂ν' := by
    have e : ∀ (ρ : Measure E) [IsProbabilityMeasure ρ], ∫ z, k z ∂ρ = (∫ z, h z ∂ρ) - m := by
      intro ρ _
      simp only [hk]
      have hhi : Integrable h ρ := Integrable.of_bound hh.aestronglyMeasurable (|h z0| + D)
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]
          have := hosc z z0
          have := abs_sub_abs_le_abs_sub (h z) (h z0)
          linarith)
      rw [integral_sub hhi (integrable_const m)]
      simp
    rw [e ν, e ν']; ring
  rw [hdiff, hlayer ν, hlayer ν', ← integral_sub (hintOn ν) (hintOn ν')]
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc 0 D)
    (f := fun t => ν.real {a | t ≤ k a} - ν'.real {a | t ≤ k a}) (C := c)
    (by simp) (fun t _ => by
      rw [Real.norm_eq_abs]; exact hc _ (measurableSet_le measurable_const hkm))
  simpa [Real.norm_eq_abs, hD, mul_comm] using this

end TV

section Spec

/-- A reversible one-site specification on the finite product `Fin n → E`: a probability
measure `P` together with Markov kernels `G i` giving the law of the `i`-th coordinate given the
others (the kernel does not depend on coordinate `i`), such that resampling coordinate `i`
from `G i` preserves `P`. -/
structure Spec (E : Type*) [MeasurableSpace E] (n : ℕ) where
  P : Measure (Fin n → E)
  G : Fin n → Kernel (Fin n → E) E
  isProb : IsProbabilityMeasure P
  isMarkov : ∀ i, IsMarkovKernel (G i)
  local_eq : ∀ i x y, (∀ k, k ≠ i → x k = y k) → G i x = G i y
  invariant : ∀ (i : Fin n) (φ : (Fin n → E) → ℝ≥0∞), Measurable φ →
    ∫⁻ x, ∫⁻ z, φ (update x i z) ∂(G i x) ∂P = ∫⁻ x, φ x ∂P

attribute [instance] Spec.isProb Spec.isMarkov

namespace Spec

variable (S : Spec E n)

/-- One-site averaging operator `(G_i g)(x) = ∫ g(x^{i ← z}) G_i(x, dz)`. -/
def site (i : Fin n) (g : (Fin n → E) → ℝ) (x : Fin n → E) : ℝ :=
  ∫ z, g (update x i z) ∂(S.G i x)

/-- Random-scan operator `P = n⁻¹ ∑ᵢ G_i`. -/
def scan (g : (Fin n → E) → ℝ) (x : Fin n → E) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, S.site i g x

/-- Conditional variance of `F` in coordinate `i`, `Var_i F (x)`. -/
def siteVar (i : Fin n) (F : (Fin n → E) → ℝ) (x : Fin n → E) : ℝ≥0∞ :=
  evariance (fun z => F (update x i z)) (S.G i x)

variable {S}

lemma measurable_section (g : (Fin n → E) → ℝ) (hg : Measurable g) (i : Fin n)
    (x : Fin n → E) : Measurable fun z => g (update x i z) :=
  hg.comp (measurable_update x)

lemma integrable_section {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ M) (i : Fin n) (x : Fin n → E) :
    Integrable (fun z => g (update x i z)) (S.G i x) :=
  Integrable.of_bound (measurable_section g hg i x).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb _)

lemma measurable_site {g : (Fin n → E) → ℝ} (hg : Measurable g) (i : Fin n) :
    Measurable (S.site i g) := by
  have h : StronglyMeasurable fun p : (Fin n → E) × E => g (update p.1 i p.2) :=
    (hg.comp measurable_update').stronglyMeasurable
  exact (h.integral_kernel_prod_right' (κ := S.G i)).measurable

lemma abs_site_le {M : ℝ} {g : (Fin n → E) → ℝ} (hb : ∀ x, |g x| ≤ M) (i : Fin n)
    (x : Fin n → E) : |S.site i g x| ≤ M := by
  have := norm_integral_le_of_norm_le_const (μ := S.G i x)
    (f := fun z => g (update x i z)) (C := M)
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb _)
  simpa [site] using this

lemma integrable_of_bdd {ρ : Measure (Fin n → E)} [IsFiniteMeasure ρ] {M : ℝ}
    {g : (Fin n → E) → ℝ} (hg : Measurable g) (hb : ∀ x, |g x| ≤ M) : Integrable g ρ :=
  Integrable.of_bound hg.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb _)

lemma site_const (c : ℝ) (i : Fin n) (x : Fin n → E) : S.site i (fun _ => c) x = c := by
  simp [site]

lemma site_add {M : ℝ} {f g : (Fin n → E) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ M) (i : Fin n) (x : Fin n → E) :
    S.site i (fun y => f y + g y) x = S.site i f x + S.site i g x :=
  integral_add (integrable_section hf hfb i x) (integrable_section hg hgb i x)

lemma site_sub {M : ℝ} {f g : (Fin n → E) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hfb : ∀ x, |f x| ≤ M) (hgb : ∀ x, |g x| ≤ M) (i : Fin n) (x : Fin n → E) :
    S.site i (fun y => f y - g y) x = S.site i f x - S.site i g x :=
  integral_sub (integrable_section hf hfb i x) (integrable_section hg hgb i x)

lemma site_const_mul (c : ℝ) (g : (Fin n → E) → ℝ) (i : Fin n) (x : Fin n → E) :
    S.site i (fun y => c * g y) x = c * S.site i g x :=
  integral_const_mul c _

lemma site_add_const {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ M) (c : ℝ) (i : Fin n) (x : Fin n → E) :
    S.site i (fun y => g y + c) x = S.site i g x + c := by
  have := site_add (S := S) (M := |M| + |c|) hg measurable_const
    (fun x => by linarith [hb x, le_abs_self M, abs_nonneg c])
    (fun _ => by linarith [abs_nonneg M]) i x
  simpa [site_const] using this

lemma site_local (g : (Fin n → E) → ℝ) (i : Fin n) {x y : Fin n → E}
    (hxy : ∀ k, k ≠ i → x k = y k) : S.site i g x = S.site i g y := by
  have : update x i = update y i := by
    funext z k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk, hxy k hk]
  simp only [site, S.local_eq i x y hxy, this]

lemma site_mul_local (g h : (Fin n → E) → ℝ) (i : Fin n)
    (hh : ∀ x y, (∀ k, k ≠ i → x k = y k) → h x = h y) (x : Fin n → E) :
    S.site i (fun y => h y * g y) x = h x * S.site i g x := by
  simp only [site]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  rw [hh (update x i z) x]
  intro k hk; simp [hk]

/-- `P` is invariant under resampling one coordinate (bounded measurable test functions). -/
lemma integral_site {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ M) (i : Fin n) :
    ∫ x, S.site i g x ∂S.P = ∫ x, g x ∂S.P := by
  set g' : (Fin n → E) → ℝ := fun y => g y + |M| with hg'
  have hg'm : Measurable g' := hg.add_const _
  have hg'0 : ∀ y, 0 ≤ g' y := fun y => by
    have := hb y
    have := neg_abs_le (g y)
    linarith [le_abs_self M]
  have hg'b : ∀ y, |g' y| ≤ 2 * |M| := fun y => by
    rw [abs_of_nonneg (hg'0 y)]
    have h1 : g' y = g y + |M| := rfl
    linarith [hb y, le_abs_self M, le_abs_self (g y)]
  have hsite : ∀ x, S.site i g' x = S.site i g x + |M| := fun x => site_add_const hg hb _ i x
  have hsm : Measurable (S.site i g') := measurable_site hg'm i
  have hs0 : ∀ x, 0 ≤ S.site i g' x := fun x =>
    integral_nonneg fun z => hg'0 _
  have key : ∫⁻ x, ENNReal.ofReal (S.site i g' x) ∂S.P = ∫⁻ x, ENNReal.ofReal (g' x) ∂S.P := by
    have h1 : ∀ x, ENNReal.ofReal (S.site i g' x)
        = ∫⁻ z, ENNReal.ofReal (g' (update x i z)) ∂(S.G i x) := fun x =>
      ofReal_integral_eq_lintegral_ofReal (integrable_section hg'm hg'b i x)
        (Filter.Eventually.of_forall fun z => hg'0 _)
    simp_rw [h1]
    exact S.invariant i (fun y => ENNReal.ofReal (g' y)) hg'm.ennreal_ofReal
  have e1 : ∫ x, S.site i g' x ∂S.P = ∫ x, g' x ∂S.P := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hs0)
      hsm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg'0)
      hg'm.aestronglyMeasurable, key]
  have hsb : ∀ x, |S.site i g x| ≤ M := fun x => abs_site_le hb i x
  have hi1 : Integrable (S.site i g) S.P := integrable_of_bdd (measurable_site hg i) hsb
  have hi2 : Integrable g S.P := integrable_of_bdd hg hb
  simp only [hsite] at e1
  simp only [hg'] at e1
  rw [integral_add hi1 (integrable_const _), integral_add hi2 (integrable_const _)] at e1
  linarith

/-- Reversibility of one-site resampling: `∫ f · G_i g = ∫ G_i f · G_i g`. -/
lemma integral_mul_site {Mf Mg : ℝ} {f g : (Fin n → E) → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hfb : ∀ x, |f x| ≤ Mf) (hgb : ∀ x, |g x| ≤ Mg) (i : Fin n) :
    ∫ x, f x * S.site i g x ∂S.P = ∫ x, S.site i f x * S.site i g x ∂S.P := by
  have hsg : Measurable (S.site i g) := measurable_site hg i
  have hsgb : ∀ x, |S.site i g x| ≤ Mg := fun x => abs_site_le hgb i x
  have hm : Measurable fun x => S.site i g x * f x := hsg.mul hf
  have hb : ∀ x, |S.site i g x * f x| ≤ Mg * Mf := fun x => by
    rw [abs_mul]
    exact mul_le_mul (hsgb x) (hfb x) (abs_nonneg _) ((abs_nonneg _).trans (hsgb x))
  have := integral_site (S := S) hm hb i
  have e : ∀ x, S.site i (fun y => S.site i g y * f y) x = S.site i f x * S.site i g x := by
    intro x
    rw [site_mul_local f (S.site i g) i (fun x y h => site_local g i h) x]
    ring
  simp_rw [e] at this
  rw [this]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)

lemma integral_site_mul_comm {Mf Mg : ℝ} {f g : (Fin n → E) → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hfb : ∀ x, |f x| ≤ Mf) (hgb : ∀ x, |g x| ≤ Mg) (i : Fin n) :
    ∫ x, f x * S.site i g x ∂S.P = ∫ x, S.site i f x * g x ∂S.P := by
  rw [integral_mul_site hf hg hfb hgb i]
  have := integral_mul_site (S := S) hg hf hgb hfb i
  have h2 : ∫ x, S.site i g x * S.site i f x ∂S.P = ∫ x, S.site i f x * S.site i g x ∂S.P :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  have h3 : ∫ x, S.site i f x * g x ∂S.P = ∫ x, g x * S.site i f x ∂S.P :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  rw [h3, this, h2]

lemma measurable_scan {g : (Fin n → E) → ℝ} (hg : Measurable g) : Measurable (S.scan g) := by
  unfold scan
  exact (Finset.measurable_sum _ fun i _ => measurable_site hg i).const_mul _

lemma abs_scan_le [NeZero n] {M : ℝ} {g : (Fin n → E) → ℝ} (hb : ∀ x, |g x| ≤ M)
    (x : Fin n → E) : |S.scan g x| ≤ M := by
  unfold scan
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hn)]
  have : |∑ i, S.site i g x| ≤ ∑ i : Fin n, M :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => abs_site_le hb i x)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  calc 1 / (n : ℝ) * |∑ i, S.site i g x| ≤ 1 / (n : ℝ) * (n * M) :=
        mul_le_mul_of_nonneg_left this (one_div_pos.mpr hn).le
    _ = M := by field_simp

lemma scan_add_const [NeZero n] {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ M) (c : ℝ) (x : Fin n → E) :
    S.scan (fun y => g y + c) x = S.scan g x + c := by
  unfold scan
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp_rw [site_add_const hg hb c _ x]
  rw [Finset.sum_add_distrib]
  simp
  field_simp

lemma scan_const [NeZero n] (c : ℝ) (x : Fin n → E) : S.scan (fun _ => c) x = c := by
  unfold scan
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp_rw [site_const]
  simp
  field_simp

lemma integral_scan [NeZero n] {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ M) : ∫ x, S.scan g x ∂S.P = ∫ x, g x ∂S.P := by
  unfold scan
  rw [integral_const_mul, integral_finsetSum _ fun i _ =>
    integrable_of_bdd (measurable_site hg i) (abs_site_le hb i)]
  simp_rw [integral_site hg hb]
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  simp
  field_simp

lemma integral_mul_scan_comm [NeZero n] {Mf Mg : ℝ} {f g : (Fin n → E) → ℝ} (hf : Measurable f)
    (hg : Measurable g) (hfb : ∀ x, |f x| ≤ Mf) (hgb : ∀ x, |g x| ≤ Mg) :
    ∫ x, f x * S.scan g x ∂S.P = ∫ x, S.scan f x * g x ∂S.P := by
  unfold scan
  have e1 : ∀ x, f x * ((1 / (n : ℝ)) * ∑ i, S.site i g x)
      = (1 / (n : ℝ)) * ∑ i, f x * S.site i g x := fun x => by
    rw [mul_left_comm, Finset.mul_sum]
  have e2 : ∀ x, ((1 / (n : ℝ)) * ∑ i, S.site i f x) * g x
      = (1 / (n : ℝ)) * ∑ i, S.site i f x * g x := fun x => by
    rw [mul_assoc, Finset.sum_mul]
  simp_rw [e1, e2]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  have h1 : ∫ x, ∑ i, f x * S.site i g x ∂S.P = ∑ i, ∫ x, f x * S.site i g x ∂S.P :=
    integral_finsetSum _ fun i _ => integrable_of_bdd (hf.mul (measurable_site hg i))
      (M := |Mf| * |Mg|) (fun x => by
        rw [abs_mul]
        exact mul_le_mul ((hfb x).trans (le_abs_self _)) ((abs_site_le hgb i x).trans (le_abs_self _))
          (abs_nonneg _) (abs_nonneg _))
  have h2 : ∫ x, ∑ i, S.site i f x * g x ∂S.P = ∑ i, ∫ x, S.site i f x * g x ∂S.P :=
    integral_finsetSum _ fun i _ => integrable_of_bdd ((measurable_site hf i).mul hg)
      (M := |Mf| * |Mg|) (fun x => by
        rw [abs_mul]
        exact mul_le_mul ((abs_site_le hfb i x).trans (le_abs_self _)) ((hgb x).trans (le_abs_self _))
          (abs_nonneg _) (abs_nonneg _))
  rw [h1, h2]
  exact Finset.sum_congr rfl fun i _ => integral_site_mul_comm hf hg hfb hgb i

end Spec

end Spec

section Density

variable (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)

/-- Normalizer `Z_i(x) = ∫ W(x^{i ← z}) μ(dz)` of the one-site conditional density. -/
def normalizer (i : Fin n) (x : Fin n → E) : ℝ≥0∞ := ∫⁻ z, W (update x i z) ∂μ

/-- The one-site conditional kernel of the law `(μ^n).withDensity W`: the density of
`G_i(x, ·)` with respect to `μ` is `z ↦ W(x^{i ← z}) / Z_i(x)`. -/
def siteKernel (i : Fin n) : Kernel (Fin n → E) E :=
  Kernel.withDensity (Kernel.const (Fin n → E) μ)
    (fun x z => W (update x i z) * (normalizer μ W i x)⁻¹)

variable {μ W}

lemma update_update_same (x : Fin n → E) (i : Fin n) (w z : E) :
    update (update x i w) i z = update x i z := by simp

lemma normalizer_update (i : Fin n) (x : Fin n → E) (w : E) :
    normalizer μ W i (update x i w) = normalizer μ W i x := by
  simp [normalizer]

lemma measurable_normalizer (hW : Measurable W) (i : Fin n) : Measurable (normalizer μ W i) := by
  unfold normalizer
  exact (hW.comp measurable_update').lintegral_prod_right'

lemma normalizer_pos (hpos : ∀ x, 0 < W x) (hW : Measurable W) (i : Fin n)
    (x : Fin n → E) : 0 < normalizer μ W i x := by
  unfold normalizer
  rw [pos_iff_ne_zero]
  intro h
  have hm : Measurable fun z => W (update x i z) := hW.comp (measurable_update x)
  rw [lintegral_eq_zero_iff hm] at h
  have hne : ∀ᵐ z ∂μ, False := by
    filter_upwards [h] with z hz
    exact (hpos _).ne' hz
  have := (ae_iff.mp hne)
  simp at this

lemma normalizer_lt_top {K : ℝ≥0} (hbd : ∀ x, W x ≤ K) (i : Fin n) (x : Fin n → E) :
    normalizer μ W i x < ∞ := by
  unfold normalizer
  calc ∫⁻ z, W (update x i z) ∂μ ≤ ∫⁻ _, (K : ℝ≥0∞) ∂μ := lintegral_mono fun z => hbd _
    _ = K := by simp
    _ < ∞ := ENNReal.coe_lt_top

lemma measurable_density (hW : Measurable W) (i : Fin n) :
    Measurable (Function.uncurry fun (x : Fin n → E) (z : E) =>
      W (update x i z) * (normalizer μ W i x)⁻¹) := by
  have h1 : Measurable fun p : (Fin n → E) × E => W (update p.1 i p.2) :=
    hW.comp measurable_update'
  have h2 : Measurable fun p : (Fin n → E) × E => (normalizer μ W i p.1)⁻¹ :=
    (measurable_normalizer hW i).inv.comp measurable_fst
  exact h1.mul h2

lemma siteKernel_apply (hW : Measurable W) (i : Fin n) (x : Fin n → E) :
    siteKernel μ W i x = μ.withDensity fun z => W (update x i z) * (normalizer μ W i x)⁻¹ := by
  unfold siteKernel
  rw [Kernel.withDensity_apply _ (measurable_density hW i)]
  rfl

lemma lintegral_siteKernel (hW : Measurable W) (i : Fin n) (x : Fin n → E)
    {φ : E → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ z, φ z ∂(siteKernel μ W i x)
      = ∫⁻ z, W (update x i z) * (normalizer μ W i x)⁻¹ * φ z ∂μ := by
  unfold siteKernel
  rw [Kernel.lintegral_withDensity _ (measurable_density hW i) _ hφ]
  rfl

lemma isMarkov_siteKernel (hW : Measurable W) (hpos : ∀ x, 0 < W x) {K : ℝ≥0}
    (hbd : ∀ x, W x ≤ K) (i : Fin n) : IsMarkovKernel (siteKernel μ W i) := by
  refine ⟨fun x => ⟨?_⟩⟩
  have h := lintegral_siteKernel (μ := μ) hW i x (φ := fun _ => 1) measurable_const
  simp only [lintegral_const, mul_one, one_mul] at h
  have hm : Measurable fun z => W (update x i z) := hW.comp (measurable_update x)
  rw [h, lintegral_mul_const _ hm]
  exact ENNReal.mul_inv_cancel (normalizer_pos hpos hW i x).ne' (normalizer_lt_top hbd i x).ne

lemma siteKernel_local (i : Fin n) {x y : Fin n → E} (hxy : ∀ k, k ≠ i → x k = y k)
    (hW : Measurable W) : siteKernel μ W i x = siteKernel μ W i y := by
  have : update x i = update y i := by
    funext z k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk, hxy k hk]
  rw [siteKernel_apply hW, siteKernel_apply hW]
  simp only [normalizer, this]

/-- Invariance of `(μ^n).withDensity W` under resampling coordinate `i` from `G_i`. -/
lemma invariant_density (hW : Measurable W) (hpos : ∀ x, 0 < W x) {K : ℝ≥0}
    (hbd : ∀ x, W x ≤ K) (i : Fin n) {φ : (Fin n → E) → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, ∫⁻ z, φ (update x i z) ∂(siteKernel μ W i x) ∂((Measure.pi fun _ : Fin n => μ).withDensity W)
      = ∫⁻ x, φ x ∂((Measure.pi fun _ : Fin n => μ).withDensity W) := by
  set PP : Measure (Fin n → E) := Measure.pi fun _ : Fin n => μ with hPP
  have hZm := measurable_normalizer (μ := μ) hW i
  set A : (Fin n → E) → ℝ≥0∞ := fun x => ∫⁻ z, W (update x i z) * φ (update x i z) ∂μ with hA
  have hAm : Measurable A := by
    have : Measurable fun p : (Fin n → E) × E => W (update p.1 i p.2) * φ (update p.1 i p.2) :=
      (hW.comp measurable_update').mul (hφ.comp measurable_update')
    exact this.lintegral_prod_right'
  have hAupd : ∀ x w, A (update x i w) = A x := fun x w => by simp [hA]
  have hinner : ∀ x, ∫⁻ z, φ (update x i z) ∂(siteKernel μ W i x) = (normalizer μ W i x)⁻¹ * A x := by
    intro x
    rw [lintegral_siteKernel hW i x (φ := fun z => φ (update x i z)) (hφ.comp (measurable_update x))]
    have : ∀ z, W (update x i z) * (normalizer μ W i x)⁻¹ * φ (update x i z)
        = (normalizer μ W i x)⁻¹ * (W (update x i z) * φ (update x i z)) := fun z => by ring
    simp_rw [this]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr (normalizer_pos hpos hW i x).ne')]
  have hinnerm : Measurable fun x => (normalizer μ W i x)⁻¹ * A x := hZm.inv.mul hAm
  simp_rw [hinner]
  rw [lintegral_withDensity_eq_lintegral_mul _ hW hinnerm,
    lintegral_withDensity_eq_lintegral_mul _ hW hφ]
  have hL : Measurable fun x => (W * fun x => (normalizer μ W i x)⁻¹ * A x) x :=
    hW.mul hinnerm
  have hR : Measurable fun x => (W * φ) x := hW.mul hφ
  rw [lintegral_pi_update μ i hL, lintegral_pi_update μ i hR]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply, normalizer_update, hAupd]
  have hm : Measurable fun z => W (update x i z) := hW.comp (measurable_update x)
  have e1 : ∫⁻ w, W (update x i w) * ((normalizer μ W i x)⁻¹ * A x) ∂μ = A x := by
    rw [lintegral_mul_const _ hm]
    change normalizer μ W i x * ((normalizer μ W i x)⁻¹ * A x) = A x
    rw [← mul_assoc, ENNReal.mul_inv_cancel (normalizer_pos hpos hW i x).ne'
      (normalizer_lt_top hbd i x).ne, one_mul]
  rw [e1]

/-- The one-site specification of the law `(μ^n).withDensity W`, for a measurable, strictly
positive and bounded density `W` with `∫ W d(μ^n) = 1`. -/
def Spec.ofDensity (μ : Measure E) [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞)
    (hW : Measurable W) (hpos : ∀ x, 0 < W x) (K : ℝ≥0) (hbd : ∀ x, W x ≤ K)
    (hnorm : ∫⁻ x, W x ∂(Measure.pi fun _ : Fin n => μ) = 1) : Spec E n where
  P := (Measure.pi fun _ : Fin n => μ).withDensity W
  G := siteKernel μ W
  isProb := ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact hnorm⟩
  isMarkov := isMarkov_siteKernel hW hpos hbd
  local_eq := fun i _ _ h => siteKernel_local i h hW
  invariant := fun i _ hφ => invariant_density hW hpos hbd i hφ

end Density

section Core

open Spec

variable {S : Spec E n} {c : Fin n → Fin n → ℝ}

/-- Oscillation vector bound: `Δ j` bounds the oscillation of `g` in coordinate `j`. -/
def OscBound (g : (Fin n → E) → ℝ) (Δ : Fin n → ℝ) : Prop :=
  ∀ j x y, (∀ k, k ≠ j → x k = y k) → |g x - g y| ≤ Δ j

/-- Dobrushin interdependence matrix: `c i j` bounds, for `i ≠ j`, the total variation distance
`sup_A |G_i(x, A) - G_i(y, A)|` between one-site kernels at configurations `x, y` that differ only
in coordinate `j` (this is the Wasserstein distance for the discrete metric). -/
structure IsDobrushin (S : Spec E n) (c : Fin n → Fin n → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ c i j
  le : ∀ i j, i ≠ j → ∀ x y : Fin n → E, (∀ k, k ≠ j → x k = y k) → ∀ A : Set E,
    MeasurableSet A → |(S.G i x).real A - (S.G i y).real A| ≤ c i j

lemma update_agree {x y : Fin n → E} {j : Fin n} (hxy : ∀ k, k ≠ j → x k = y k) (i : Fin n)
    (z : E) : ∀ k, k ≠ j → update x i z k = update y i z k := by
  intro k hk
  by_cases hki : k = i
  · subst hki; simp
  · simp [hki, hxy k hk]

lemma update_agree' (y : Fin n → E) (i : Fin n) (z z' : E) :
    ∀ k, k ≠ i → update y i z k = update y i z' k := by
  intro k hk; simp [hk]

/-- Step (a) of the contraction argument, for a single site `i`. -/
lemma abs_site_sub_le (hc : IsDobrushin S c) {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ M) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 ≤ Δ j) (hosc : OscBound g Δ)
    (i j : Fin n) {x y : Fin n → E} (hxy : ∀ k, k ≠ j → x k = y k) :
    |S.site i g x - S.site i g y| ≤ if i = j then 0 else Δ j + c i j * Δ i := by
  by_cases hij : i = j
  · subst hij
    simp [site_local g i hxy]
  · simp only [hij, ite_false]
    set ν := S.G i x with hν
    set ν' := S.G i y with hν'
    have hsplit : S.site i g x - S.site i g y
        = (∫ z, (g (update x i z) - g (update y i z)) ∂ν)
          + ((∫ z, g (update y i z) ∂ν) - ∫ z, g (update y i z) ∂ν') := by
      have h1 : Integrable (fun z => g (update x i z)) ν := integrable_section hg hb i x
      have h2 : Integrable (fun z => g (update y i z)) ν := by
        exact Integrable.of_bound (measurable_section g hg i y).aestronglyMeasurable M
          (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hb _)
      rw [integral_sub h1 h2]
      simp only [site]
      ring
    have hfirst : |∫ z, (g (update x i z) - g (update y i z)) ∂ν| ≤ Δ j := by
      have := norm_integral_le_of_norm_le_const (μ := ν)
        (f := fun z => g (update x i z) - g (update y i z)) (C := Δ j)
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact hosc j _ _ (update_agree hxy i z))
      simpa using this
    have hsecond : |(∫ z, g (update y i z) ∂ν) - ∫ z, g (update y i z) ∂ν'| ≤ c i j * Δ i :=
      abs_integral_sub_le_of_tv ν ν' (hΔ i)
        (fun A hA => hc.le i j hij x y hxy A hA) (measurable_section g hg i y)
        (fun z z' => hosc i _ _ (update_agree' y i z z'))
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add hfirst hsecond)

/-- Contraction of the oscillation vector by the random-scan operator. -/
lemma exists_osc_scan [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {M : ℝ} {g : (Fin n → E) → ℝ}
    (hg : Measurable g) (hb : ∀ x, |g x| ≤ M) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 ≤ Δ j)
    (hosc : OscBound g Δ) :
    ∃ Δ' : Fin n → ℝ, (∀ j, 0 ≤ Δ' j) ∧ OscBound (S.scan g) Δ' ∧
      ∑ j, Δ' j ≤ (1 - (1 - r) / n) * ∑ j, Δ j := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  let t : Fin n → Fin n → ℝ := fun i j => if i = j then 0 else Δ j + c i j * Δ i
  have ht0 : ∀ i j, 0 ≤ t i j := fun i j => by
    simp only [t]
    split_ifs
    · exact le_rfl
    · exact add_nonneg (hΔ j) (mul_nonneg (hc.nonneg i j) (hΔ i))
  refine ⟨fun j => (1 / (n : ℝ)) * ∑ i, t i j, fun j => ?_, ?_, ?_⟩
  · exact mul_nonneg (one_div_pos.mpr hn).le (Finset.sum_nonneg fun i _ => ht0 i j)
  · intro j x y hxy
    unfold scan
    rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (one_div_pos.mpr hn)]
    refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hn).le
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => abs_site_sub_le hc hg hb hΔ hosc i j hxy)
  · have hsum : ∀ i, ∑ j, t i j ≤ ∑ j, Δ j - (1 - r) * Δ i := by
      intro i
      have e1 : ∑ j, t i j = ∑ j ∈ Finset.univ.erase i, t i j :=
        (Finset.sum_erase _ (by simp [t])).symm
      have e2 : ∑ j ∈ Finset.univ.erase i, t i j
          = ∑ j ∈ Finset.univ.erase i, Δ j + (∑ j ∈ Finset.univ.erase i, c i j) * Δ i := by
        rw [Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j hj => ?_
        have : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
        simp [t, this]
      have e3 : ∑ j ∈ Finset.univ.erase i, Δ j = ∑ j, Δ j - Δ i :=
        Finset.sum_erase_eq_sub (Finset.mem_univ i)
      rw [e1, e2, e3]
      nlinarith [mul_le_mul_of_nonneg_right (hrow i) (hΔ i)]
    calc ∑ j, (1 / (n : ℝ)) * ∑ i, t i j = (1 / (n : ℝ)) * ∑ i, ∑ j, t i j := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ (1 / (n : ℝ)) * ∑ i : Fin n, (∑ j, Δ j - (1 - r) * Δ i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hsum i) (one_div_pos.mpr hn).le
      _ = (1 - (1 - r) / n) * ∑ j, Δ j := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp

/-- Telescoping: the oscillation of `g` is at most the sum of its coordinate oscillations. -/
lemma abs_sub_le_sum_of_osc {g : (Fin n → E) → ℝ} {Δ : Fin n → ℝ} (hosc : OscBound g Δ)
    (s : Finset (Fin n)) : ∀ x y : Fin n → E, (∀ k, k ∉ s → x k = y k) →
      |g x - g y| ≤ ∑ j ∈ s, Δ j := by
  induction s using Finset.induction_on with
  | empty =>
    intro x y h
    have : x = y := funext fun k => h k (by simp)
    simp [this]
  | insert a s ha ih =>
    intro x y h
    set z : Fin n → E := update x a (y a) with hz
    have h1 : |g x - g z| ≤ Δ a := hosc a x z (fun k hk => by simp [hz, hk])
    have h2 : |g z - g y| ≤ ∑ j ∈ s, Δ j := by
      refine ih z y fun k hk => ?_
      by_cases hka : k = a
      · subst hka; simp [hz]
      · have := h k (by simp [hka, hk])
        simp [hz, hka, this]
    rw [Finset.sum_insert ha]
    calc |g x - g y| = |(g x - g z) + (g z - g y)| := by ring_nf
      _ ≤ |g x - g z| + |g z - g y| := abs_add_le _ _
      _ ≤ Δ a + ∑ j ∈ s, Δ j := add_le_add h1 h2

/-- A function with oscillation bounds `Δ` stays within `∑ Δ` of its `P`-mean. -/
lemma abs_sub_integral_le {h : (Fin n → E) → ℝ} {M : ℝ} (hm : Measurable h)
    (hb : ∀ x, |h x| ≤ M) {Δ : Fin n → ℝ} (hosc : OscBound h Δ) (x : Fin n → E) :
    |h x - ∫ y, h y ∂S.P| ≤ ∑ j, Δ j := by
  have hint : Integrable h S.P := integrable_of_bdd hm hb
  have : h x - ∫ y, h y ∂S.P = ∫ y, (h x - h y) ∂S.P := by
    rw [integral_sub (integrable_const _) hint]
    simp
  rw [this]
  have := norm_integral_le_of_norm_le_const (μ := S.P) (f := fun y => h x - h y)
    (C := ∑ j, Δ j) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]
      exact abs_sub_le_sum_of_osc hosc Finset.univ x y (by simp))
  simpa using this

lemma rho_nonneg [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) : 0 ≤ 1 - (1 - r) / (n : ℝ) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hr : 0 ≤ r :=
    (Finset.sum_nonneg fun j _ => hc.nonneg ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ j).trans
      (hrow ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩)
  have h1 : (1 - r) / (n : ℝ) ≤ 1 := by
    rw [div_le_one hn]
    have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    linarith
  linarith

/-- Iterating the random-scan operator contracts the oscillation geometrically. -/
lemma osc_scan_iterate [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {M : ℝ} {g : (Fin n → E) → ℝ}
    (hg : Measurable g) (hb : ∀ x, |g x| ≤ M) {Δ : Fin n → ℝ} (hΔ : ∀ j, 0 ≤ Δ j)
    (hosc : OscBound g Δ) (k : ℕ) :
    Measurable (S.scan^[k] g) ∧ (∀ x, |S.scan^[k] g x| ≤ M) ∧
      ∃ Δ' : Fin n → ℝ, (∀ j, 0 ≤ Δ' j) ∧ OscBound (S.scan^[k] g) Δ' ∧
        ∑ j, Δ' j ≤ (1 - (1 - r) / n) ^ k * ∑ j, Δ j := by
  induction k with
  | zero => exact ⟨hg, hb, Δ, hΔ, hosc, by simp⟩
  | succ k ih =>
    obtain ⟨hm, hbk, Δk, hΔk, hoscK, hsum⟩ := ih
    obtain ⟨Δ', hΔ', hosc', hsum'⟩ := exists_osc_scan hc hrow hm hbk hΔk hoscK
    rw [Function.iterate_succ_apply']
    refine ⟨measurable_scan hm, fun x => abs_scan_le hbk x, Δ', hΔ', hosc', ?_⟩
    have hρ := rho_nonneg hc hrow
    calc ∑ j, Δ' j ≤ (1 - (1 - r) / n) * ∑ j, Δk j := hsum'
      _ ≤ (1 - (1 - r) / n) * ((1 - (1 - r) / n) ^ k * ∑ j, Δ j) :=
          mul_le_mul_of_nonneg_left hsum hρ
      _ = (1 - (1 - r) / n) ^ (k + 1) * ∑ j, Δ j := by ring

/-- The mean is preserved by the iterates of the random-scan operator. -/
lemma integral_scan_iterate [NeZero n] {M : ℝ} {g : (Fin n → E) → ℝ} (hg : Measurable g)
    (hb : ∀ x, |g x| ≤ M) (k : ℕ) :
    Measurable (S.scan^[k] g) ∧ (∀ x, |S.scan^[k] g x| ≤ M) ∧
      ∫ x, S.scan^[k] g x ∂S.P = ∫ x, g x ∂S.P := by
  induction k with
  | zero => exact ⟨hg, hb, rfl⟩
  | succ k ih =>
    obtain ⟨hm, hbk, hint⟩ := ih
    rw [Function.iterate_succ_apply']
    exact ⟨measurable_scan hm, fun x => abs_scan_le hbk x, by
      rw [integral_scan hm hbk, hint]⟩

/-- Geometric decay of the sup-norm distance of `P^k g` to the mean. -/
lemma abs_scan_iterate_sub_integral_le [NeZero n] (hc : IsDobrushin S c) {r : ℝ}
    (hrow : ∀ i, ∑ j ∈ Finset.univ.erase i, c i j ≤ r) {M : ℝ} {g : (Fin n → E) → ℝ}
    (hg : Measurable g) (hb : ∀ x, |g x| ≤ M) (k : ℕ) (x : Fin n → E) :
    |S.scan^[k] g x - ∫ y, g y ∂S.P| ≤ (1 - (1 - r) / n) ^ k * (n * (2 * M)) := by
  have hM : 0 ≤ M := by
    obtain ⟨x0⟩ := Measure.nonempty_of_neZero S.P
    exact (abs_nonneg _).trans (hb x0)
  have hosc : OscBound g (fun _ => 2 * M) := fun j x y _ => by
    calc |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
      _ ≤ M + M := add_le_add (hb x) (hb y)
      _ = 2 * M := by ring
  obtain ⟨hm, hbk, Δ', hΔ', hoscK, hsum⟩ := osc_scan_iterate hc hrow hg hb
    (fun _ => by positivity) hosc k
  obtain ⟨_, _, hint⟩ := integral_scan_iterate (S := S) hg hb k
  have := abs_sub_integral_le (S := S) hm hbk hoscK x
  rw [hint] at this
  refine this.trans (hsum.trans ?_)
  simp

end Core

end HRS.External
