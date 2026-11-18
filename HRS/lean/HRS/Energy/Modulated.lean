import HRS.Torus.Sobolev
import HRS.Kernel.Riesz
import HRS.Prob.Metrics
import HRS.Energy.StaticLimitAux
import HRS.Energy.StaticLimitGauss
import HRS.Energy.StaticLimitFourier
import HRS.Energy.StaticLimitBasic
import HRS.Energy.StaticLimitTiltedGauss
import HRS.Prob.HilbertCLT

/-!
# Modulated energy, modulated Gibbs preparations, canonical Gibbs ensemble, centerings

Source: HRS periodic main paper, Section 2.1 (source lines 433-470) and Section 2.3
(lines 905-920).

* `H:eq:modulated-energy` (437-443):
  `F_N^h(X_N, μ) = (2N²)⁻¹ ∑_{i≠j} h(x_i,x_j) - N⁻¹ ∑_i ∫ h(x_i,y) dμ(y) + ½ ∬ h dμ dμ`;
  "the deleted diagonal is the original particle diagonal; `F_N^c = -c/(2N)` for a
  constant kernel `c`".
* `H:eq:modulated-gibbs` (446-452):
  `Q_{N,β₀}(μ) = K_{N,β₀}(μ)⁻¹ e^{-β₀ N F_N(X_N,μ)} μ^{⊗N}`, `K = ∫ e^{-β₀ N F_N} dμ^{⊗N}`.
* Relative entropy is unnormalised: `H(f | Q) = ∫ log(df/dQ) df` if `f ≪ Q`, `∞` otherwise
  (lines 455-457).
* `H:eq:centerings` (461-466): `Fluc_N = μ_N - μ`, `η_N = √N Fluc_N`, `ζ_N = √N(μ_N - m_N)`,
  `m_N = E[μ_N]`; `H:eq:centering-decomposition` (468-470).
* `H:eq:canonical` (907-912): `dP_{N,β} = Z⁻¹ exp[-β(∑_i V(x_i) + N⁻¹ ∑_{i<j} g(x_i-x_j))] dX_N`.
* `H:eq:thermal-equation` (915-918): `ρ_β = e^{-β(V + g*ρ_β)} / ∫ e^{-β(V+g*ρ_β)}`.
* `H:eq:energy-completion` (548-553): `o_N = C₀ N^{s/d-1} + 1_{s=0} log N/(2dN)`.
* `δ_N` (lines 720-735): `N⁻¹` for `0 ≤ s < d/2`, `N⁻¹ log(eN)` at `s = d/2`,
  `N^{1-d/s}` for `d/2 < s < d`.

## Representation
* `modulatedEnergy h X μ` uses Bochner integrals (junk `0` for non-integrable terms;
  hypotheses supply integrability where needed, e.g. bounded densities with `s < d`).
* `relEntropy f Q := InformationTheory.klDiv f Q : ℝ≥0∞`; for probability measures Mathlib's
  `klDiv` is `∫ log(df/dQ) df` when `f ≪ Q` and the log-likelihood ratio is integrable,
  and `∞` otherwise, matching the source convention (see `docs/ISSUES.md` §E1 on the
  non-integrable `f ≪ Q` case).
* `firstMarginal P := P.map (fun X => X 0)`; for exchangeable laws this is `m_N` (line 467).
* `meanEmpirical P := E_P[μ_N]` is the mixture measure `∫ μ_N dP` (Mathlib `Measure.bind`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-- The modulated energy `F_N^h(X_N, μ)` of `H:eq:modulated-energy` (lines 437-443) for a
symmetric pair kernel `h`. -/
def modulatedEnergy (h : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)
    - (1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂μ
    + (1 / 2) * ∫ x, ∫ y, h x y ∂μ ∂μ

/-- `F_N = F_N^g` with `h(x,y) = g(x - y)` for the kernel `g`. -/
def modulatedEnergyKernel (g : Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  modulatedEnergy (fun x y => g (x - y)) X μ

/-- `F_N` for the periodic Riesz/log kernel with parameters `d, s`. -/
def rieszEnergy (d : ℕ) (s : ℝ) {N : ℕ} (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  modulatedEnergyKernel (periodicRiesz d s) X μ

/-- The normaliser `K_{N,β₀}(μ) = ∫ e^{-β₀ N F_N} dμ^{⊗N}` (line 450). -/
def gibbsNormalizer (g : Torus d → ℝ) (N : ℕ) (β₀ : ℝ) (μ : Measure (Torus d)) : ℝ :=
  ∫ X : Config d N, Real.exp (-β₀ * N * modulatedEnergyKernel g X μ) ∂(Measure.pi fun _ => μ)

/-- The modulated Gibbs preparation `Q_{N,β₀}(μ)` of `H:eq:modulated-gibbs` (lines 446-452).
At `β₀ = 0` this is `μ^{⊗N}`. -/
def modulatedGibbs (g : Torus d → ℝ) (N : ℕ) (β₀ : ℝ) (μ : Measure (Torus d)) :
    Measure (Config d N) :=
  (ENNReal.ofReal (gibbsNormalizer g N β₀ μ))⁻¹ •
    (Measure.pi fun _ => μ).withDensity
      fun X => ENNReal.ofReal (Real.exp (-β₀ * N * modulatedEnergyKernel g X μ))

/-- Unnormalised relative entropy `H(f | Q)` (lines 455-457), as Mathlib's `klDiv`. -/
def relEntropy {α : Type*} [MeasurableSpace α] (f Q : Measure α) : ℝ≥0∞ :=
  InformationTheory.klDiv f Q

open Classical in
/-- The first marginal `P^{(1)}` of a law on configurations (`0` if `N = 0`). -/
def firstMarginal (P : Measure (Config d N)) : Measure (Torus d) :=
  if h : 0 < N then P.map (fun X => X ⟨0, h⟩) else 0

/-- Exchangeability of a law on `𝕋^{dN}`. -/
def IsExchangeable (P : Measure (Config d N)) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), P.map (fun X => X ∘ σ) = P

/-- `m_N = E[μ_N]`, the mean empirical measure (line 466). -/
def meanEmpirical (P : Measure (Config d N)) : Measure (Torus d) :=
  P.bind empirical

/-- `Fluc_N = μ_N - μ` in `E_m` (line 463). -/
def flucE (m : ℝ) (X : Config d N) (μ : Measure (Torus d)) : NegSobolev d m :=
  NegSobolev.ofMeasureDiff m (empirical X) μ

/-- `η_N = √N (μ_N - μ)` in `E_m`. -/
def etaE (m : ℝ) (X : Config d N) (μ : Measure (Torus d)) : NegSobolev d m :=
  Real.sqrt N • flucE m X μ

/-- `ζ_N = √N (μ_N - m_N)` in `E_m`, with `m_N = E[μ_N]` the mean under the law `P`. -/
def zetaE (m : ℝ) (P : Measure (Config d N)) (X : Config d N) : NegSobolev d m :=
  Real.sqrt N • NegSobolev.ofMeasureDiff m (empirical X) (meanEmpirical P)

/-- The canonical Gibbs ensemble `P_{N,β}` of `H:eq:canonical` (lines 907-912), with
Hamiltonian `∑_i V(x_i) + N⁻¹ ∑_{i<j} g(x_i - x_j)`. -/
def canonicalHamiltonian (g : Torus d → ℝ) (V : Torus d → ℝ) (X : Config d N) : ℝ :=
  ∑ i, V (X i) + (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j)

def canonicalPartition (g V : Torus d → ℝ) (N : ℕ) (β : ℝ) : ℝ :=
  ∫ X : Config d N, Real.exp (-β * canonicalHamiltonian g V X)

def canonicalGibbs (g V : Torus d → ℝ) (N : ℕ) (β : ℝ) : Measure (Config d N) :=
  (ENNReal.ofReal (canonicalPartition g V N β))⁻¹ •
    (volume : Measure (Config d N)).withDensity
      fun X => ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V X))

/-- The thermal equation `H:eq:thermal-equation` (lines 915-918): `ρ` is a thermal
equilibrium density at inverse temperature `β` for potential `V`. -/
def IsThermalDensity (g V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) : Prop :=
  IsProbDensity ρ ∧
    ∀ x, ρ x = Real.exp (-β * (V x + convFun g ρ x)) /
      ∫ y, Real.exp (-β * (V y + convFun g ρ y))

/-- `o_N = C₀ N^{s/d - 1} + 1_{s=0} log N /(2dN)` (`H:eq:energy-completion`, line 551). -/
def oN (d : ℕ) (s : ℝ) (C₀ : ℝ) (N : ℕ) : ℝ :=
  C₀ * (N : ℝ) ^ (s / d - 1) + (if s = 0 then Real.log N / (2 * d * N) else 0)

/-- `δ_N` (source lines 720-735): `N⁻¹` (`s < d/2`), `N⁻¹ log(eN)` (`s = d/2`),
`N^{1-d/s}` (`s > d/2`). -/
def deltaN (d : ℕ) (s : ℝ) (N : ℕ) : ℝ :=
  if s < (d : ℝ) / 2 then (N : ℝ)⁻¹
  else if s = (d : ℝ) / 2 then (N : ℝ)⁻¹ * Real.log (Real.exp 1 * N)
  else (N : ℝ) ^ (1 - (d : ℝ) / s)

/-! ### Helper lemmas (work package ENER-01) -/

section Helpers

open ProbabilityTheory

variable {d N : ℕ}

def permMeasEquiv {ι α : Type*} [MeasurableSpace α] (σ : Equiv.Perm ι) : (ι → α) ≃ᵐ (ι → α) where
  toFun X := X ∘ σ
  invFun X := X ∘ σ.symm
  left_inv X := by funext i; simp
  right_inv X := by funext i; simp
  measurable_toFun := Measurable.of_eval fun i => measurable_pi_apply (σ i)
  measurable_invFun := Measurable.of_eval fun i => measurable_pi_apply (σ.symm i)

theorem permMeasEquiv_apply {ι α : Type*} [MeasurableSpace α] (σ : Equiv.Perm ι) (X : ι → α) :
    permMeasEquiv σ X = X ∘ σ := rfl

theorem piPremeasure_perm {ι α : Type*} [Fintype ι] [MeasurableSpace α] (μ : Measure α)
    (σ : Equiv.Perm ι) (t : Set (ι → α)) :
    piPremeasure (fun _ : ι => μ.toOuterMeasure) (permMeasEquiv σ ⁻¹' t) =
      piPremeasure (fun _ : ι => μ.toOuterMeasure) t := by
  unfold piPremeasure
  have : ∀ i, Function.eval i '' (permMeasEquiv σ ⁻¹' t) = Function.eval (σ.symm i) '' t := by
    intro i
    ext a
    simp only [Set.mem_image, Set.mem_preimage, Function.eval]
    constructor
    · rintro ⟨X, hX, rfl⟩
      refine ⟨X ∘ σ, hX, ?_⟩
      simp
    · rintro ⟨Y, hY, rfl⟩
      refine ⟨Y ∘ σ.symm, ?_, ?_⟩
      · simpa [permMeasEquiv_apply, Function.comp_def] using hY
      · simp
  simp_rw [this]
  exact Equiv.prod_comp σ.symm (fun i => μ.toOuterMeasure (Function.eval i '' t))

theorem outer_pi_perm_le {ι α : Type*} [Fintype ι] [MeasurableSpace α] (μ : Measure α)
    (σ : Equiv.Perm ι) (t : Set (ι → α)) :
    OuterMeasure.pi (fun _ : ι => μ.toOuterMeasure) (permMeasEquiv σ ⁻¹' t) ≤
      OuterMeasure.pi (fun _ : ι => μ.toOuterMeasure) t := by
  have h : OuterMeasure.map (permMeasEquiv σ) (OuterMeasure.pi (fun _ : ι => μ.toOuterMeasure)) ≤
      OuterMeasure.pi (fun _ : ι => μ.toOuterMeasure) := by
    unfold OuterMeasure.pi
    rw [OuterMeasure.le_boundedBy]
    intro s
    rw [OuterMeasure.map_apply]
    calc _ ≤ piPremeasure (fun _ : ι => μ.toOuterMeasure) (permMeasEquiv σ ⁻¹' s) :=
          OuterMeasure.boundedBy_le _
      _ = _ := piPremeasure_perm μ σ s
  exact h t

theorem pi_map_perm {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (σ : Equiv.Perm ι) :
    (Measure.pi fun _ : ι => μ).map (permMeasEquiv σ) = Measure.pi fun _ : ι => μ := by
  classical
  ext s hs
  rw [MeasurableEquiv.map_apply, Measure.pi_def, toMeasure_apply _ _ hs,
    toMeasure_apply _ _ ((permMeasEquiv σ).measurable hs)]
  refine le_antisymm (outer_pi_perm_le μ σ s) ?_
  have := outer_pi_perm_le μ σ.symm (permMeasEquiv σ ⁻¹' s)
  convert this using 2
  ext X
  simp [permMeasEquiv_apply, Function.comp_def]

theorem pi_perm_measurePreserving {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (σ : Equiv.Perm ι) :
    MeasurePreserving (permMeasEquiv σ) (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) :=
  ⟨(permMeasEquiv σ).measurable, pi_map_perm μ σ⟩

theorem modulatedEnergy_perm (h : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d))
    (σ : Equiv.Perm (Fin N)) : modulatedEnergy h (X ∘ σ) μ = modulatedEnergy h X μ := by
  unfold modulatedEnergy
  congr 2
  · congr 1
    rw [← Equiv.sum_comp σ (fun i => ∑ j ∈ Finset.univ.erase i, h (X i) (X j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Function.comp]
    refine Finset.sum_bij (fun j _ => σ j) (fun j hj => ?_) (fun a _ b _ hab => σ.injective hab)
      (fun j hj => ?_) (fun j _ => rfl)
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
      exact fun h => hj (σ.injective h)
    · refine ⟨σ.symm j, ?_, by simp⟩
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj ⊢
      intro h; apply hj; rw [← h]; simp
  · congr 1
    exact Equiv.sum_comp σ (fun i => ∫ y, h (X i) y ∂μ)

theorem map_withDensity_perm {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) (σ : Equiv.Perm ι) (f : (ι → α) → ℝ≥0∞)
    (hf : ∀ X, f (X ∘ σ) = f X) :
    ((Measure.pi fun _ : ι => μ).withDensity f).map (fun X => X ∘ σ) =
      (Measure.pi fun _ : ι => μ).withDensity f := by
  have hmp := pi_perm_measurePreserving μ σ
  have hm : Measurable (fun X : ι → α => X ∘ σ) := (permMeasEquiv σ).measurable
  ext s hs
  rw [Measure.map_apply hm hs, withDensity_apply _ (hm hs), withDensity_apply _ hs]
  have := hmp.setLIntegral_comp_preimage_emb (permMeasEquiv σ).measurableEmbedding f s
  simp only [permMeasEquiv_apply, hf] at this
  exact this

theorem measurable_empirical : Measurable (fun X : Config d N => empirical X) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have : ∀ X : Config d N, empirical X s = (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N, s.indicator 1 (X i) := by
    intro X
    simp [empirical, Measure.smul_apply, Finset.sum_apply, Measure.dirac_apply' _ hs]
  simp_rw [this]
  refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
  exact (measurable_one.indicator hs).comp (measurable_pi_apply i)

theorem meanEmpirical_apply (P : Measure (Config d N)) {s : Set (Torus d)} (hs : MeasurableSet s) :
    meanEmpirical P s = (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N, P {X | X i ∈ s} := by
  unfold meanEmpirical
  rw [Measure.bind_apply hs measurable_empirical.aemeasurable]
  have : ∀ X : Config d N, empirical X s = (N : ℝ≥0∞)⁻¹ * ∑ i : Fin N, s.indicator 1 (X i) := by
    intro X
    simp [empirical, Measure.smul_apply, Finset.sum_apply, Measure.dirac_apply' _ hs]
  simp_rw [this]
  have hmi : ∀ i : Fin N, Measurable (fun X : Config d N => s.indicator (1 : Torus d → ℝ≥0∞) (X i)) :=
    fun i => (measurable_one.indicator hs).comp (measurable_pi_apply i)
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hmi i),
    lintegral_finsetSum _ fun i _ => hmi i]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hms : MeasurableSet {X : Config d N | X i ∈ s} := (measurable_pi_apply i) hs
  have : ∫⁻ X, s.indicator 1 (X i) ∂P = ∫⁻ X, ({X : Config d N | X i ∈ s}).indicator 1 X ∂P := by
    congr 1
  rw [this, lintegral_indicator_one hms]

theorem sum_erase_eq_two_mul_sum_lt (a : Fin N → Fin N → ℝ)
    (ha : ∀ i j, a i j = a j i) :
    ∑ i, ∑ j ∈ Finset.univ.erase i, a i j =
      2 * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), a i j := by
  have split : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, a i j =
      ∑ j ∈ Finset.univ.filter (fun j => i < j), a i j +
        ∑ j ∈ Finset.univ.filter (fun j => j < i), a i j := by
    intro i
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_filter,
        true_and]
      constructor
      · intro h; exact (lt_or_gt_of_ne h).symm
      · rintro (h | h)
        · exact h.ne'
        · exact h.ne
    · rw [Finset.disjoint_left]
      intro j h1 h2
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      exact lt_asymm h1 h2
  simp_rw [split]
  rw [Finset.sum_add_distrib, two_mul]
  congr 1
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun j => Finset.univ.filter (fun i => j < i))]
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ha i j
  · intro i j
    simp

theorem withDensity_withDensity_nonmeas {α : Type*} [MeasurableSpace α] (ν : Measure α)
    {R : α → ℝ≥0∞} (hR : Measurable R) (hR' : ∀ x, R x < ∞) (f : α → ℝ≥0∞) :
    (ν.withDensity R).withDensity f = ν.withDensity (R * f) := by
  ext s hs
  rw [withDensity_apply _ hs, withDensity_apply _ hs,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable ν hR f hs
      (Filter.Eventually.of_forall fun x => hR' x)]

theorem sigmaFinite_withDensityReal (ρ : Torus d → ℝ) : SigmaFinite (withDensityReal ρ) := by
  unfold withDensityReal; infer_instance

theorem pi_withDensityReal_eq (ρ : Torus d → ℝ) (hρ : Measurable ρ) :
    Measure.pi (fun _ : Fin N => withDensityReal ρ) =
      (volume : Measure (Config d N)).withDensity (fun X => ∏ i, ENNReal.ofReal (ρ (X i))) := by
  have := sigmaFinite_withDensityReal ρ
  refine (Measure.pi_eq (μ := fun _ : Fin N => withDensityReal ρ) fun s hs => ?_)
  have hms : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hms, ← lintegral_indicator hms]
  have h1 : (Set.univ.pi s).indicator (fun X : Config d N => ∏ i, ENNReal.ofReal (ρ (X i))) =
      fun X => ∏ i, (s i).indicator (fun y => ENNReal.ofReal (ρ y)) (X i) := by
    funext X
    by_cases h : ∀ i, X i ∈ s i
    · rw [Set.indicator_of_mem (by simpa using h)]
      exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (h i) (fun y => ENNReal.ofReal (ρ y))).symm
    · push Not at h
      obtain ⟨i, hi⟩ := h
      rw [Set.indicator_of_notMem (by simpa using ⟨i, hi⟩)]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm
  rw [h1]
  have hmeas : ∀ i, Measurable ((s i).indicator (fun y => ENNReal.ofReal (ρ y))) :=
    fun i => (ENNReal.measurable_ofReal.comp hρ).indicator (hs i)
  have hind : iIndepFun (fun (i : Fin N) (X : Config d N) =>
      (s i).indicator (fun y => ENNReal.ofReal (ρ y)) (X i)) (volume : Measure (Config d N)) :=
    iIndepFun_pi (μ := fun _ : Fin N => (volume : Measure (Torus d)))
      (X := fun i => (s i).indicator (fun y => ENNReal.ofReal (ρ y))) fun i => (hmeas i).aemeasurable
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind
    (fun i => (hmeas i).comp (measurable_pi_apply i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : ∫⁻ X : Config d N, (s i).indicator (fun y => ENNReal.ofReal (ρ y)) (X i) =
      ∫⁻ y, (s i).indicator (fun y => ENNReal.ofReal (ρ y)) y ∂(volume : Measure (Torus d)) := by
    have := (measurePreserving_eval (fun _ : Fin N => (volume : Measure (Torus d))) i).lintegral_comp
      (hmeas i)
    exact this
  rw [h2, lintegral_indicator (hs i)]
  unfold withDensityReal
  rw [withDensity_apply _ (hs i)]

theorem integral_withDensityReal_eq (ρ : Torus d → ℝ) (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (f : Torus d → ℝ) : ∫ y, f y ∂(withDensityReal ρ) = ∫ y, ρ y * f y := by
  unfold withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul₀ (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ).aemeasurable
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 y)]

theorem energy_identity (g : Torus d → ℝ) (hg : ∀ x, g (-x) = g x) (ρ : Torus d → ℝ)
    (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (X : Config d N) :
    (N : ℝ) * modulatedEnergyKernel g X (withDensityReal ρ) =
      (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), g (X i - X j)
        - ∑ i, convFun g ρ (X i)
        + ((N : ℝ) / 2) * ∫ x, ∫ y, g (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
  unfold modulatedEnergyKernel modulatedEnergy
  have hsym : ∀ i j : Fin N, g (X i - X j) = g (X j - X i) := by
    intro i j
    rw [← hg (X i - X j)]; congr 1; abel
  rw [sum_erase_eq_two_mul_sum_lt (fun i j => g (X i - X j)) hsym]
  have hc : ∀ i, ∫ y, g (X i - y) ∂(withDensityReal ρ) = convFun g ρ (X i) := by
    intro i
    rw [integral_withDensityReal_eq ρ hρ hρ0]
    unfold convFun
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by simp [mul_comm])
  simp_rw [hc]
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0
    simp
  · have : (N : ℝ) ≠ 0 := by positivity
    field_simp

theorem pi_map_pair {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {i j : ι} (hij : i ≠ j) :
    (Measure.pi fun _ : ι => μ).map (fun X => (X i, X j)) = μ.prod μ := by
  have hind := (iIndepFun_pi (μ := fun _ : ι => μ) (X := fun _ => id)
    (fun _ => aemeasurable_id)).indepFun hij
  have hmi : Measurable (fun X : ι → α => X i) := measurable_pi_apply i
  have hmj : Measurable (fun X : ι → α => X j) := measurable_pi_apply j
  have h := (indepFun_iff_map_prod_eq_prod_map_map hmi.aemeasurable hmj.aemeasurable).1 hind
  have e1 : (Measure.pi fun _ : ι => μ).map (fun X => X i) = μ :=
    (measurePreserving_eval (fun _ : ι => μ) i).map_eq
  have e2 : (Measure.pi fun _ : ι => μ).map (fun X => X j) = μ :=
    (measurePreserving_eval (fun _ : ι => μ) j).map_eq
  rw [e1, e2] at h
  exact h

section Iid

variable {α : Type*} [MeasurableSpace α]

theorem integrable_pair_comp (μ : Measure α) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {i j : ι} (hij : i ≠ j) {H : α × α → ℝ} (hH : Integrable H (μ.prod μ)) :
    Integrable (fun X : ι → α => H (X i, X j)) (Measure.pi fun _ : ι => μ) := by
  have hm : Measurable (fun X : ι → α => (X i, X j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  rw [← pi_map_pair μ hij] at hH
  exact (integrable_map_measure hH.aestronglyMeasurable hm.aemeasurable).1 hH

theorem integral_pair_comp (μ : Measure α) [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
    {i j : ι} (hij : i ≠ j) {H : α × α → ℝ} (hH : Integrable H (μ.prod μ)) :
    ∫ X : ι → α, H (X i, X j) ∂(Measure.pi fun _ : ι => μ) = ∫ p, H p ∂(μ.prod μ) := by
  have hm : Measurable (fun X : ι → α => (X i, X j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  rw [← pi_map_pair μ hij] at hH ⊢
  rw [integral_map hm.aemeasurable hH.aestronglyMeasurable]

end Iid

theorem isProbabilityMeasure_meanEmpirical (P : Measure (Config d N)) [IsProbabilityMeasure P]
    (hN : 1 ≤ N) : IsProbabilityMeasure (meanEmpirical P) := by
  refine ⟨?_⟩
  unfold meanEmpirical
  rw [Measure.bind_apply MeasurableSet.univ measurable_empirical.aemeasurable]
  have : ∀ X : Config d N, empirical X Set.univ = 1 := fun X =>
    (empirical_isProbabilityMeasure hN X).measure_univ
  simp [this]

namespace NegSobolev

variable {m : ℝ}

theorem ofMeasureDiff_add (hm : (d : ℝ) < 2 * m) (a b c : Measure (Torus d))
    [IsFiniteMeasure a] [IsFiniteMeasure b] [IsFiniteMeasure c] :
    ofMeasureDiff m a c = ofMeasureDiff m a b + ofMeasureDiff m b c := by
  have hmem : ∀ x y : Measure (Torus d), IsFiniteMeasure x → IsFiniteMeasure y →
      Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) *
        (Torus.measureRealCoeff x k - Torus.measureRealCoeff y k)) 2 := by
    intro x y hx hy
    refine memℓp_of_bounded hm _ ⟨Real.sqrt 2 * (x Set.univ).toReal + Real.sqrt 2 * (y Set.univ).toReal, fun k => ?_⟩
    have h1 := abs_measureRealCoeff_le x k
    have h2 := abs_measureRealCoeff_le y k
    calc |Torus.measureRealCoeff x k - Torus.measureRealCoeff y k|
        ≤ |Torus.measureRealCoeff x k| + |Torus.measureRealCoeff y k| := abs_sub _ _
      _ ≤ _ := add_le_add h1 h2
  have key : ∀ k, coord (ofMeasureDiff m a c) k =
      coord (ofMeasureDiff m a b) k + coord (ofMeasureDiff m b c) k := by
    intro k
    unfold ofMeasureDiff
    rw [coord_ofSeq_of_mem _ (hmem a c inferInstance inferInstance),
      coord_ofSeq_of_mem _ (hmem a b inferInstance inferInstance),
      coord_ofSeq_of_mem _ (hmem b c inferInstance inferInstance)]
    ring
  show (ofMeasureDiff m a c : lp (fun _ : NonzeroLattice d => ℝ) 2) = _
  refine lp.ext (funext fun k => ?_)
  exact key k

end NegSobolev

end Helpers

section KernelFacts

open Set Complex
open scoped Real
open ProbabilityTheory TopologicalSpace

variable {d N : ℕ} {s : ℝ}


theorem theta_nonneg (x : Torus d) {u : ℝ} (hu : 0 < u) :
    0 ≤ ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x := by
  choose y hy1 hy2 using fun i => exists_rep (x i)
  have hxy : x = fun i => ((y i : ℝ) : UnitAddCircle) := funext hy2
  set S : Fin d → ℂ := fun i => ∑' n : ℤ, Complex.exp (2 * π * I * n * (y i) - u * (n:ℂ)^2) with hS
  set f : Fin d → ℤ → ℂ := fun i n => Complex.exp (2 * π * I * n * (y i) - u * (n:ℂ)^2) with hf
  have hfn : ∀ i, Summable fun m => ‖f i m‖ := by
    intro i
    refine (summable_exp_sq u hu).congr fun m => ?_
    simp only [hf]
    rw [Complex.norm_exp]
    congr 1
    rw [show ((m:ℂ)) = ((m:ℝ):ℂ) by simp]
    simp [pow_two, Complex.mul_re]
  obtain ⟨hsum, hhas⟩ := pi_hasSum d f hfn
  have hterm : ∀ k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x =
      (∏ i, f i (k i)).re := by
    intro k
    have h1 : ∏ i, f i (k i) = ((Real.exp (-u * Lattice.enorm k ^ 2) : ℝ) : ℂ) * Torus.mode k x := by
      rw [hxy, mode_eq_prod]
      have h2 : ∏ i, f i (k i) = (∏ i, Complex.exp (-((u:ℂ) * ((k i : ℤ):ℂ)^2))) *
          ∏ i, Complex.exp (2 * π * I * (k i : ℤ) * (y i : ℝ)) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        simp only [hf]
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [h2, ← Complex.exp_sum, Complex.ofReal_exp, enorm_sq]
      congr 2
      push_cast
      rw [neg_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [h1, Complex.re_ofReal_mul]
    rfl
  have hre : ∑' k : Lattice d, Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x =
      (∏ i, S i).re := by
    simp_rw [hterm]
    rw [← Complex.re_tsum hsum.of_norm, hhas.tsum_eq]
  rw [hre]
  have hS' : ∀ i, S i = ((Real.sqrt (π / u) * ∑' n : ℤ, Real.exp (-(π^2 * ((n:ℝ) - y i)^2 / u)) : ℝ) : ℂ) :=
    fun i => theta_eq u (y i) hu
  simp_rw [hS']
  rw [← Complex.ofReal_prod, Complex.ofReal_re]
  exact Finset.prod_nonneg fun i _ => mul_nonneg (Real.sqrt_nonneg _)
    (tsum_nonneg fun n => (Real.exp_pos _).le)


theorem psi_ge (x : Torus d) {u : ℝ} (hu : 0 < u) :
    -(Real.exp 1 * (1 + ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2))) * Real.exp (-u) ≤
      psiFn x u := by
  set G := ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) with hG
  have hG0 : 0 ≤ G := tsum_nonneg fun _ => (Real.exp_pos _).le
  have hθ := theta_nonneg x hu
  rw [psi_eq x hu] at hθ
  rcases le_total 1 u with h1 | h1
  · -- large u
    have hb : ∀ k : Lattice d, ‖if k = 0 then 0 else Real.exp (-u * Lattice.enorm k ^ 2) * Torus.cosMode k x‖
        ≤ Real.exp (-u) * Real.exp 1 * Real.exp (-1 * Lattice.enorm k ^ 2) := by
      intro k
      by_cases hk : k = 0
      · simp only [hk, ite_true, norm_zero]; positivity
      · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hm := one_le_enorm k hk
        calc Real.exp (-u * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
            ≤ Real.exp (-u * Lattice.enorm k ^ 2) * 1 := by gcongr; exact abs_cosMode_le k x
          _ = Real.exp (-u * Lattice.enorm k ^ 2) := mul_one _
          _ ≤ Real.exp (-u + 1 + -1 * Lattice.enorm k ^ 2) := by
              apply Real.exp_le_exp.mpr
              nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr (show (1:ℝ) ≤ Lattice.enorm k ^ 2 by nlinarith))]
          _ = _ := by rw [Real.exp_add, Real.exp_add]
    have hsum := ((summable_gauss_lattice d 1 one_pos).mul_left
      (Real.exp (-u) * Real.exp 1)).hasSum
    have h2 := tsum_of_norm_bounded hsum hb
    rw [tsum_mul_left, ← hG] at h2
    have h3 : |psiFn x u| ≤ Real.exp (-u) * Real.exp 1 * G := by
      rw [← Real.norm_eq_abs]; exact h2
    have h4 := (abs_le.mp h3).1
    have : Real.exp (-u) * Real.exp 1 * G ≤ Real.exp 1 * (1 + G) * Real.exp (-u) := by
      nlinarith [Real.exp_pos (-u), Real.exp_pos 1, mul_nonneg (Real.exp_pos (-u)).le (Real.exp_pos 1).le]
    nlinarith
  · -- small u : psi ≥ -1
    have h5 : 1 ≤ Real.exp 1 * Real.exp (-u) := by
      rw [← Real.exp_add]; apply Real.one_le_exp; linarith
    have : -(Real.exp 1 * (1 + G)) * Real.exp (-u) ≤ -1 := by
      nlinarith [mul_nonneg hG0 (mul_nonneg (Real.exp_pos 1).le (Real.exp_pos (-u)).le)]
    linarith


theorem heatRiesz_ge {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ∀ x : Torus d, x ≠ 0 → -B ≤ heatRiesz d s ε x := by
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set c : ℝ := Real.exp 1 * (1 + ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2)) with hc
  have hc0 : 0 ≤ c := by
    rw [hc]
    have : 0 ≤ ∑' k : Lattice d, Real.exp (-1 * Lattice.enorm k ^ 2) :=
      tsum_nonneg fun _ => (Real.exp_pos _).le
    positivity
  set A : ℝ := rieszConst d s * (2 * π) ^ (s - d) / Real.Gamma a with hA
  have hA0 : 0 ≤ A := by
    have := rieszConst_pos hd hs0 hsd
    have := Real.Gamma_pos_of_pos ha
    rw [hA]; positivity
  refine ⟨A * (c * Real.Gamma a), fun ε hε x hx => ?_⟩
  rw [heatRiesz_eq_integral hsd hε x]
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * psiFn x (t + ε)) (Ioi 0) := by
    obtain ⟨M, hM0, hM⟩ := psi_bound x hx
    have hcont := psi_continuousOn x
    have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (a - 1) * psiFn x (t + ε))
        (volume.restrict (Ioi 0)) := by
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      refine ContinuousOn.mul (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)) ?_
      refine hcont.comp (continuousOn_id.add continuousOn_const) fun t ht => ?_
      simp only [mem_Ioi] at ht ⊢
      linarith
    refine Integrable.mono' ((Real.GammaIntegral_convergent ha).const_mul M) hmeas ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun t ht => ?_)
    have ht' : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht' _)]
    have h1 := hM (t + ε) (by linarith)
    have h2 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    have h3 := Real.rpow_pos_of_pos ht' (a - 1)
    calc t ^ (a - 1) * |psiFn x (t + ε)| ≤ t ^ (a - 1) * (M * Real.exp (-t)) := by
          gcongr
          exact h1.trans (by gcongr)
      _ = _ := by ring
  have hG : IntegrableOn (fun t : ℝ => Real.exp (-t) * t ^ (a - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent ha
  have hlow : -(c * Real.Gamma a) ≤ ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x (t + ε) := by
    have h1 : ∫ t in Ioi (0:ℝ), -(c * (Real.exp (-t) * t ^ (a - 1))) = -(c * Real.Gamma a) := by
      rw [integral_neg, integral_const_mul, Real.Gamma_eq_integral ha]
    rw [← h1]
    refine setIntegral_mono_on (hG.const_mul c).neg hint measurableSet_Ioi ?_
    intro t ht
    have ht' : 0 < t := ht
    have h2 := psi_ge x (show 0 < t + ε by linarith)
    have h3 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    have h4 := Real.rpow_pos_of_pos ht' (a - 1)
    have h5 : -(c * Real.exp (-t)) ≤ psiFn x (t + ε) := by
      refine le_trans ?_ h2
      rw [neg_mul, neg_le_neg_iff, ← hc]
      exact mul_le_mul_of_nonneg_left h3 hc0
    calc -(c * (Real.exp (-t) * t ^ (a - 1))) = t ^ (a - 1) * (-(c * Real.exp (-t))) := by ring
      _ ≤ t ^ (a - 1) * psiFn x (t + ε) := by gcongr
  have : -(A * (c * Real.Gamma a)) ≤ A * ∫ t in Ioi (0:ℝ), t ^ (a - 1) * psiFn x (t + ε) := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left hlow hA0
  exact this

theorem periodicRiesz_ge {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ B : ℝ, ∀ x : Torus d, -B ≤ periodicRiesz d s x := by
  obtain ⟨B0, hB0⟩ := heatRiesz_ge (d := d) hd hs0 hsd
  refine ⟨|B0| + |periodicRiesz d s 0|, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    have := neg_abs_le (periodicRiesz d s 0)
    have := abs_nonneg B0
    linarith
  · have h := ge_of_tendsto (periodicRiesz_tendsto hd hs0 hsd x hx)
      (Filter.eventually_of_mem (self_mem_nhdsWithin) fun ε hε => hB0 ε hε x hx)
    have := le_abs_self B0
    have := abs_nonneg (periodicRiesz d s 0)
    linarith



theorem volume_singleton_circle (x : UnitAddCircle) : (volume : Measure UnitAddCircle) {x} = 0 := by
  have hle : ∀ δ : ℝ, 0 < δ → (volume : Measure UnitAddCircle) {x} ≤ ENNReal.ofReal (2 * δ) := by
    intro δ hδ
    calc (volume : Measure UnitAddCircle) {x} ≤ volume (Metric.closedBall x δ) :=
          measure_mono (by simp [Metric.mem_closedBall, hδ.le])
      _ = ENNReal.ofReal (min 1 (2 * δ)) := by
          rw [AddCircle.volume_closedBall]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (min_le_right _ _)
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  calc (volume : Measure UnitAddCircle) {x} ≤ ENNReal.ofReal (2 * ((ε : ℝ) / 2)) :=
        hle _ (by positivity)
    _ = ε := by
        rw [show 2 * ((ε : ℝ) / 2) = ε by ring]
        exact ENNReal.ofReal_coe_nnreal
    _ = 0 + ε := by simp

theorem volume_singleton_torus (hd : 1 ≤ d) (x : Torus d) : (volume : Measure (Torus d)) {x} = 0 := by
  have : NullSingletonClass (volume : Measure UnitAddCircle) := ⟨fun y => volume_singleton_circle y⟩
  have h2 := MeasureTheory.Measure.pi_nullSingletonClass (μ := fun _ : Fin d => (volume : Measure UnitAddCircle)) (⟨0, hd⟩ : Fin d)
  exact measure_singleton (μ := Measure.pi fun _ : Fin d => (volume : Measure UnitAddCircle)) x



theorem continuous_heatRiesz (hsd : s < d) (ε : ℝ) (hε : 0 < ε) :
    Continuous (heatRiesz d s ε) := by
  unfold heatRiesz
  refine continuous_tsum (u := fun k : Lattice d => |rieszConst d s| * Real.exp (-ε * Lattice.enorm k ^ 2))
    (fun k => ?_) ((summable_gauss_lattice d ε hε).mul_left |rieszConst d s|) (fun k x => ?_)
  · exact (continuous_const.mul (Torus.continuous_cosMode k))
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hc := abs_cosMode_le k x
    have hexp := (Real.exp_pos (-ε * Lattice.enorm k ^ 2)).le
    have hcoef : |rieszCoeff d s k| ≤ |rieszConst d s| := by
      unfold rieszCoeff
      by_cases hk : k = 0
      · simp [hk]
      · simp only [hk, ite_false]; rw [abs_mul]
        have h1 := one_le_enorm k hk
        have hb : (2 * Real.pi * Lattice.enorm k) ^ (s - (d:ℝ)) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three]) (by linarith)
        have hp : 0 ≤ (2 * Real.pi * Lattice.enorm k) ^ (s - (d:ℝ)) :=
          Real.rpow_nonneg (by positivity) _
        rw [abs_of_nonneg hp]
        nlinarith [abs_nonneg (rieszConst d s)]
    calc |rieszCoeff d s k| * Real.exp (-ε * Lattice.enorm k ^ 2) * |Torus.cosMode k x|
        ≤ |rieszConst d s| * Real.exp (-ε * Lattice.enorm k ^ 2) * 1 := by gcongr
      _ = _ := by ring

theorem aemeasurable_periodicRiesz (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    AEMeasurable (periodicRiesz d s) (volume : Measure (Torus d)) := by
  let εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεn : Tendsto εn atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
    exact Filter.Eventually.of_forall fun n => by simp only [εn, Set.mem_Ioi]; positivity
  refine aemeasurable_of_tendsto_metrizable_ae atTop (f := fun n => heatRiesz d s (εn n))
    (fun n => (continuous_heatRiesz hsd _ (by simp only [εn]; positivity)).measurable.aemeasurable) ?_
  have hne : ∀ᵐ x ∂(volume : Measure (Torus d)), x ≠ 0 := by
    rw [ae_iff]
    simpa using volume_singleton_torus (by omega) 0
  filter_upwards [hne] with x hx
  exact (periodicRiesz_tendsto hd hs0 hsd x hx).comp hεn



theorem measurePreserving_sub_coord {i j : Fin N} (hij : i ≠ j) :
    MeasurePreserving (fun X : Config d N => X i - X j) volume (volume : Measure (Torus d)) := by
  have h1 : MeasurePreserving (fun X : Config d N => (X i, X j)) volume
      ((volume : Measure (Torus d)).prod volume) :=
    ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j),
      pi_map_pair (volume : Measure (Torus d)) hij⟩
  have h2 : MeasurePreserving (fun z : Torus d × Torus d => z.1 - z.2)
      ((volume : Measure (Torus d)).prod volume) volume :=
    (measurePreserving_fst (μ := (volume : Measure (Torus d))) (ν := (volume : Measure (Torus d)))).comp
      (measurePreserving_sub_prod (volume : Measure (Torus d)) (volume : Measure (Torus d)))
  exact h2.comp h1

theorem integrable_exp_canonical (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun X : Config d N =>
      Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) (fun _ => c) X)) := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hB' : ∀ x, -(max B 0) ≤ periodicRiesz d s x := fun x => (neg_le_neg (le_max_left _ _)).trans (hB x)
  set B' := max B 0 with hB'def
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hgm := aemeasurable_periodicRiesz (d := d) hd hs0 hsd
  have hmeas : AEMeasurable (fun X : Config d N =>
      canonicalHamiltonian (periodicRiesz d s) (fun _ => c) X) volume := by
    unfold canonicalHamiltonian
    have hsum : AEMeasurable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        periodicRiesz d s (X i - X j)) volume := by
      refine Finset.aemeasurable_fun_sum (f := fun (i : Fin N) (X : Config d N) =>
        ∑ j ∈ Finset.univ.filter (fun j => i < j), periodicRiesz d s (X i - X j)) _ fun i _ => ?_
      refine Finset.aemeasurable_fun_sum (f := fun (j : Fin N) (X : Config d N) =>
        periodicRiesz d s (X i - X j)) _ fun j hj => ?_
      have hij : i ≠ j := (Finset.mem_filter.mp hj).2.ne
      exact AEMeasurable.comp_quasiMeasurePreserving (g := periodicRiesz d s)
        (f := fun X : Config d N => X i - X j) hgm (measurePreserving_sub_coord hij).quasiMeasurePreserving
    exact AEMeasurable.add aemeasurable_const (hsum.const_mul (1 / (N : ℝ)))
  have hlow : ∀ X : Config d N,
      (N : ℝ) * c - N * B' ≤ canonicalHamiltonian (periodicRiesz d s) (fun _ => c) X := by
    intro X
    unfold canonicalHamiltonian
    have h1 : ∑ i : Fin N, c = N * c := by simp
    rw [h1]
    have h2 : -((N : ℝ) * N * B') ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        periodicRiesz d s (X i - X j) := by
      have : ∀ i : Fin N, -((N : ℝ) * B') ≤ ∑ j ∈ Finset.univ.filter (fun j => i < j),
          periodicRiesz d s (X i - X j) := by
        intro i
        calc -((N : ℝ) * B') ≤ -(((Finset.univ.filter (fun j => i < j)).card : ℝ) * B') := by
              have : ((Finset.univ.filter (fun j => i < j)).card : ℝ) ≤ N := by
                have := Finset.card_filter_le (Finset.univ : Finset (Fin N)) (fun j => i < j)
                simpa using (Nat.cast_le (α := ℝ)).mpr this
              nlinarith
          _ = ∑ j ∈ Finset.univ.filter (fun j => i < j), (-B') := by simp
          _ ≤ _ := Finset.sum_le_sum fun j _ => hB' _
      calc -((N : ℝ) * N * B') = ∑ i : Fin N, -((N : ℝ) * B') := by simp; ring
        _ ≤ _ := Finset.sum_le_sum fun i _ => this i
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    · have hN : (0 : ℝ) < N := by exact_mod_cast h0
      have : -((N : ℝ) * B') ≤ (1 / (N : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
          periodicRiesz d s (X i - X j) := by
        calc -((N : ℝ) * B') = (1 / (N : ℝ)) * (-((N : ℝ) * N * B')) := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
  set K : ℝ := Real.exp (β * ((N : ℝ) * B' - N * c)) with hK
  refine Integrable.mono' (integrable_const K) ?_ (Filter.Eventually.of_forall fun X => ?_)
  · exact (Real.measurable_exp.comp_aemeasurable (hmeas.const_mul (-β))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hK]
    apply Real.exp_le_exp.mpr
    have := hlow X
    nlinarith



theorem eq_volume_of_addLeftInvariant (ν : Measure (Torus d)) [IsFiniteMeasure ν]
    [ν.IsAddLeftInvariant] (h : ν Set.univ = 1) : ν = volume := by
  let K : PositiveCompacts (Torus d) := ⊤
  have hK : (K : Set (Torus d)) = Set.univ := rfl
  have h1 := Measure.addHaarMeasure_unique ν K
  have h2 := Measure.addHaarMeasure_unique (volume : Measure (Torus d)) K
  rw [hK, h] at h1
  rw [hK, measure_univ] at h2
  rw [h1, h2]

theorem map_withDensity_of_measurePreserving {α : Type*} [MeasurableSpace α] (e : α ≃ᵐ α)
    (ν : Measure α) (he : MeasurePreserving e ν ν) (f : α → ℝ≥0∞) (hf : ∀ x, f (e x) = f x) :
    (ν.withDensity f).map e = ν.withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  have := he.setLIntegral_comp_preimage_emb e.measurableEmbedding f s
  simp only [hf] at this
  exact this

/-- Simultaneous translation of all particles as a measurable equivalence. -/
def shiftEquiv (t : Torus d) : Config d N ≃ᵐ Config d N where
  toFun X := fun i => t + X i
  invFun X := fun i => -t + X i
  left_inv X := by funext i; simp
  right_inv X := by funext i; simp
  measurable_toFun := Measurable.of_eval fun i => measurable_const.add (measurable_pi_apply i)
  measurable_invFun := Measurable.of_eval fun i => measurable_const.add (measurable_pi_apply i)

theorem shiftEquiv_apply (t : Torus d) (X : Config d N) (i : Fin N) : shiftEquiv t X i = t + X i := rfl

theorem shiftEquiv_measurePreserving (t : Torus d) :
    MeasurePreserving (shiftEquiv t : Config d N ≃ᵐ Config d N) volume volume := by
  have := measurePreserving_pi (fun _ : Fin N => (volume : Measure (Torus d)))
    (fun _ : Fin N => (volume : Measure (Torus d))) (f := fun _ => fun x : Torus d => t + x)
    (fun _ => measurePreserving_add_left volume t)
  exact this

theorem canonicalHamiltonian_shift (g : Torus d → ℝ) (c : ℝ) (t : Torus d) (X : Config d N) :
    canonicalHamiltonian g (fun _ => c) (shiftEquiv t X) = canonicalHamiltonian g (fun _ => c) X := by
  unfold canonicalHamiltonian
  simp only [shiftEquiv_apply, add_sub_add_left_eq_sub]


end KernelFacts

/-! ### Elementary identities (work package ENER-01) -/

section Identities

variable (hN : 2 ≤ N)

/-- `F_N^c = -c/(2N)` for a constant kernel (line 444). -/
theorem modulatedEnergy_const (c : ℝ) (X : Config d N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (hN : 1 ≤ N) :
    modulatedEnergy (fun _ _ => c) X μ = -c / (2 * N) := by
  unfold modulatedEnergy
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, c = ((N : ℝ) - 1) * c := by
    intro i
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub hN]; simp
  have hμ : μ.real Set.univ = 1 := by simp [Measure.real]
  simp only [h1, integral_const, hμ, smul_eq_mul, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- `P_{N,β} = Q_{N,β}(μ_β)` for the thermal equilibrium measure, "including its original
diagonal" (lines 919-920). -/
theorem canonicalGibbs_eq_modulatedGibbs (g V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity g V β ρ) (hg : ∀ x, g (-x) = g x)
    (hint : ∀ x, Integrable (fun y => g (x - y)) (withDensityReal ρ)) :
    canonicalGibbs g V N β = modulatedGibbs g N β (withDensityReal ρ) := by
  obtain ⟨hprob, hth⟩ := hρ
  have hρm := hprob.measurable
  have hρ0 := hprob.nonneg
  set Zr : ℝ := ∫ y, Real.exp (-β * (V y + convFun g ρ y)) with hZr
  have hZr_nonneg : 0 ≤ Zr := by
    by_contra hneg
    push Not at hneg
    have h := hth 0
    have h2 : ρ 0 < 0 := by
      rw [h]; exact div_neg_of_pos_of_neg (Real.exp_pos _) hneg
    exact absurd (hρ0 0) (not_le.mpr h2)
  have hZr_pos : 0 < Zr := by
    rcases hZr_nonneg.eq_or_lt with h0 | h0
    · exfalso
      have : ∀ x, ρ x = 0 := fun x => by rw [hth x, ← h0, div_zero]
      have h1 := hprob.integral_one
      simp [this] at h1
    · exact h0
  set J : ℝ := ∫ x, ∫ y, g (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hJ
  set c : ℝ := Real.exp (-β * (((N : ℝ) / 2) * J)) / Zr ^ N with hc
  have hc_pos : 0 < c := by positivity
  have key : ∀ X : Config d N, (∏ i, ρ (X i)) *
      Real.exp (-β * N * modulatedEnergyKernel g X (withDensityReal ρ)) =
      c * Real.exp (-β * canonicalHamiltonian g V X) := by
    intro X
    have hI := energy_identity g hg ρ hρm hρ0 X
    have h1 : ∏ i, ρ (X i) = Real.exp (∑ i, (-β * (V (X i) + convFun g ρ (X i)))) / Zr ^ N := by
      simp_rw [hth]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Real.exp_sum]
    rw [h1, hc, div_mul_eq_mul_div, div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add]
    congr 2
    unfold canonicalHamiltonian
    have e1 : -β * (N : ℝ) * modulatedEnergyKernel g X (withDensityReal ρ) =
        -β * ((N : ℝ) * modulatedEnergyKernel g X (withDensityReal ρ)) := by ring
    have hs : ∑ i, (-β * (V (X i) + convFun g ρ (X i))) =
        -β * (∑ i, V (X i)) + -β * (∑ i, convFun g ρ (X i)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, mul_add]
    rw [← hJ] at hI
    rw [hs, e1, hI]
    ring
  -- measure part
  set R : Config d N → ℝ≥0∞ := fun X => ∏ i, ENNReal.ofReal (ρ (X i)) with hR
  have hRm : Measurable R := Finset.measurable_prod _ fun i _ =>
    ENNReal.measurable_ofReal.comp (hρm.comp (measurable_pi_apply i))
  have hRlt : ∀ X, R X < ∞ := fun X => ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top
  have hRreal : ∀ X, (R X).toReal = ∏ i, ρ (X i) := by
    intro X
    rw [hR, ENNReal.toReal_prod]
    exact Finset.prod_congr rfl fun i _ => ENNReal.toReal_ofReal (hρ0 _)
  have hRofReal : ∀ X, R X = ENNReal.ofReal (∏ i, ρ (X i)) := by
    intro X
    rw [hR, ENNReal.ofReal_prod_of_nonneg fun i _ => hρ0 _]
  have hpi : Measure.pi (fun _ : Fin N => withDensityReal ρ) = (volume : Measure (Config d N)).withDensity R :=
    pi_withDensityReal_eq ρ hρm
  -- the normaliser
  have hK : gibbsNormalizer g N β (withDensityReal ρ) = c * canonicalPartition g V N β := by
    unfold gibbsNormalizer canonicalPartition
    rw [hpi, integral_withDensity_eq_integral_toReal_smul₀ hRm.aemeasurable
      (Filter.Eventually.of_forall hRlt), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [smul_eq_mul, hRreal]
    exact key X
  have hdens : (volume : Measure (Config d N)).withDensity (R * fun X =>
      ENNReal.ofReal (Real.exp (-β * N * modulatedEnergyKernel g X (withDensityReal ρ)))) =
      ENNReal.ofReal c • (volume : Measure (Config d N)).withDensity
        (fun X => ENNReal.ofReal (Real.exp (-β * canonicalHamiltonian g V X))) := by
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext X
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hRofReal, ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hρ0 _), key X,
      ENNReal.ofReal_mul hc_pos.le]
  unfold canonicalGibbs modulatedGibbs
  rw [hK, hpi, withDensity_withDensity_nonmeas _ hRm hRlt, hdens, smul_smul,
    ENNReal.ofReal_mul hc_pos.le]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (by simpa using hc_pos)) (Or.inl ENNReal.ofReal_ne_top),
    mul_comm (ENNReal.ofReal c)⁻¹, mul_assoc, ENNReal.inv_mul_cancel (by simpa using hc_pos)
    ENNReal.ofReal_ne_top, mul_one]

/-- `Q_{N,0}(μ) = μ^{⊗N}` (line 453). -/
theorem modulatedGibbs_zero (g : Torus d → ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    modulatedGibbs g N 0 μ = Measure.pi fun _ : Fin N => μ := by
  unfold modulatedGibbs gibbsNormalizer
  simp

/-- `Q_{N,β₀}(μ)` is a probability measure when the normaliser is finite and positive. -/
theorem modulatedGibbs_isProbabilityMeasure (g : Torus d → ℝ) (β₀ : ℝ) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (hK : 0 < gibbsNormalizer g N β₀ μ)
    (hint : Integrable (fun X : Config d N => Real.exp (-β₀ * N * modulatedEnergyKernel g X μ))
      (Measure.pi fun _ => μ)) :
    IsProbabilityMeasure (modulatedGibbs g N β₀ μ) := by
  refine ⟨?_⟩
  unfold modulatedGibbs
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  have := ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)
  unfold gibbsNormalizer at hK ⊢
  rw [← this]
  exact ENNReal.inv_mul_cancel (by simpa using hK) ENNReal.ofReal_ne_top

/-- The centering decomposition `η_N = ζ_N + √N(m_N - μ)` (`H:eq:centering-decomposition`,
lines 468-470), in `E_m` for `2m > d`. -/
theorem eta_eq_zeta_add (m : ℝ) (hm : (d : ℝ) < 2 * m) (P : Measure (Config d N))
    [IsProbabilityMeasure P] (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (X : Config d N)
    (hN : 1 ≤ N) :
    etaE m X μ = zetaE m P X + Real.sqrt N • NegSobolev.ofMeasureDiff m (meanEmpirical P) μ := by
  haveI := empirical_isProbabilityMeasure hN X
  haveI := isProbabilityMeasure_meanEmpirical P hN
  unfold etaE flucE zetaE
  rw [NegSobolev.ofMeasureDiff_add hm (empirical X) (meanEmpirical P) μ, smul_add]

/-- For exchangeable laws `m_N` is the first marginal (line 467). -/
theorem meanEmpirical_eq_firstMarginal (P : Measure (Config d N)) [IsProbabilityMeasure P]
    (hP : IsExchangeable P) (hN : 1 ≤ N) :
    meanEmpirical P = firstMarginal P := by
  have h0 : 0 < N := hN
  unfold firstMarginal
  rw [dif_pos h0]
  ext s hs
  rw [meanEmpirical_apply P hs, Measure.map_apply (measurable_pi_apply (⟨0, h0⟩ : Fin N)) hs]
  have : ∀ i : Fin N, P {X | X i ∈ s} = P {X | X ⟨0, h0⟩ ∈ s} := by
    intro i
    have h := hP (Equiv.swap ⟨0, h0⟩ i)
    have hm : Measurable (fun X : Config d N => X ∘ (Equiv.swap (⟨0, h0⟩ : Fin N) i)) :=
      (permMeasEquiv _).measurable
    have := congrArg (fun Q => Q {X : Config d N | X ⟨0, h0⟩ ∈ s}) h
    have hs0 : MeasurableSet {X : Config d N | X ⟨0, h0⟩ ∈ s} := (measurable_pi_apply (⟨0, h0⟩ : Fin N)) hs
    rw [Measure.map_apply hm hs0] at this
    simpa [Set.preimage, Function.comp_def] using this
  simp_rw [this]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel (by exact_mod_cast h0.ne') (ENNReal.natCast_ne_top N), one_mul]
  rfl

/-- The modulated Gibbs law is exchangeable (the energy is symmetric). -/
theorem modulatedGibbs_isExchangeable (g : Torus d → ℝ) (β₀ : ℝ) (μ : Measure (Torus d))
    (hg : ∀ x, g (-x) = g x) :
    IsExchangeable (modulatedGibbs g N β₀ μ) := by
  intro σ
  unfold modulatedGibbs
  rw [Measure.map_smul]
  congr 1
  refine map_withDensity_perm μ σ _ ?_
  intro X
  simp only [modulatedEnergyKernel, modulatedEnergy_perm]
  exact (permMeasEquiv σ).measurable.aemeasurable

/-- Lemma A.35(i) `M:B:lem:initial-energy`, first display (lines 11498-11505): for i.i.d.
data `X_N^0 ∼ (μ°)^{⊗N}`, `E[F_N(X_N^0, μ°)] = -(2N)⁻¹ ∬ g d(μ°)^{⊗2}`. -/
theorem expectation_modulatedEnergy_iid (g : Torus d → ℝ) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (hN : 1 ≤ N)
    (hint : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    (hint1 : ∀ x, Integrable (fun y => g (x - y)) μ) :
    ∫ X, modulatedEnergyKernel g X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / (2 * N)) * ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) := by
  set G := ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂(μ.prod μ) with hG
  have hN' : (N : ℝ) ≠ 0 := by positivity
  -- the three pieces
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => g (X i - X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => g (p.1 - p.2)) hint
  have hpair' : ∀ i j : Fin N, i ≠ j →
      ∫ X : Config d N, g (X i - X j) ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i j hij => integral_pair_comp μ hij (H := fun p => g (p.1 - p.2)) hint
  have hconv_int : Integrable (fun x => ∫ y, g (x - y) ∂μ) μ := hint.integral_prod_left
  have hconv_mean : ∫ x, ∫ y, g (x - y) ∂μ ∂μ = G := by
    rw [hG, integral_prod _ hint]
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i => by
    have := integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
    exact this
  have h1' : ∀ i : Fin N, ∫ X : Config d N, ∫ y, g (X i - y) ∂μ ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i => by
      have := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int.aestronglyMeasurable
      exact this.trans hconv_mean
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, g (X i - y) ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  have E1 : ∫ X : Config d N, ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
      ∂(Measure.pi fun _ : Fin N => μ) = (N : ℝ) * ((N : ℝ) - 1) * G := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm]
    have : ∀ i : Fin N, ∫ X : Config d N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
        ∂(Measure.pi fun _ : Fin N => μ) = ((N : ℝ) - 1) * G := by
      intro i
      rw [integral_finsetSum _ fun j hj => hpair i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_congr rfl fun j hj => hpair' i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hN]; simp
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have E2 : ∫ X : Config d N, ∑ i, ∫ y, g (X i - y) ∂μ ∂(Measure.pi fun _ : Fin N => μ) = N * G := by
    rw [integral_finsetSum _ fun i _ => h1 i]
    simp_rw [h1']
    simp
  unfold modulatedEnergyKernel modulatedEnergy
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, E1, E2, integral_const]
  · have hμ : (Measure.pi fun _ : Fin N => μ).real Set.univ = 1 := by simp [Measure.real]
    rw [hμ, one_smul]
    have : ∫ x, ∫ y, (fun x y => g (x - y)) x y ∂μ ∂μ = G := hconv_mean
    rw [this]
    field_simp
    ring
  all_goals first
    | exact (hT1.const_mul _)
    | exact (hT2.const_mul _)
    | exact ((hT1.const_mul _).sub (hT2.const_mul _))
    | exact integrable_const _

end Identities

/-! ### Second moment: auxiliary Hoeffding-decomposition development (work package ENER-01)

The lemmas below prove Lemma C.8 (`second_moment_modulatedEnergy_iid`) by the Hoeffding
decomposition of the V-statistic. -/

namespace SecondMomentAux
section SecondMoment
open ProbabilityTheory
variable {d N : ℕ}

theorem sq_integral_le_integral_sq {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {f : α → ℝ} (hf : MemLp f 2 ν) :
    (∫ x, f x ∂ν) ^ 2 ≤ ∫ x, f x ^ 2 ∂ν := by
  have h := variance_nonneg f ν
  rw [variance_eq_sub hf] at h
  simp only [Pi.pow_apply] at h
  linarith

variable (g : Torus d → ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]

/-- `W(p) = g(p.1 - p.2)` -/
theorem W_memLp (hmeas : AEStronglyMeasurable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    (hint2 : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2) ^ 2) (μ.prod μ)) :
    MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ) :=
  (memLp_two_iff_integrable_sq hmeas).mpr hint2

theorem h_integrable (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) :
    Integrable (convMeasure g μ) μ :=
  (hW.integrable one_le_two).integral_prod_left

theorem h_memLp_sq_le (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) :
    MemLp (convMeasure g μ) 2 μ ∧
      ∫ x, convMeasure g μ x ^ 2 ∂μ ≤ ∫ p : Torus d × Torus d, g (p.1 - p.2) ^ 2 ∂μ.prod μ := by
  have hsq : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2) ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hW.aestronglyMeasurable).mp hW
  have hae1 : ∀ᵐ x ∂μ, Integrable (fun y => g (x - y) ^ 2) μ := hsq.prod_right_ae
  have hae2 : ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => g (x - y)) μ := hW.aestronglyMeasurable.prodMk_left
  have hbound : ∀ᵐ x ∂μ, convMeasure g μ x ^ 2 ≤ ∫ y, g (x - y) ^ 2 ∂μ := by
    filter_upwards [hae1, hae2] with x h1 h2
    have hm : MemLp (fun y => g (x - y)) 2 μ := (memLp_two_iff_integrable_sq h2).mpr h1
    exact sq_integral_le_integral_sq μ hm
  have hI : Integrable (fun x => ∫ y, g (x - y) ^ 2 ∂μ) μ := hsq.integral_prod_left
  have hmeas_h : AEStronglyMeasurable (convMeasure g μ) μ := (h_integrable g μ hW).aestronglyMeasurable
  have hint : Integrable (fun x => convMeasure g μ x ^ 2) μ := by
    refine Integrable.mono' hI (hmeas_h.pow 2) ?_
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  refine ⟨(memLp_two_iff_integrable_sq hmeas_h).mpr hint, ?_⟩
  calc ∫ x, convMeasure g μ x ^ 2 ∂μ ≤ ∫ x, ∫ y, g (x - y) ^ 2 ∂μ ∂μ :=
        integral_mono_ae hint hI hbound
    _ = _ := (integral_prod (fun p : Torus d × Torus d => g (p.1 - p.2) ^ 2) hsq).symm


/-- Mean `G = ∬ g(x-y) dμ dμ`. -/
def gMean (g : Torus d → ℝ) (μ : Measure (Torus d)) : ℝ :=
  ∫ p : Torus d × Torus d, g (p.1 - p.2) ∂μ.prod μ

/-- Hoeffding kernel `k(x,y) = g(x-y) - g*μ(x) - g*μ(y) + ∬ g`. -/
def hoeffK (g : Torus d → ℝ) (μ : Measure (Torus d)) (x y : Torus d) : ℝ :=
  g (x - y) - convMeasure g μ x - convMeasure g μ y + gMean g μ

variable {g μ}

theorem gMean_eq (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) :
    gMean g μ = ∫ x, convMeasure g μ x ∂μ :=
  integral_prod (fun p : Torus d × Torus d => g (p.1 - p.2)) (hW.integrable one_le_two)

theorem hoeffK_symm (hg : ∀ x, g (-x) = g x) (x y : Torus d) : hoeffK g μ x y = hoeffK g μ y x := by
  unfold hoeffK
  have : g (x - y) = g (y - x) := by rw [← hg (y - x)]; congr 1; abel
  rw [this]; ring

theorem hoeffK_memLp (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) :
    MemLp (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2) 2 (μ.prod μ) := by
  have hh := (h_memLp_sq_le g μ hW).1
  have h1 : MemLp (fun p : Torus d × Torus d => convMeasure g μ p.1) 2 (μ.prod μ) :=
    hh.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := μ))
  have h2 : MemLp (fun p : Torus d × Torus d => convMeasure g μ p.2) 2 (μ.prod μ) :=
    hh.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := μ))
  have h3 : MemLp (fun _ : Torus d × Torus d => gMean g μ) 2 (μ.prod μ) := memLp_const _
  exact ((hW.sub h1).sub h2).add h3

theorem hoeffK_degenerate (hg : ∀ x, g (-x) = g x)
    (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) :
    ∀ᵐ y ∂μ, ∫ x, hoeffK g μ x y ∂μ = 0 := by
  have hW1 : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ) :=
    hW.integrable one_le_two
  have hae : ∀ᵐ y ∂μ, Integrable (fun x => g (y - x)) μ := hW1.prod_right_ae
  have hhi := h_integrable g μ hW
  filter_upwards [hae] with y hy
  have e1 : ∀ x, g (x - y) = g (y - x) := fun x => by rw [← hg (y - x)]; congr 1; abel
  have hy' : Integrable (fun x => g (x - y)) μ := by simpa [e1] using hy
  unfold hoeffK
  rw [integral_add, integral_sub, integral_sub]
  · have hμ : μ.real Set.univ = 1 := by simp [Measure.real]
    simp only [e1, integral_const, hμ, smul_eq_mul, one_mul]
    rw [← gMean_eq hW]
    show ∫ x, g (y - x) ∂μ - gMean g μ - convMeasure g μ y + gMean g μ = 0
    unfold convMeasure; ring
  · exact hy'
  · exact hhi
  · exact hy'.sub hhi
  · exact integrable_const _
  · exact (hy'.sub hhi).sub (integrable_const _)
  · exact integrable_const _


theorem hoeffK_orth_fst (hg : ∀ x, g (-x) = g x)
    (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ))
    {φ : Torus d → ℝ} (hφ : MemLp φ 2 μ) :
    ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 * φ p.1 ∂μ.prod μ = 0 := by
  have hk := hoeffK_memLp hW
  have hφ' : MemLp (fun p : Torus d × Torus d => φ p.1) 2 (μ.prod μ) :=
    hφ.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := μ))
  have hint : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 * φ p.1) (μ.prod μ) :=
    hk.integrable_mul hφ'
  rw [integral_prod _ hint]
  have hdeg := hoeffK_degenerate hg hW
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hdeg] with x hx
  simp only [Pi.zero_apply]
  rw [integral_mul_const]
  have : ∫ y, hoeffK g μ x y ∂μ = 0 := by
    simp_rw [hoeffK_symm hg x]
    exact hx
  rw [this, zero_mul]

theorem hoeffK_orth_snd (hg : ∀ x, g (-x) = g x)
    (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ))
    {φ : Torus d → ℝ} (hφ : MemLp φ 2 μ) :
    ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 * φ p.2 ∂μ.prod μ = 0 := by
  have hk := hoeffK_memLp hW
  have hφ' : MemLp (fun p : Torus d × Torus d => φ p.2) 2 (μ.prod μ) :=
    hφ.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := μ))
  have hint : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 * φ p.2) (μ.prod μ) :=
    hk.integrable_mul hφ'
  rw [integral_prod_symm _ hint]
  have hdeg := hoeffK_degenerate hg hW
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hdeg] with y hy
  simp only [Pi.zero_apply]
  rw [integral_mul_const, hy, zero_mul]

theorem hoeffK_sq_le (hg : ∀ x, g (-x) = g x)
    (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) :
    ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 ^ 2 ∂μ.prod μ ≤
      ∫ p : Torus d × Torus d, g (p.1 - p.2) ^ 2 ∂μ.prod μ := by
  have hk := hoeffK_memLp hW
  have hh := (h_memLp_sq_le g μ hW).1
  have hsq : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2) ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hW.aestronglyMeasurable).mp hW
  have ksq : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).mp hk
  -- m = h(x) + h(y) - G
  set m : Torus d × Torus d → ℝ := fun p => convMeasure g μ p.1 + convMeasure g μ p.2 - gMean g μ
    with hm
  have hmL : MemLp m 2 (μ.prod μ) := by
    have h1 : MemLp (fun p : Torus d × Torus d => convMeasure g μ p.1) 2 (μ.prod μ) :=
      hh.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := μ))
    have h2 : MemLp (fun p : Torus d × Torus d => convMeasure g μ p.2) 2 (μ.prod μ) :=
      hh.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := μ))
    exact (h1.add h2).sub (memLp_const _)
  have msq : Integrable (fun p => m p ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hmL.aestronglyMeasurable).mp hmL
  have hkm : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 * m p) (μ.prod μ) :=
    hk.integrable_mul hmL
  have hW_eq : ∀ p : Torus d × Torus d, g (p.1 - p.2) ^ 2 =
      hoeffK g μ p.1 p.2 ^ 2 + 2 * (hoeffK g μ p.1 p.2 * m p) + m p ^ 2 := by
    intro p
    simp only [hoeffK, hm]
    ring
  have hkm0 : ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 * m p ∂μ.prod μ = 0 := by
    have e : ∀ p : Torus d × Torus d, hoeffK g μ p.1 p.2 * m p =
        hoeffK g μ p.1 p.2 * convMeasure g μ p.1 + hoeffK g μ p.1 p.2 * convMeasure g μ p.2
          - gMean g μ * hoeffK g μ p.1 p.2 := by
      intro p; simp only [hm]; ring
    have i1 : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 * convMeasure g μ p.1) (μ.prod μ) :=
      hk.integrable_mul (hh.comp_measurePreserving (measurePreserving_fst (μ := μ) (ν := μ)))
    have i2 : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 * convMeasure g μ p.2) (μ.prod μ) :=
      hk.integrable_mul (hh.comp_measurePreserving (measurePreserving_snd (μ := μ) (ν := μ)))
    have i3 : Integrable (fun p : Torus d × Torus d => gMean g μ * hoeffK g μ p.1 p.2) (μ.prod μ) :=
      (hk.integrable one_le_two).const_mul _
    have i12 : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 * convMeasure g μ p.1 +
        hoeffK g μ p.1 p.2 * convMeasure g μ p.2) (μ.prod μ) := i1.add i2
    simp_rw [e]
    rw [integral_sub i12 i3, integral_add i1 i2,
      hoeffK_orth_fst hg hW hh, hoeffK_orth_snd hg hW hh]
    have h1 := hoeffK_orth_fst hg hW (memLp_const (1 : ℝ))
    simp only [mul_one] at h1
    rw [integral_const_mul, h1]
    ring
  have : ∫ p : Torus d × Torus d, g (p.1 - p.2) ^ 2 ∂μ.prod μ =
      ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 ^ 2 ∂μ.prod μ + ∫ p, m p ^ 2 ∂μ.prod μ := by
    simp_rw [hW_eq]
    have i12 : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 ^ 2 +
        2 * (hoeffK g μ p.1 p.2 * m p)) (μ.prod μ) := ksq.add (hkm.const_mul 2)
    rw [integral_add i12 msq, integral_add ksq (hkm.const_mul 2),
      integral_const_mul, hkm0]
    ring
  rw [this]
  have := integral_nonneg (μ := μ.prod μ) (f := fun p => m p ^ 2) (fun p => sq_nonneg (m p))
  linarith


section Lifting

variable (μ)

theorem pi_update_measurePreserving (a : Fin N) :
    MeasurePreserving (fun q : Torus d × Config d N => Function.update q.2 a q.1)
      (μ.prod (Measure.pi fun _ : Fin N => μ)) (Measure.pi fun _ : Fin N => μ) := by
  have hmeas : Measurable (fun q : Torus d × Config d N => Function.update q.2 a q.1) := by
    refine Measurable.of_eval fun i => ?_
    by_cases h : i = a
    · subst h
      simp only [Function.update_self]
      exact measurable_fst
    · simp only [Function.update_of_ne h]
      exact (measurable_pi_apply i).comp measurable_snd
  refine ⟨hmeas, ?_⟩
  refine (Measure.pi_eq (μ := fun _ : Fin N => μ) fun s hs => ?_).symm
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun q : Torus d × Config d N => Function.update q.2 a q.1) ⁻¹' (Set.univ.pi s) =
      (s a) ×ˢ (Set.univ.pi (Function.update s a Set.univ)) := by
    ext ⟨x, X⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨by simpa using h a, fun i => ?_⟩
      by_cases hi : i = a
      · subst hi; simp
      · have := h i
        simpa [Function.update_of_ne hi] using this
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = a
      · subst hi; simpa using h1
      · have := h2 i
        simpa [Function.update_of_ne hi] using this
  have hms : MeasurableSet (Set.univ.pi (Function.update s a Set.univ)) := by
    refine MeasurableSet.univ_pi fun i => ?_
    by_cases hi : i = a
    · subst hi; simp
    · simp only [Function.update_of_ne hi]; exact hs i
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  have hprod : ∏ i, μ (Function.update s a Set.univ i) = ∏ i ∈ Finset.univ.erase a, μ (s i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a)]
    simp only [Function.update_self, measure_univ, one_mul]
    refine Finset.prod_congr rfl fun i hi => ?_
    simp [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hprod, Finset.mul_prod_erase Finset.univ (fun i => μ (s i)) (Finset.mem_univ a)]

theorem memLp_hoeffK_pair (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ))
    {i j : Fin N} (hij : i ≠ j) :
    MemLp (fun X : Config d N => hoeffK g μ (X i) (X j)) 2 (Measure.pi fun _ : Fin N => μ) :=
  (hoeffK_memLp hW).comp_measurePreserving
    (f := fun X : Config d N => (X i, X j))
    ⟨(measurable_pi_apply i).prodMk (measurable_pi_apply j), pi_map_pair μ hij⟩

theorem siv (hg : ∀ x, g (-x) = g x)
    (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ))
    {a b : Fin N} (hab : a ≠ b) (Ψ : Config d N → ℝ)
    (hΨ : ∀ X x, Ψ (Function.update X a x) = Ψ X)
    (hΨL : MemLp Ψ 2 (Measure.pi fun _ : Fin N => μ)) :
    ∫ X, hoeffK g μ (X a) (X b) * Ψ X ∂(Measure.pi fun _ : Fin N => μ) = 0 := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  have hmp : MeasurePreserving (fun q : Torus d × Config d N => Function.update q.2 a q.1)
      (μ.prod P) P := pi_update_measurePreserving (d := d) (N := N) μ a
  have hΦ : Integrable (fun X : Config d N => hoeffK g μ (X a) (X b) * Ψ X) P :=
    (memLp_hoeffK_pair μ hW hab).integrable_mul hΨL
  have h1 : ∫ X, hoeffK g μ (X a) (X b) * Ψ X ∂P =
      ∫ q : Torus d × Config d N, hoeffK g μ (Function.update q.2 a q.1 a)
        (Function.update q.2 a q.1 b) * Ψ (Function.update q.2 a q.1) ∂(μ.prod P) := by
    have := integral_map (f := fun X : Config d N => hoeffK g μ (X a) (X b) * Ψ X)
      hmp.measurable.aemeasurable (hmp.map_eq ▸ hΦ.aestronglyMeasurable)
    rw [hmp.map_eq] at this
    exact this
  rw [h1]
  have hsimp : ∀ q : Torus d × Config d N, hoeffK g μ (Function.update q.2 a q.1 a)
        (Function.update q.2 a q.1 b) * Ψ (Function.update q.2 a q.1) =
      hoeffK g μ q.1 (q.2 b) * Ψ q.2 := by
    intro q
    rw [hΨ, Function.update_self, Function.update_of_ne hab.symm]
  simp_rw [hsimp]
  have hint : Integrable (fun q : Torus d × Config d N => hoeffK g μ q.1 (q.2 b) * Ψ q.2) (μ.prod P) := by
    have := hmp.integrable_comp_of_integrable hΦ
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.comp]
    exact hsimp q
  rw [integral_prod_symm _ hint]
  have hdeg := hoeffK_degenerate hg hW
  have hmpb : MeasurePreserving (fun X : Config d N => X b) P μ := measurePreserving_eval _ b
  have hdeg' : ∀ᵐ X ∂P, ∫ x, hoeffK g μ x (X b) ∂μ = 0 := hmpb.quasiMeasurePreserving.ae hdeg
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hdeg'] with X hX
  simp only [Pi.zero_apply]
  rw [integral_mul_const, hX, zero_mul]

theorem pair_orth (hg : ∀ x, g (-x) = g x)
    (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ))
    {i j i' j' : Fin N} (hij : i ≠ j) (hij' : i' ≠ j')
    (h1 : ¬ (i' = i ∧ j' = j)) (h2 : ¬ (i' = j ∧ j' = i)) :
    ∫ X, hoeffK g μ (X i) (X j) * hoeffK g μ (X i') (X j') ∂(Measure.pi fun _ : Fin N => μ) = 0 := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  have mij := memLp_hoeffK_pair (N := N) μ hW hij
  have mij' := memLp_hoeffK_pair (N := N) μ hW hij'
  by_cases hA : i' ∈ ({i, j} : Finset (Fin N))
  · by_cases hB : j' ∈ ({i, j} : Finset (Fin N))
    · exfalso
      simp only [Finset.mem_insert, Finset.mem_singleton] at hA hB
      rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> simp_all
    · -- j' appears once
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hB
      have := siv μ hg hW (a := j') (b := i') (Ne.symm hij') (fun X => hoeffK g μ (X i) (X j))
        (fun X x => by
          simp [Function.update_of_ne (Ne.symm hB.1), Function.update_of_ne (Ne.symm hB.2)]) mij
      have e : ∀ X : Config d N, hoeffK g μ (X j') (X i') * hoeffK g μ (X i) (X j) =
          hoeffK g μ (X i) (X j) * hoeffK g μ (X i') (X j') := by
        intro X; rw [hoeffK_symm hg (X j') (X i'), mul_comm]
      simp_rw [e] at this
      exact this
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hA
    have := siv μ hg hW (a := i') (b := j') hij' (fun X => hoeffK g μ (X i) (X j))
      (fun X x => by
        simp [Function.update_of_ne (Ne.symm hA.1), Function.update_of_ne (Ne.symm hA.2)]) mij
    have e : ∀ X : Config d N, hoeffK g μ (X i') (X j') * hoeffK g μ (X i) (X j) =
        hoeffK g μ (X i) (X j) * hoeffK g μ (X i') (X j') := fun X => mul_comm _ _
    simp_rw [e] at this
    exact this

theorem pair_sq (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ))
    {i j : Fin N} (hij : i ≠ j) :
    ∫ X, hoeffK g μ (X i) (X j) * hoeffK g μ (X i) (X j) ∂(Measure.pi fun _ : Fin N => μ) =
      ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 ^ 2 ∂μ.prod μ := by
  have hk := hoeffK_memLp hW
  have hi : Integrable (fun p : Torus d × Torus d => hoeffK g μ p.1 p.2 ^ 2) (μ.prod μ) :=
    (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).mp hk
  have := integral_pair_comp μ hij hi
  simp only [sq] at this
  simpa [sq] using this

theorem sum_pair_sq (hg : ∀ x, g (-x) = g x)
    (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) :
    ∫ X, (∑ i, ∑ j ∈ Finset.univ.erase i, hoeffK g μ (X i) (X j)) ^ 2
        ∂(Measure.pi fun _ : Fin N => μ) =
      2 * (N : ℝ) * ((N : ℝ) - 1) * ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 ^ 2 ∂μ.prod μ := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  set K := ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 ^ 2 ∂μ.prod μ with hK
  have hS : ∀ X : Config d N, (∑ i, ∑ j ∈ Finset.univ.erase i, hoeffK g μ (X i) (X j)) ^ 2 =
      ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ i', ∑ j' ∈ Finset.univ.erase i',
        hoeffK g μ (X i) (X j) * hoeffK g μ (X i') (X j') := by
    intro X
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
  have hint : ∀ i j i' j' : Fin N, i ≠ j → i' ≠ j' → Integrable (fun X : Config d N =>
      hoeffK g μ (X i) (X j) * hoeffK g μ (X i') (X j')) P :=
    fun i j i' j' hij hij' => (memLp_hoeffK_pair μ hW hij).integrable_mul (memLp_hoeffK_pair μ hW hij')
  simp_rw [hS]
  have hne : ∀ i j : Fin N, j ∈ Finset.univ.erase i → i ≠ j := fun i j hj => (Finset.ne_of_mem_erase hj).symm
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j hj => integrable_finsetSum _ fun i' _ =>
    integrable_finsetSum _ fun j' hj' => hint i j i' j' (hne i j hj) (hne i' j' hj'))]
  have step : ∀ i ∈ (Finset.univ : Finset (Fin N)), ∫ X, ∑ j ∈ Finset.univ.erase i, ∑ i', ∑ j' ∈ Finset.univ.erase i',
      hoeffK g μ (X i) (X j) * hoeffK g μ (X i') (X j') ∂P = ∑ j ∈ Finset.univ.erase i, 2 * K := by
    intro i _
    rw [integral_finsetSum _ (fun j hj => integrable_finsetSum _ fun i' _ =>
      integrable_finsetSum _ fun j' hj' => hint i j i' j' (hne i j hj) (hne i' j' hj'))]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij := hne i j hj
    rw [integral_finsetSum _ (fun i' _ => integrable_finsetSum _ fun j' hj' =>
      hint i j i' j' hij (hne i' j' hj'))]
    rw [Finset.sum_congr rfl fun i' _ => integral_finsetSum _ (fun j' hj' =>
      hint i j i' j' hij (hne i' j' hj'))]
    have hval : ∀ i' j', j' ∈ Finset.univ.erase i' →
        ∫ X, hoeffK g μ (X i) (X j) * hoeffK g μ (X i') (X j') ∂P =
          (if i' = i ∧ j' = j then K else 0) + (if i' = j ∧ j' = i then K else 0) := by
      intro i' j' hj'
      have hij' := hne i' j' hj'
      by_cases c1 : i' = i ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := c1
        have c2 : ¬ (i' = j' ∧ j' = i') := fun h => hij' h.1
        simp only [c2, if_false, add_zero, true_and, and_self, if_true]
        exact pair_sq μ hW hij
      · by_cases c2 : i' = j ∧ j' = i
        · obtain ⟨h1, h2⟩ := c2
          rw [h1, h2]
          have c1' : ¬ (j = i ∧ i = j) := fun h => hij h.2
          simp only [c1', ite_false, zero_add, and_self, ite_true]
          have e : ∀ X : Config d N, hoeffK g μ (X i) (X j) * hoeffK g μ (X j) (X i) =
              hoeffK g μ (X i) (X j) * hoeffK g μ (X i) (X j) := by
            intro X; rw [hoeffK_symm hg (X j) (X i)]
          simp_rw [e]
          exact pair_sq μ hW hij
        · simp only [c1, c2, if_false, add_zero]
          exact pair_orth μ hg hW hij hij' c1 c2
    rw [Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun j' hj' => hval i' j' hj']
    simp_rw [Finset.sum_add_distrib]
    have e1 : ∑ i', ∑ j' ∈ Finset.univ.erase i', (if i' = i ∧ j' = j then K else 0) = K := by
      simp_rw [ite_and]
      rw [Finset.sum_eq_single i]
      · simp [Finset.sum_ite_eq', hj]
      · intro b _ hb; simp [hb]
      · simp
    have e2 : ∑ i', ∑ j' ∈ Finset.univ.erase i', (if i' = j ∧ j' = i then K else 0) = K := by
      simp_rw [ite_and]
      rw [Finset.sum_eq_single j]
      · have : i ∈ Finset.univ.erase j := by simp [hij]
        simp [Finset.sum_ite_eq', this]
      · intro b _ hb; simp [hb]
      · simp
    rw [e1, e2]; ring
  rw [Finset.sum_congr rfl step]
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · subst h0; simp
  · rw [Nat.cast_sub h0]
    simp
    ring


theorem sqrt_int_sq_add_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {f h : α → ℝ} (hf : MemLp f 2 ν) (hh : MemLp h 2 ν) :
    Real.sqrt (∫ x, (f x + h x) ^ 2 ∂ν) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂ν) + Real.sqrt (∫ x, h x ^ 2 ∂ν) := by
  have key : ∀ k : α → ℝ, MemLp k 2 ν →
      (eLpNorm k 2 ν).toReal = Real.sqrt (∫ x, k x ^ 2 ∂ν) := by
    intro k hk
    rw [hk.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), ENNReal.toReal_ofReal
      (by positivity)]
    simp [Real.sqrt_eq_rpow]
  have hfh : MemLp (fun x => f x + h x) 2 ν := hf.add hh
  rw [← key _ hfh, ← key _ hf, ← key _ hh]
  have := eLpNorm_add_le (μ := ν) (p := 2) (f := f) (g := h) (by norm_num)
  have h2 : (eLpNorm (fun x => f x + h x) 2 ν).toReal ≤ (eLpNorm f 2 ν + eLpNorm h 2 ν).toReal :=
    ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hh.eLpNorm_ne_top⟩) this
  rwa [ENNReal.toReal_add hf.eLpNorm_ne_top hh.eLpNorm_ne_top] at h2

theorem energy_decomp (hN : 1 ≤ N)
    (hW : MemLp (fun p : Torus d × Torus d => g (p.1 - p.2)) 2 (μ.prod μ)) (X : Config d N) :
    modulatedEnergyKernel g X μ =
      (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i, hoeffK g μ (X i) (X j))
        - (1 / (N : ℝ) ^ 2) * ∑ i, (convMeasure g μ (X i) - gMean g μ / 2) := by
  have hc : ∫ x, convMeasure g μ x ∂μ = gMean g μ := (gMean_eq hW).symm
  have hN' : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    exact this.ne'
  have hsum : ∑ i, ∑ j ∈ Finset.univ.erase i, hoeffK g μ (X i) (X j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) -
        2 * ((N : ℝ) - 1) * ∑ i, convMeasure g μ (X i) + (N : ℝ) * ((N : ℝ) - 1) * gMean g μ := by
    simp only [hoeffK, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have e1 : ∑ i, ∑ j ∈ Finset.univ.erase i, convMeasure g μ (X j) =
        ((N : ℝ) - 1) * ∑ j, convMeasure g μ (X j) := by
      simp only [Finset.sum_erase_eq_sub (Finset.mem_univ _), Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [e1, Nat.cast_sub hN]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_one]
    have e2 : ∑ i, ((N : ℝ) - 1) * convMeasure g μ (X i) =
        ((N : ℝ) - 1) * ∑ i, convMeasure g μ (X i) := by rw [Finset.mul_sum]
    rw [e2]
    ring
  unfold modulatedEnergyKernel modulatedEnergy
  have e : ∀ x, ∫ y, (fun x y => g (x - y)) x y ∂μ = convMeasure g μ x := fun _ => rfl
  simp only [e, hc, hsum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem T2_second_moment (hN : 1 ≤ N) {u : Torus d → ℝ} (hu : MemLp u 2 μ) :
    ∫ X, (∑ i, u (X i)) ^ 2 ∂(Measure.pi fun _ : Fin N => μ) ≤
      (N : ℝ) ^ 2 * ∫ x, u x ^ 2 ∂μ := by
  set P := Measure.pi fun _ : Fin N => μ with hP
  have hi : ∀ i : Fin N, MemLp (fun X : Config d N => u (X i)) 2 P := fun i =>
    hu.comp_measurePreserving (measurePreserving_eval _ i)
  have hi2 : ∀ i : Fin N, Integrable (fun X : Config d N => u (X i) ^ 2) P := fun i =>
    (memLp_two_iff_integrable_sq (hi i).aestronglyMeasurable).mp (hi i)
  have hu2 : Integrable (fun x => u x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).mp hu
  have hS : MemLp (fun X : Config d N => ∑ i, u (X i)) 2 P := by
    exact memLp_finsetSum (Finset.univ : Finset (Fin N)) (fun i _ => hi i)
  have hSi : Integrable (fun X : Config d N => (∑ i, u (X i)) ^ 2) P :=
    (memLp_two_iff_integrable_sq hS.aestronglyMeasurable).mp hS
  calc ∫ X, (∑ i, u (X i)) ^ 2 ∂P ≤ ∫ X, (N : ℝ) * ∑ i, u (X i) ^ 2 ∂P := by
        refine integral_mono hSi ((integrable_finsetSum _ fun i _ => hi2 i).const_mul _) ?_
        intro X
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => u (X i))
        simpa using this
    _ = (N : ℝ) * ∑ i, ∫ X, u (X i) ^ 2 ∂P := by
        rw [integral_const_mul, integral_finsetSum _ fun i _ => hi2 i]
    _ = (N : ℝ) ^ 2 * ∫ x, u x ^ 2 ∂μ := by
        have : ∀ i : Fin N, ∫ X, u (X i) ^ 2 ∂P = ∫ x, u x ^ 2 ∂μ := fun i =>
          integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) (hu2.aestronglyMeasurable)
        simp_rw [this]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Lifting

end SecondMoment
end SecondMomentAux

section SecondMomentEven
open SecondMomentAux
variable {d N : ℕ}

/-- Lemma C.8 `M:B:lem:v-statistics` (lines 12327-12330): for i.i.d. data with
`g ∈ L²(μ° ⊗ μ°)`, `(E[(F_N + o_N)²])^{1/2} ≤ C (N⁻¹ ∨ o_N)`, with `C` depending on
`∬(1+g²) d(μ°)^{⊗2}` and `‖g*μ°‖_∞`. The source's `g` is the periodic Riesz or logarithmic
kernel, which is even and measurable, and `N ≥ 2` throughout; the statement is made for an
abstract kernel and therefore carries these three properties as hypotheses (without evenness the
one-body term `g * μ°` and the pair sum see different kernels and the rate is only `N^{-1/2}`;
for `N = 0` the bound fails, see `second_moment_modulatedEnergy_iid_false_of_N_zero` and
`docs/ISSUES.md` §E). -/
theorem second_moment_modulatedEnergy_iid (g : Torus d → ℝ) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (hg : ∀ x, g (-x) = g x)
    (hmeas : AEStronglyMeasurable (fun p : Torus d × Torus d => g (p.1 - p.2)) (μ.prod μ))
    (o : ℝ) (ho : 0 ≤ o)
    (hint2 : Integrable (fun p : Torus d × Torus d => g (p.1 - p.2) ^ 2) (μ.prod μ))
    (M : ℝ) (hM : ∀ x, |convMeasure g μ x| ≤ M) (hN : 1 ≤ N) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ C', (∫ p : Torus d × Torus d, (1 + g (p.1 - p.2) ^ 2) ∂(μ.prod μ)) ≤ C' →
      M ≤ C' → C ≤ C' * C' + C') ∧
      Real.sqrt (∫ X, (modulatedEnergyKernel g X μ + o) ^ 2 ∂(Measure.pi fun _ : Fin N => μ)) ≤
        C * max ((N : ℝ)⁻¹) o := by
  have hW := W_memLp g μ hmeas hint2
  set G := ∫ p : Torus d × Torus d, g (p.1 - p.2) ^ 2 ∂(μ.prod μ) with hG
  have hG0 : 0 ≤ G := integral_nonneg fun _ => sq_nonneg _
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc1 : ∫ p : Torus d × Torus d, (1 + g (p.1 - p.2) ^ 2) ∂(μ.prod μ) = 1 + G := by
    rw [integral_add (integrable_const _) hint2]; simp; exact hG.symm
  refine ⟨2 + G, by positivity, ?_, ?_⟩
  · intro C' h1 _
    rw [hc1] at h1
    nlinarith
  set P := Measure.pi fun _ : Fin N => μ with hP
  set c := gMean g μ with hc
  set m := convMeasure g μ with hm
  obtain ⟨hmL, hm2⟩ := h_memLp_sq_le g μ hW
  set u : Torus d → ℝ := fun x => m x - c / 2 with hu
  have huL : MemLp u 2 μ := hmL.sub (memLp_const _)
  have hmint : Integrable m μ := hmL.integrable one_le_two
  have hm2i : Integrable (fun x => m x ^ 2) μ :=
    (memLp_two_iff_integrable_sq hmL.aestronglyMeasurable).mp hmL
  have hint_m : ∫ x, m x ∂μ = c := (gMean_eq hW).symm
  have hu2 : ∫ x, u x ^ 2 ∂μ ≤ G := by
    have : ∫ x, u x ^ 2 ∂μ = ∫ x, m x ^ 2 ∂μ - c * ∫ x, m x ∂μ + c ^ 2 / 4 := by
      have e : ∀ x, u x ^ 2 = (m x ^ 2 - c * m x) + c ^ 2 / 4 := fun x => by
        simp only [hu]; ring
      simp_rw [e]
      have hsub : Integrable (fun x => m x ^ 2 - c * m x) μ := hm2i.sub (hmint.const_mul c)
      rw [integral_add hsub (integrable_const _),
        integral_sub hm2i (hmint.const_mul c), integral_const_mul]
      simp
    rw [this, hint_m]
    nlinarith [sq_nonneg c]
  -- the two pieces
  set T1 : Config d N → ℝ := fun X => (1 / (2 * (N : ℝ) ^ 2)) *
    ∑ i, ∑ j ∈ Finset.univ.erase i, hoeffK g μ (X i) (X j) with hT1def
  set T2 : Config d N → ℝ := fun X => -((1 / (N : ℝ) ^ 2) * ∑ i, u (X i)) with hT2def
  have hF : ∀ X, modulatedEnergyKernel g X μ = T1 X + T2 X := by
    intro X
    rw [energy_decomp (g := g) (μ := μ) hN hW X]
    simp only [hT1def, hT2def, hu, hm, hc]
    ring
  have hSK : MemLp (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, hoeffK g μ (X i) (X j))
      2 P := by
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j hj => ?_
    exact memLp_hoeffK_pair μ hW (Finset.ne_of_mem_erase hj).symm
  have hSU : MemLp (fun X : Config d N => ∑ i, u (X i)) 2 P :=
    memLp_finsetSum _ fun i _ => huL.comp_measurePreserving (measurePreserving_eval _ i)
  have hT1L : MemLp T1 2 P := hSK.const_mul _
  have hT2L : MemLp T2 2 P := (hSU.const_mul _).neg
  have hbound : (G + 1) / (2 * N) = (1 + G) / (2 * N) := by ring
  -- second moment of T1
  have hI1 : Real.sqrt (∫ X, T1 X ^ 2 ∂P) ≤ (1 + G) / (2 * N) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have e : ∀ X, T1 X ^ 2 = (1 / (2 * (N : ℝ) ^ 2)) ^ 2 *
        (∑ i, ∑ j ∈ Finset.univ.erase i, hoeffK g μ (X i) (X j)) ^ 2 := fun X => by
      simp only [hT1def]; ring
    simp_rw [e]
    rw [integral_const_mul, sum_pair_sq (g := g) (μ := μ) hg hW]
    have hK := hoeffK_sq_le hg hW
    have hK0 : 0 ≤ ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 ^ 2 ∂μ.prod μ :=
      integral_nonneg fun _ => sq_nonneg _
    set K := ∫ p : Torus d × Torus d, hoeffK g μ p.1 p.2 ^ 2 ∂μ.prod μ
    have : (1 / (2 * (N : ℝ) ^ 2)) ^ 2 * (2 * (N : ℝ) * ((N : ℝ) - 1) * K) =
        (N - 1) * K / (2 * N ^ 3) := by field_simp
    rw [this, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hKG : K ≤ G := hK
    have : (0 : ℝ) ≤ (N - 1) := by linarith
    nlinarith [mul_nonneg this hK0, sq_nonneg (G - 1), mul_nonneg (mul_nonneg this hNpos.le) hK0,
      mul_nonneg hNpos.le hG0, pow_pos hNpos 3, mul_nonneg (pow_pos hNpos 3).le hG0,
      mul_nonneg (mul_nonneg this (pow_pos hNpos 2).le) (sub_nonneg.mpr hKG)]
  -- second moment of T2
  have hI2 : Real.sqrt (∫ X, T2 X ^ 2 ∂P) ≤ (1 + G) / (2 * N) := by
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    have e : ∀ X, T2 X ^ 2 = (1 / (N : ℝ) ^ 2) ^ 2 * (∑ i, u (X i)) ^ 2 := fun X => by
      simp only [hT2def]; ring
    simp_rw [e]
    rw [integral_const_mul]
    have h1 := T2_second_moment μ hN huL
    have h0 : (0 : ℝ) ≤ (1 / (N : ℝ) ^ 2) ^ 2 := by positivity
    calc (1 / (N : ℝ) ^ 2) ^ 2 * ∫ X, (∑ i, u (X i)) ^ 2 ∂P
        ≤ (1 / (N : ℝ) ^ 2) ^ 2 * ((N : ℝ) ^ 2 * ∫ x, u x ^ 2 ∂μ) := mul_le_mul_of_nonneg_left h1 h0
      _ = (∫ x, u x ^ 2 ∂μ) / (N : ℝ) ^ 2 := by field_simp
      _ ≤ G / (N : ℝ) ^ 2 := by gcongr
      _ ≤ ((1 + G) / (2 * N)) ^ 2 := by
          rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg (G - 1), sq_nonneg (N : ℝ), mul_nonneg (sq_nonneg (N : ℝ)) (sq_nonneg (G - 1))]
  -- Minkowski
  have hFL : MemLp (fun X => modulatedEnergyKernel g X μ) 2 P := by
    have : (fun X => modulatedEnergyKernel g X μ) = fun X => T1 X + T2 X := funext hF
    rw [this]; exact hT1L.add hT2L
  have hstep1 := sqrt_int_sq_add_le (ν := P) hFL (memLp_const o)
  have hstep2 := sqrt_int_sq_add_le (ν := P) hT1L hT2L
  have hFeq : ∫ X, modulatedEnergyKernel g X μ ^ 2 ∂P = ∫ X, (T1 X + T2 X) ^ 2 ∂P := by
    simp_rw [hF]
  have hconst : Real.sqrt (∫ _ : Config d N, o ^ 2 ∂P) = o := by
    simp [Real.sqrt_sq ho]
  rw [hconst, hFeq] at hstep1
  have hmax1 : (N : ℝ)⁻¹ ≤ max ((N : ℝ)⁻¹) o := le_max_left _ _
  have hmax2 : o ≤ max ((N : ℝ)⁻¹) o := le_max_right _ _
  have hA : (1 + G) / (2 * N) + (1 + G) / (2 * N) = (1 + G) * (N : ℝ)⁻¹ := by
    field_simp; ring
  calc Real.sqrt (∫ X, (modulatedEnergyKernel g X μ + o) ^ 2 ∂P)
      ≤ Real.sqrt (∫ X, (T1 X + T2 X) ^ 2 ∂P) + o := hstep1
    _ ≤ (1 + G) * (N : ℝ)⁻¹ + o := by linarith
    _ ≤ (1 + G) * max ((N : ℝ)⁻¹) o + 1 * max ((N : ℝ)⁻¹) o := by
        gcongr
        · linarith
    _ = (2 + G) * max ((N : ℝ)⁻¹) o := by ring

/-- Counterexample to `second_moment_modulatedEnergy_iid` at `N = 0` (kernel `g ≡ 1`, `o = 0`):
`F_0 = ½ ∬ g = ½`, while the right-hand side `C · max (0⁻¹) 0` is `0`. -/
theorem second_moment_modulatedEnergy_iid_false_of_N_zero :
    ¬ (∀ (g : Torus 1 → ℝ) (μ : Measure (Torus 1)) [IsProbabilityMeasure μ] (o : ℝ) (_ : 0 ≤ o)
      (_ : Integrable (fun p : Torus 1 × Torus 1 => g (p.1 - p.2) ^ 2) (μ.prod μ))
      (M : ℝ) (_ : ∀ x, |convMeasure g μ x| ≤ M),
      ∃ C : ℝ, 0 ≤ C ∧ Real.sqrt (∫ X, (modulatedEnergyKernel g X μ + o) ^ 2
        ∂(Measure.pi fun _ : Fin 0 => μ)) ≤ C * max (((0 : ℕ) : ℝ)⁻¹) o) := by
  intro H
  obtain ⟨C, hC, h⟩ := H (fun _ => 1) volume 0 le_rfl (by simp) 1 (by
    intro x; simp [convMeasure])
  simp [modulatedEnergyKernel, modulatedEnergy] at h
  norm_num at h

end SecondMomentEven


/-! ### Auxiliary facts for the first-marginal centering (work package STAT-4.21) -/

section MarginalAux


section Coord

variable {d N : ℕ} {m : ℝ}

theorem meanEmpirical_eq_sum (P : Measure (Config d N)) :
    meanEmpirical P = (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, P.map (fun X : Config d N => X i) := by
  ext s hs
  rw [meanEmpirical_apply P hs, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
    smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Measure.map_apply (measurable_pi_apply i) hs]; rfl

theorem integral_meanEmpirical (P : Measure (Config d N)) [IsProbabilityMeasure P]
    {f : Torus d → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(meanEmpirical P) = (N : ℝ)⁻¹ * ∑ i, ∫ X, f (X i) ∂P := by
  rw [meanEmpirical_eq_sum, integral_smul_measure, integral_finsetSum_measure]
  · have : ∀ i : Fin N, ∫ x, f x ∂(P.map (fun X : Config d N => X i)) = ∫ X, f (X i) ∂P := by
      intro i
      exact integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
    simp [this]
  · intro i _
    have : IsProbabilityMeasure (P.map (fun X : Config d N => X i)) :=
      ⟨by rw [Measure.map_apply (measurable_pi_apply i) MeasurableSet.univ]; simp⟩
    exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_ofMeasureDiff_empirical (hm : (d : ℝ) < 2 * m) (P : Measure (Config d N))
    [IsProbabilityMeasure P] (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (hN : 1 ≤ N)
    (hF : AEMeasurable (fun X : Config d N => NegSobolev.ofMeasureDiff m (empirical X) μ) P) :
    ∫ X, NegSobolev.ofMeasureDiff m (empirical X) μ ∂P =
      NegSobolev.ofMeasureDiff m (meanEmpirical P) μ := by
  have hE : ∀ X : Config d N, IsProbabilityMeasure (empirical X) :=
    fun X => empirical_isProbabilityMeasure hN X
  have hM := isProbabilityMeasure_meanEmpirical P hN
  set F : Config d N → NegSobolev d m := fun X => NegSobolev.ofMeasureDiff m (empirical X) μ with hFdef
  have hint : Integrable F P := by
    refine Integrable.of_bound hF.aestronglyMeasurable (Real.sqrt (8 * ∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (-(2 * m)))) (Filter.Eventually.of_forall fun X => ?_)
    haveI := hE X
    exact norm_ofMeasureDiff_le hm (empirical X) μ
  show (∫ X, F X ∂P : lp (fun _ : NonzeroLattice d => ℝ) 2) =
    (NegSobolev.ofMeasureDiff m (meanEmpirical P) μ : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine lp.ext (funext fun k => ?_)
  have h1 : NegSobolev.coord (∫ X, F X ∂P) k = ∫ X, NegSobolev.coord (F X) k ∂P := by
    have := (negCoordCLM (m := m) k).integral_comp_comm hint
    exact this.symm
  have h2 : NegSobolev.coord (NegSobolev.ofMeasureDiff m (meanEmpirical P) μ) k =
      Lattice.jp k.1 ^ (-m) * ((N : ℝ)⁻¹ * ∑ i, ∫ X, Torus.realMode k (X i) ∂P -
        Torus.measureRealCoeff μ k) := by
    rw [coord_ofMeasureDiff hm]
    congr 2
    exact integral_meanEmpirical P (continuous_realMode' k)
  have hc : ∀ i : Fin N, Integrable (fun X : Config d N => Torus.realMode k (X i)) P := fun i =>
    ((continuous_realMode' k).comp (continuous_apply i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  show NegSobolev.coord (∫ X, F X ∂P) k = NegSobolev.coord (NegSobolev.ofMeasureDiff m (meanEmpirical P) μ) k
  rw [h1, h2]
  have h3 : ∀ X, NegSobolev.coord (F X) k = Lattice.jp k.1 ^ (-m) *
      ((N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X i) - Torus.measureRealCoeff μ k) := by
    intro X
    haveI := hE X
    rw [hFdef]; dsimp only
    rw [coord_ofMeasureDiff hm]
    congr 2
    exact integral_empirical X (continuous_realMode' k)
  simp_rw [h3]
  rw [integral_const_mul]
  congr 1
  rw [integral_sub ((integrable_finset_sum _ fun i _ => hc i).const_mul _) (integrable_const _),
    integral_const_mul, integral_finsetSum _ fun i _ => hc i]
  simp
theorem coord_ofMeasureDiff_empirical (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (hN : 1 ≤ N) (X : Config d N) (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical X) μ) k =
      Lattice.jp k.1 ^ (-m) * ((N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X i) -
        Torus.measureRealCoeff μ k) := by
  haveI := empirical_isProbabilityMeasure hN X
  rw [coord_ofMeasureDiff hm]
  congr 2
  exact integral_empirical X (continuous_realMode' k)

theorem measurable_ofMeasureDiff_empirical (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (hN : 1 ≤ N) :
    Measurable fun X : Config d N => NegSobolev.ofMeasureDiff m (empirical X) μ := by
  set F : Config d N → NegSobolev d m := fun X => NegSobolev.ofMeasureDiff m (empirical X) μ with hF
  have hc : ∀ k, Measurable fun X : Config d N => NegSobolev.coord (F X) k := by
    intro k
    simp_rw [hF, coord_ofMeasureDiff_empirical hm μ hN]
    refine measurable_const.mul (Measurable.sub (measurable_const.mul ?_) measurable_const)
    exact Finset.measurable_sum _ fun i _ =>
      (continuous_realMode' k).measurable.comp (measurable_pi_apply i)
  have hlim : ∀ X : Config d N, Tendsto
      (fun s : Finset (NonzeroLattice d) => (∑ k ∈ s,
        (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
          (NegSobolev.coord (F X) k))))
      atTop (𝓝 (F X)) := by
    intro X
    exact lp.hasSum_single (p := 2) (by simp) (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F X)
  refine measurable_of_tendsto_metrizable' (atTop : Filter (Finset (NonzeroLattice d)))
    (f := fun (s : Finset (NonzeroLattice d)) (X : Config d N) =>
      (∑ k ∈ s, (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k
        (NegSobolev.coord (F X) k)))) (fun s => ?_) (tendsto_pi_nhds.2 hlim)
  refine Finset.measurable_sum _ fun k _ => ?_
  have hcont : Continuous (fun a : ℝ => (show NegSobolev d m from
      lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 k a)) :=
    (lp.isometry_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) k).continuous
  exact hcont.measurable.comp (hc k)
end Coord

section Prob

variable {d N : ℕ}

theorem exists_abs_bound {g : Torus d → ℝ} (hg : Continuous g) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, |g x| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  have := hM x (Set.mem_univ _)
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem continuous_conv0 {g : Torus d → ℝ} (hg : Continuous g) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : Continuous fun x => ∫ y, g (x - y) ∂μ := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hg
  refine continuous_of_dominated (bound := fun _ => M) (fun x => ?_) (fun x => ?_)
    (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
  · exact (hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM _
  · exact hg.comp (continuous_id.sub continuous_const)

theorem measurable_modulatedEnergyKernel {g : Torus d → ℝ} (hg : Continuous g)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Measurable fun X : Config d N => modulatedEnergyKernel g X μ := by
  unfold modulatedEnergyKernel modulatedEnergy
  have h1 : ∀ i j : Fin N, Measurable fun X : Config d N => g (X i - X j) := fun i j =>
    hg.measurable.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have h2 : ∀ i : Fin N, Measurable fun X : Config d N => ∫ y, g (X i - y) ∂μ := fun i =>
    (continuous_conv0 hg μ).measurable.comp (measurable_pi_apply i)
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => h1 i j) _
  · exact Measurable.const_mul (Finset.measurable_sum _ fun i _ => h2 i) _

theorem abs_modulatedEnergyKernel_le {g : Torus d → ℝ} {M : ℝ} (hM : ∀ x, |g x| ≤ M)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (X : Config d N) :
    |modulatedEnergyKernel g X μ| ≤ 2 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hI : ∀ (h : Torus d → ℝ), (∀ y, |h y| ≤ M) → |∫ y, h y ∂μ| ≤ M := by
    intro h hh
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := h) (C := M)
      (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hh y)
    simpa using this
  have hI1 : ∀ x, |∫ y, g (x - y) ∂μ| ≤ M := fun x => hI _ fun y => hM _
  have hI2 : |∫ x, ∫ y, g (x - y) ∂μ ∂μ| ≤ M := hI _ hI1
  unfold modulatedEnergyKernel modulatedEnergy
  have hS1 : |∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)| ≤ (N : ℝ) * N * M := by
    calc _ ≤ ∑ i : Fin N, |∑ j ∈ Finset.univ.erase i, g (X i - X j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, (N : ℝ) * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        calc _ ≤ ∑ j ∈ Finset.univ.erase i, |g (X i - X j)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ j ∈ Finset.univ.erase i, M := Finset.sum_le_sum fun j _ => hM _
          _ = ((Finset.univ.erase i).card : ℝ) * M := by simp
          _ ≤ (N : ℝ) * M := by
            refine mul_le_mul_of_nonneg_right ?_ hM0
            have : (Finset.univ.erase i).card ≤ N := by
              calc _ ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_card (Finset.erase_subset _ _)
                _ = N := by simp
            exact_mod_cast this
      _ = (N : ℝ) * N * M := by simp; ring
  have hS2 : |∑ i : Fin N, ∫ y, g (X i - y) ∂μ| ≤ (N : ℝ) * M := by
    calc _ ≤ ∑ i : Fin N, |∫ y, g (X i - y) ∂μ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin N, M := Finset.sum_le_sum fun i _ => hI1 _
      _ = (N : ℝ) * M := by simp
  have hT1 : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)| ≤ M / 2 := by
    rw [abs_mul]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp; positivity
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      rw [abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * (N : ℝ) ^ 2))]
      calc _ ≤ (1 / (2 * (N : ℝ) ^ 2)) * ((N : ℝ) * N * M) :=
            mul_le_mul_of_nonneg_left hS1 (by positivity)
        _ = M / 2 := by field_simp
  have hT2 : |(1 / (N : ℝ)) * ∑ i : Fin N, ∫ y, g (X i - y) ∂μ| ≤ M := by
    rw [abs_mul]
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp; exact hM0
    · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      rw [abs_of_pos (by positivity : (0:ℝ) < 1 / (N : ℝ))]
      calc _ ≤ (1 / (N : ℝ)) * ((N : ℝ) * M) := mul_le_mul_of_nonneg_left hS2 (by positivity)
        _ = M := by field_simp
  have hT3 : |(1 / 2 : ℝ) * ∫ x, ∫ y, g (x - y) ∂μ ∂μ| ≤ M / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    linarith
  calc _ ≤ |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
        - (1 / (N : ℝ)) * ∑ i : Fin N, ∫ y, g (X i - y) ∂μ| + |(1 / 2 : ℝ) * ∫ x, ∫ y, g (x - y) ∂μ ∂μ| :=
        abs_add_le _ _
    _ ≤ (|(1 / (2 * (N : ℝ) ^ 2)) * ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, g (X i - X j)|
        + |(1 / (N : ℝ)) * ∑ i : Fin N, ∫ y, g (X i - y) ∂μ|) + M / 2 := by
        gcongr; exact abs_sub _ _
    _ ≤ 2 * M := by linarith

theorem modulatedGibbs_prob_of_continuous {g : Torus d → ℝ} (hg : Continuous g) (β : ℝ)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (modulatedGibbs g N β μ) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hg
  set f : Config d N → ℝ := fun X => Real.exp (-β * N * modulatedEnergyKernel g X μ) with hf
  have hmeas : Measurable f := Real.measurable_exp.comp
    (measurable_const.mul (measurable_modulatedEnergyKernel hg μ))
  set t : ℝ := |β| * N * (2 * M) with ht
  have hbd : ∀ X : Config d N, |-β * N * modulatedEnergyKernel g X μ| ≤ t := by
    intro X
    rw [abs_mul, abs_mul, abs_neg, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left (abs_modulatedEnergyKernel_le hM μ X) (by positivity)
  have hint : Integrable f (Measure.pi fun _ : Fin N => μ) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.exp t) (Filter.Eventually.of_forall fun X => ?_)
    rw [hf, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr ((le_abs_self _).trans (hbd X))
  have hK : 0 < gibbsNormalizer g N β μ := by
    have h1 : ∫ _ : Config d N, Real.exp (-t) ∂(Measure.pi fun _ : Fin N => μ) ≤
        gibbsNormalizer g N β μ := by
      unfold gibbsNormalizer
      refine integral_mono (integrable_const _) hint fun X => ?_
      exact Real.exp_le_exp.mpr (by have := hbd X; rw [abs_le] at this; linarith [this.1])
    have h2 : ∫ _ : Config d N, Real.exp (-t) ∂(Measure.pi fun _ : Fin N => μ) = Real.exp (-t) := by simp
    rw [h2] at h1
    exact lt_of_lt_of_le (Real.exp_pos _) h1
  exact modulatedGibbs_isProbabilityMeasure g β μ hK hint

end Prob

section Marg

variable {d N : ℕ} {m : ℝ}

theorem marginal_of_mean {g : Torus d → ℝ} (hg : Continuous g)
    (hm : (d : ℝ) < 2 * m) (hN : 1 ≤ N) (β : ℝ) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussian γ) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : wassersteinE 2 (law (modulatedGibbs g N β μ) (fun X : Config d N => etaE m X μ)) γ ≤
      ENNReal.ofReal δ) :
    wassersteinE 2 (law (modulatedGibbs g N β μ)
      (fun X : Config d N => zetaE m (modulatedGibbs g N β μ) X)) γ ≤ ENNReal.ofReal (2 * δ) := by
  haveI := modulatedGibbs_prob_of_continuous (N := N) hg β μ
  set P := modulatedGibbs g N β μ with hP
  haveI := hγ.1
  have hmeasF := measurable_ofMeasureDiff_empirical hm μ hN
  have hη : Measurable (fun X : Config d N => etaE m X μ) := by
    unfold etaE flucE; exact hmeasF.const_smul (Real.sqrt N)
  set c : NegSobolev d m := Real.sqrt N • NegSobolev.ofMeasureDiff m (meanEmpirical P) μ with hc_def
  have hζ : ∀ X : Config d N, zetaE m P X = etaE m X μ + (-c) := by
    intro X
    rw [eta_eq_zeta_add m hm P μ X hN, hc_def]
    abel
  have hint : Integrable (fun X : Config d N => etaE m X μ) P := by
    refine Integrable.of_bound hη.aestronglyMeasurable (Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d,
      Lattice.jp k.1 ^ (-(2 * m)))) (Filter.Eventually.of_forall fun X => ?_)
    haveI := empirical_isProbabilityMeasure hN X
    unfold etaE flucE
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_left (norm_ofMeasureDiff_le hm (empirical X) μ) (Real.sqrt_nonneg _)
  have hc : ∫ X, etaE m X μ ∂P = c := by
    unfold etaE flucE
    rw [integral_smul, integral_ofMeasureDiff_empirical hm P μ hN hmeasF.aemeasurable]
  have hA : ENNReal.ofReal ‖c‖ ≤ ENNReal.ofReal δ := by
    have hint' : Integrable (fun x : NegSobolev d m => x) (law P (fun X : Config d N => etaE m X μ)) :=
      (integrable_map_measure aestronglyMeasurable_id hη.aemeasurable).2 hint
    have := ofReal_norm_integral_sub_le_wE1 (law P (fun X : Config d N => etaE m X μ)) γ hint'
      ProbabilityTheory.IsGaussian.integrable_id
    have hmean : ∫ x, x ∂(law P (fun X : Config d N => etaE m X μ)) = c := by
      have := integral_map (μ := P) (φ := fun X : Config d N => etaE m X μ)
        (f := fun x : NegSobolev d m => x) hη.aemeasurable continuous_id.aestronglyMeasurable
      rw [show (law P fun X : Config d N => etaE m X μ) = P.map (fun X : Config d N => etaE m X μ) from rfl, this]; exact hc
    have hg0 : ∫ y, y ∂γ = 0 := HilbertCLTAux.gaussian_mean_zero hγ
    rw [hmean, hg0, sub_zero] at this
    exact this.trans ((wassersteinE_one_le_two _ _).trans hδ)
  have h1 : wassersteinE 2 (law P (fun X : Config d N => zetaE m P X))
      (law P (fun X : Config d N => etaE m X μ)) ≤ ENNReal.ofReal ‖c‖ := by
    have := wassersteinE_translate P 2 (by norm_num) (fun X : Config d N => etaE m X μ)
      hη.aemeasurable (-c) 0
    simp only [add_zero, sub_zero, norm_neg] at this
    have e : (fun X : Config d N => zetaE m P X) = fun X => etaE m X μ + -c := funext hζ
    rw [e]; exact this
  calc _ ≤ wassersteinE 2 (law P (fun X : Config d N => zetaE m P X))
        (law P (fun X : Config d N => etaE m X μ)) +
        wassersteinE 2 (law P (fun X : Config d N => etaE m X μ)) γ :=
        wassersteinE_triangle 2 (by norm_num) _ _ _
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := add_le_add (h1.trans hA) hδ
    _ = ENNReal.ofReal (2 * δ) := by
        rw [← ENNReal.ofReal_add hδ0 hδ0]; ring_nf

end Marg


end MarginalAux

section GeneralAux

open StaticLimitAux

variable {d : ℕ}

/-- A continuous kernel with the (nonnegative, summable) Fourier coefficients `ĝ` is the spectral
kernel of `ĝ`. -/
theorem eq_specKernel_of_coeff (g : Torus d → ℝ) (hg : Continuous g) (ĝ : Lattice d → ℝ)
    (hsum : Summable ĝ) (hcoeff : ∀ k, Torus.funFourierCoeff (fun x => (g x : ℂ)) k = ĝ k) :
    g = specKernel ĝ := by
  funext x
  have hco : ∀ k, Torus.fcoef g k = (ĝ k : ℂ) := fun k => by
    have h1 : Torus.funFourierCoeff (fun x => (g x : ℂ)) k = Torus.fcoef g k := by
      simp only [Torus.funFourierCoeff, UnitAddTorus.mFourierCoeff, Torus.fcoef, smul_eq_mul]
      rw [Torus.volume_eq_pi_haar]
      rfl
    rw [← h1, hcoeff k]
  have hs : Summable fun k => ‖Torus.fcoef g k‖ := by
    simpa [hco] using hsum.abs
  have h := Torus.hasSum_fcoef_series hg hs x
  have h2 := Complex.reCLM.hasSum h
  simp only [hco, Complex.reCLM_apply, Complex.ofReal_re] at h2
  unfold specKernel
  refine h2.tsum_eq.symm.trans ?_
  refine tsum_congr fun k => ?_
  rw [Complex.re_ofReal_mul]
  rfl


/-- Mean-field centering as a coordinate of the normalised sum of the summands `Y`. -/
theorem etaE_eq_TJ {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (m : ℝ)
    (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ)
    (hN : 1 ≤ N) (X : Config d N) :
    etaE m X μ = TJ d m (Ssum (Yj m ha0 has μ) N X) := by
  unfold etaE flucE TJ
  rw [fst_Ssum ha0 has μ N X]
  exact etaE_eq_aux hm μ N hN X

/-- The modulated Gibbs law of `η_N` is the tilted law of the normalised sum. -/
theorem law_modulatedGibbs_eq {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (m : ℝ) (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (N : ℕ)
    (hN : 1 ≤ N) (β : ℝ) :
    law (modulatedGibbs (specKernel a) N β μ) (fun X : Config d N => etaE m X μ) =
      (tiltMeasure (tw (qJ d m) β) ((Measure.pi fun _ : Fin N => μ).map (Ssum (Yj m ha0 has μ) N))).map
        (TJ d m) := by
  have hSm : Measurable (Ssum (Yj m ha0 has μ) N) :=
    measurable_Ssum' (continuous_Yj hm ha0 has μ).measurable N
  have hwm : Measurable (tw (qJ d m) β) :=
    Real.measurable_exp.comp (measurable_const.mul (measurable_qJ.pow_const 2))
  have hfun : (fun X : Config d N => etaE m X μ) = fun X => TJ d m (Ssum (Yj m ha0 has μ) N X) :=
    funext fun X => etaE_eq_TJ ha0 has m hm μ N hN X
  unfold law modulatedGibbs gibbsNormalizer
  rw [hfun]
  refine gibbs_map_eq (Measure.pi fun _ : Fin N => μ) (Ssum (Yj m ha0 has μ) N) hSm (TJ d m)
    measurable_TJ (tw (qJ d m) β) hwm (fun v => (tw_pos _ _ v).le) _ (β * specKernel a 0 / 2)
    (fun X => ?_)
  have h := StaticLimitAux.energy_identity m ha0 has μ N hN X
  have hE : modulatedEnergyKernel (specKernel a) X μ = modE (specKernel a) N X μ := rfl
  rw [hE]
  unfold tw qJ
  rw [← Real.exp_add]
  congr 1
  have : -β * (N : ℝ) * modE (specKernel a) N X μ = -β * ((N : ℝ) * modE (specKernel a) N X μ) := by ring
  rw [this, h]
  ring

end GeneralAux

/-! ### Static field limits for compact temperature ranges (work package STAT-01) -/

section StaticLimit

variable {s : ℝ}

/-- A centered Gaussian law `γ` on `E_m = H^{-m}_0(𝕋^d)` with covariance form `C`
on smooth test functions: `Cov_γ(F(φ), F(ψ)) = C(φ, ψ)`. -/
def IsCenteredGaussianWithCov (m : ℝ) (γ : Measure (NegSobolev d m))
    (C : (Torus d → ℝ) → (Torus d → ℝ) → ℝ) : Prop :=
  IsCenteredGaussian γ ∧ ∀ φ ψ : Torus d → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
    ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂γ = C φ ψ

/-! #### The bounded positive spectral kernel of `O:sec:negative` (M L5500-5505) -/

open Classical in
/-- The symbol `O:eq:negative-symbol` (M L5502-5504): `ĝ(0) = 0` and `ĝ(k) = c (2π|k|)^{s-d}`
for `k ≠ 0`, with `s < 0` and a positive spectral normalisation `c > 0`.  This is "not an
analytic continuation of the coefficient of `|x|^{-s}` from `s > 0`" (L5505), so `c` is a free
parameter rather than `rieszConst d s`. -/
def negSpectralCoeff (d : ℕ) (s c : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else c * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ))

/-- The bounded kernel with negative spectral exponent (M L5501-5505): the Fourier series
`g(x) = ∑_k ĝ(k) e^{2πi k·x} = ∑_k ĝ(k) cos(2π k·x)` with the coefficients
`O:eq:negative-symbol` (`negSpectralCoeff d s c`).  For `s < 0` one has
`∑_{k≠0} |k|^{s-d} < ∞`, so the series "converges absolutely and uniformly; thus `g` is
continuous and bounded" (L5505); it is even, positive-definite, has mean zero, and is the
`tsum` of an absolutely summable family, hence an honest value.  (For `s ≥ 0` the family is
not summable and the `tsum` is the junk value `0`; every statement below assumes `s < 0`.) -/
def negSpectralKernel (d : ℕ) (s c : ℝ) (x : Torus d) : ℝ :=
  ∑' k : Lattice d, negSpectralCoeff d s c k * Torus.cosMode k x

theorem negSpectralKernel_eq_spec (d : ℕ) (s c : ℝ) :
    negSpectralKernel d s c = StaticLimitAux.specKernel (negSpectralCoeff d s c) := rfl

theorem negSpectralCoeff_nonneg (d : ℕ) (s : ℝ) {c : ℝ} (hc : 0 ≤ c) (k : Lattice d) :
    0 ≤ negSpectralCoeff d s c k := by
  unfold negSpectralCoeff
  split_ifs
  · exact le_rfl
  · exact mul_nonneg hc (Real.rpow_nonneg (mul_nonneg (by positivity) (by
      unfold Lattice.enorm; exact norm_nonneg _)) _)

theorem summable_negSpectralCoeff (d : ℕ) {s : ℝ} (hs : s < 0) (c : ℝ) :
    Summable (negSpectralCoeff d s c) := by
  have h1 : Summable fun k : NonzeroLattice d => Lattice.enorm k.1 ^ (s - (d : ℝ)) :=
    summable_enorm_rpow_aux (s - (d : ℝ)) (by linarith)
  have h2 : Summable fun k : NonzeroLattice d => negSpectralCoeff d s c k.1 := by
    refine (h1.mul_left (c * (2 * Real.pi) ^ (s - (d : ℝ)))).congr fun k => ?_
    have hk : (k.1 : Lattice d) ≠ 0 := k.2
    unfold negSpectralCoeff
    have hm := Real.mul_rpow (x := 2 * Real.pi) (y := Lattice.enorm k.1) (z := s - (d : ℝ))
      (by positivity) (by unfold Lattice.enorm; exact norm_nonneg _)
    rw [if_neg hk, hm]
    ring
  exact (Function.Injective.summable_iff (g := fun k : NonzeroLattice d => k.1)
    Subtype.val_injective (fun k hk => by
      unfold negSpectralCoeff
      have : k = 0 := by
        by_contra h; exact hk ⟨⟨k, h⟩, rfl⟩
      simp [this])).mp h2

theorem negSpectralCoeff_neg (d : ℕ) (s c : ℝ) (k : Lattice d) :
    negSpectralCoeff d s c (-k) = negSpectralCoeff d s c k := by
  unfold negSpectralCoeff
  have h : Lattice.enorm (-k) = Lattice.enorm k := by simp [Lattice.enorm, Torus.toEuc_neg]
  by_cases hk : k = 0
  · simp [hk]
  · have hk' : (-k) ≠ 0 := neg_ne_zero.mpr hk
    rw [if_neg hk, if_neg hk', h]

theorem negSpectralKernel_continuous (d : ℕ) {s : ℝ} (hs : s < 0) {c : ℝ} (hc : 0 < c) :
    Continuous (negSpectralKernel d s c) :=
  StaticLimitAux.continuous_specKernel (negSpectralCoeff_nonneg d s hc.le)
    (summable_negSpectralCoeff d hs c)

theorem negSpectralKernel_even (d : ℕ) (s c : ℝ) (x : Torus d) :
    negSpectralKernel d s c (-x) = negSpectralKernel d s c x := by
  unfold negSpectralKernel
  refine tsum_congr fun k => ?_
  rw [StaticLimitAux.cosMode_neg_arg]

theorem isProb_withDensityReal {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  refine ⟨?_⟩
  unfold withDensityReal
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hint : Integrable ρ := by
    by_contra h
    have := hρ.integral_one
    rw [integral_undef h] at this
    norm_num at this
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_one]
  simp

/-! #### Proposition 4.21 `M:O:prop:negative` (M L5513-5520)

The operator `K_μ f = P_μ[g*(fμ)]` of `O:eq:negative-operator` (L5507-5511) is `Kop g μ`, with
`P_μ f = f - μ(f)` = `projMean μ`; for the bounded kernel `g = negSpectralKernel d s c` and a
probability density `μ = ρ dx` that is *not necessarily bounded* (L5507), `g*(fμ)` is an honest
Bochner integral for every `f ∈ L²(μ) ⊆ L¹(μ)`, and `K_μ` is bounded, nonnegative and
self-adjoint on `L²_0(μ)` (L5511), so the response equation `h + βK_μh = P_μψ`, `μ(h) = 0`
(`IsResponse`) has a unique solution for every `β ≥ 0` and `responseInverse` is not a junk
witness.  The covariance `O:eq:negative-cov` (L5515-5518),
`C_{β,μ}(φ,ψ) = ⟨P_μφ, (I+βK_μ)^{-1}P_μψ⟩_{L²(μ)}`, is `susceptibilityCov g (withDensityReal ρ) β`.
The modulated Gibbs preparation `Q_{N,β}(μ)` is `modulatedGibbs g N β (withDensityReal ρ)`;
for this bounded kernel all three terms of the modulated energy and the normaliser are honest
for every probability density.

`W_2`-convergence of laws on `H^{-m}_0(𝕋^d)` (`NegSobolev d m`, `m > d/2`) is expressed as in
`static_field_limit_general`: for every `ε > 0` there is a threshold `N₀` such that for
`N ≥ N₀` the `W_2` distance (`wassersteinE 2`, in `ℝ≥0∞`) between the law of the fluctuation
field and the centered Gaussian law with the stated covariance (`IsCenteredGaussianWithCov`,
covariance pinned on smooth test functions) is at most `ε`.  Quantifying `β ∈ [0,B]` and the
density `ρ` *after* `N₀` is the uniformity "for `0 ≤ β ≤ B`" (L5514) and "over the reference
probability densities `μ`" (L5519).  The Gaussian targets exist by
`exists_susceptibility_gaussian`. -/

/-- Proposition 4.21, last sentence: the same holds for any continuous positive-definite
translation-invariant kernel `g` with summable nonnegative Fourier coefficients. -/
theorem static_field_limit_general (g : Torus d → ℝ) (hg : Continuous g) (hev : ∀ x, g (-x) = g x)
    (ĝ : Lattice d → ℝ) (hĝ : ∀ k, 0 ≤ ĝ k) (hsum : Summable ĝ)
    (hcoeff : ∀ k, Torus.funFourierCoeff (fun x => (g x : ℂ)) k = ĝ k) (m : ℝ)
    (hm : (d : ℝ) / 2 < m) (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ ρ : Torus d → ℝ,
      IsProbDensity ρ → ∀ γ : Measure (NegSobolev d m),
        IsCenteredGaussianWithCov m γ (susceptibilityCov g (withDensityReal ρ) β) →
        wassersteinE 2
          (law (modulatedGibbs g N β (withDensityReal ρ))
            (fun X : Config d N => etaE m X (withDensityReal ρ)))
          γ ≤ ENNReal.ofReal ε := by
  intro ε hε
  have hm' : (d : ℝ) < 2 * m := by linarith
  have hgeq : g = StaticLimitAux.specKernel ĝ := eq_specKernel_of_coeff g hg ĝ hsum hcoeff
  subst hgeq
  obtain ⟨N₀, hN₀⟩ := StaticLimitAux.joint_transfer hm' hĝ hsum B hB ε hε
  refine ⟨max N₀ 1, fun N hN β hβ ρ hρ γ hγ => ?_⟩
  have hN₀' : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hprob := isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  have hmem : MemLp (StaticLimitAux.Yj m hĝ hsum μ) 2 μ :=
    MemLp.of_bound (StaticLimitAux.continuous_Yj hm' hĝ hsum μ).aestronglyMeasurable
      (StaticLimitAux.Mconst d m ĝ)
      (Filter.Eventually.of_forall fun x => StaticLimitAux.norm_Yj_le hm' hĝ hsum μ x)
  obtain ⟨Γ, hΓp, hΓg, hΓcov⟩ := exists_centeredGaussian_of_traceClass
    (ProbabilityTheory.covarianceBilin (law μ (StaticLimitAux.Yj m hĝ hsum μ)))
    (isTraceClassCov_covarianceBilin μ (StaticLimitAux.Yj m hĝ hsum μ) hmem
      (StaticLimitAux.integral_Yj_eq_zero hm' hĝ hsum μ)).1
  have hcov : ∀ x y, ProbabilityTheory.covarianceBilin Γ x y =
      ProbabilityTheory.covarianceBilin (μ.map (StaticLimitAux.Yj m hĝ hsum μ)) x y :=
    fun x y => hΓcov x y
  have h1 := hN₀ N hN₀' μ β hβ Γ hΓg hcov
  obtain ⟨hGt, hCt⟩ := StaticLimitAux.tilted_marginal_cov hm' hĝ hsum μ hβ.1 Γ hΓg hcov
  have hγeq : (StaticLimitAux.tiltMeasure (StaticLimitAux.tw (StaticLimitAux.qJ d m) β) Γ).map
      (StaticLimitAux.TJ d m) = γ := by
    refine StaticLimitAux.gaussian_ext_of_cov _ _ hGt hγ.1 ?_
    rw [hCt]
    exact (StaticLimitAux.covarianceBilin_eq_of_smooth _ γ hγ.1 (fun φ ψ hφ hψ => by
      rw [StaticLimitAux.Cmap_avec μ hĝ hsum hβ.1 hm' hφ hψ]; exact hγ.2 φ ψ hφ hψ)).symm
  rw [law_modulatedGibbs_eq hĝ hsum m hm' μ N hN1 β, ← hγeq,
    HilbertCLTAux.wassersteinE_comm]
  exact h1

/-- Proposition 4.21 `M:O:prop:negative` (M L5513-5520), first and third sentences, mean-field
centering `√N(μ_N - μ)` (`etaE`): for `m > d/2` and `B < ∞`, with `X_N ∼ Q_{N,β}(μ)` for the
bounded kernel `negSpectralKernel d s c` (`s < 0`, `c > 0`), the laws of `√N(μ_N - μ)` converge
in `W_2` on `H^{-m}_0(𝕋^d)` to the centered Gaussian laws with covariance `C_{β,μ}`
(`O:eq:negative-cov`), uniformly for `0 ≤ β ≤ B` and uniformly over all reference probability
densities `μ` (not necessarily bounded).  Special case `ĝ = negSpectralCoeff d s c` of
`static_field_limit_general` (the last sentence of the proposition). -/
theorem static_field_limit_mean (hd : 1 ≤ d) (hs : s < 0) (c : ℝ) (hc : 0 < c) (m : ℝ)
    (hm : (d : ℝ) / 2 < m) (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ ρ : Torus d → ℝ,
      IsProbDensity ρ → ∀ γ : Measure (NegSobolev d m),
        IsCenteredGaussianWithCov m γ
          (susceptibilityCov (negSpectralKernel d s c) (withDensityReal ρ) β) →
        wassersteinE 2
          (law (modulatedGibbs (negSpectralKernel d s c) N β (withDensityReal ρ))
            (fun X : Config d N => etaE m X (withDensityReal ρ)))
          γ ≤ ENNReal.ofReal ε := by
  intro ε hε
  have ha0 := negSpectralCoeff_nonneg d s hc.le
  have has := summable_negSpectralCoeff d hs c
  refine static_field_limit_general (negSpectralKernel d s c) (negSpectralKernel_continuous d hs hc)
    (negSpectralKernel_even d s c) (negSpectralCoeff d s c) ha0 has (fun k => ?_) m hm B hB ε hε
  have h1 : Torus.funFourierCoeff (fun x => (negSpectralKernel d s c x : ℂ)) k =
      Torus.fcoef (negSpectralKernel d s c) k := by
    simp only [Torus.funFourierCoeff, UnitAddTorus.mFourierCoeff, Torus.fcoef, smul_eq_mul]
    rw [Torus.volume_eq_pi_haar]
    rfl
  rw [h1, negSpectralKernel_eq_spec]
  exact_mod_cast StaticLimitAux.fcoef_specKernel ha0 has (negSpectralCoeff_neg d s c) k

/-- Proposition 4.21, existence of the Gaussian targets (M L5545: "The inverse is bounded above
by `I`, so these covariances define Gaussian fields in the displayed negative Sobolev space"):
for the bounded kernel `negSpectralKernel d s c` (`s < 0`, `c > 0`), every `β ≥ 0`, every
probability density `ρ` (not necessarily bounded) and every `m > d/2`, there is a centered
Gaussian probability law on `H^{-m}_0(𝕋^d)` with covariance `C_{β,μ}` (`O:eq:negative-cov`) on
smooth test functions. -/
theorem exists_susceptibility_gaussian (hd : 1 ≤ d) (hs : s < 0) (c : ℝ) (hc : 0 < c) (m : ℝ)
    (hm : (d : ℝ) / 2 < m) (β : ℝ) (hβ : 0 ≤ β) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) :
    ∃ γ : Measure (NegSobolev d m), IsProbabilityMeasure γ ∧
      IsCenteredGaussianWithCov m γ
        (susceptibilityCov (negSpectralKernel d s c) (withDensityReal ρ) β) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨γ, hp, hg, hcov⟩ := StaticLimitAux.exists_gauss_spec (withDensityReal ρ)
    (negSpectralCoeff_nonneg d s hc.le) (summable_negSpectralCoeff d hs c) hβ
    (by linarith : (d : ℝ) < 2 * m)
  exact ⟨γ, hp, hg, hcov⟩

/-- Proposition 4.21, second sentence (M L5519): "The same conclusion holds with exact
first-marginal centering", i.e. for `√N(μ_N - m_N)` (`zetaE`) with `m_N = E[μ_N]` the first
marginal of `Q_{N,β}(μ)` (`meanEmpirical_eq_firstMarginal`, `modulatedGibbs_isExchangeable`),
again uniformly for `0 ≤ β ≤ B` and over all reference probability densities `μ`. -/
theorem static_field_limit_marginal (hd : 1 ≤ d) (hs : s < 0) (c : ℝ) (hc : 0 < c) (m : ℝ)
    (hm : (d : ℝ) / 2 < m) (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ ρ : Torus d → ℝ,
      IsProbDensity ρ → ∀ γ : Measure (NegSobolev d m),
        IsCenteredGaussianWithCov m γ
          (susceptibilityCov (negSpectralKernel d s c) (withDensityReal ρ) β) →
        wassersteinE 2
          (law (modulatedGibbs (negSpectralKernel d s c) N β (withDensityReal ρ))
            (fun X : Config d N =>
              zetaE m (modulatedGibbs (negSpectralKernel d s c) N β (withDensityReal ρ)) X))
          γ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := static_field_limit_mean hd hs c hc m hm B hB (ε / 2) (by positivity)
  refine ⟨max N₀ 1, fun N hN β hβ ρ hρ γ hγ => ?_⟩
  have hprob := isProb_withDensityReal hρ
  have h := marginal_of_mean (N := N) (negSpectralKernel_continuous d hs hc)
    (by linarith : (d : ℝ) < 2 * m) (le_trans (le_max_right _ _) hN) β (withDensityReal ρ) γ hγ.1
    (δ := ε / 2) (by positivity)
    (hN₀ N (le_trans (le_max_left _ _) hN) β hβ ρ hρ γ hγ)
  have e : 2 * (ε / 2) = ε := by ring
  rwa [e] at h

/-! #### Corollary 4.22 `M:O:cor:negative-canonical` (M L5559-5561)

"For a fixed continuous periodic `V`, the static conclusion of Proposition 4.21 holds for the
canonical Gibbs ensemble, centered at its thermal equilibrium measure or its exact first
marginal, uniformly for `β ∈ [0,B]`.  At `β = 0` the canonical ensemble is the Haar product
measure."  The canonical ensemble `P_{N,β}` (`H:eq:canonical`, Hamiltonian
`∑_i V(x_i) + N⁻¹∑_{i<j} g(x_i-x_j)`) is `canonicalGibbs g V N β`; its thermal equilibrium
measure `μ_β = ρ_β dx` is a solution of the thermal equation `IsThermalDensity g V β ρ`
(`H:eq:thermal-equation`), whose existence, positivity and uniqueness for this bounded kernel
are asserted by the corollary's proof (L5563) and recorded in `thermal_negSpectral_exists_unique`.
`P_{N,β} = Q_{N,β}(μ_β)` is `canonicalGibbs_eq_modulatedGibbs`, and the `β = 0` sentence is
`canonicalGibbs_zero`. -/

/-- Corollary 4.22, the thermal equilibrium measure presupposed by "its thermal equilibrium
measure" (M L5560, L5563): for a continuous periodic `V`, the bounded kernel
`negSpectralKernel d s c` (`s < 0`, `c > 0`) and every `β ≥ 0`, the free energy
`∫ρ log ρ + β∫Vρ + (β/2)∬ g ρ ρ` has a unique minimiser, which is a positive Gibbs density
solving `ρ_β ∝ e^{-β(V + g*ρ_β)}`: there is a positive thermal density, and it is the only thermal
density (for this bounded kernel every thermal density is bounded above and below, hence a
finite-energy critical point of the strictly convex functional). -/
theorem thermal_negSpectral_exists_unique (hd : 1 ≤ d) (hs : s < 0) (c : ℝ) (hc : 0 < c)
    (V : Torus d → ℝ) (hV : Continuous V) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ ρ : Torus d → ℝ, IsThermalDensity (negSpectralKernel d s c) V β ρ ∧ (∀ x, 0 < ρ x) ∧
      ∀ ρ' : Torus d → ℝ, IsThermalDensity (negSpectralKernel d s c) V β ρ' → ρ' = ρ := by
  have ha0 := negSpectralCoeff_nonneg d s hc.le
  have has := summable_negSpectralCoeff d hs c
  obtain ⟨ρ, hρc, hρpos, hρint, hρeq⟩ := StaticLimitAux.exists_thermal_density ha0 has hV hβ
  refine ⟨ρ, ⟨⟨fun x => (hρpos x).le, hρc.measurable, hρint⟩, ?_⟩, hρpos, ?_⟩
  · intro x; exact hρeq x
  · rintro ρ' ⟨⟨h0, hm, hi⟩, heq'⟩
    exact StaticLimitAux.thermal_unique ha0 has V hV β hβ ρ' ρ h0 hm hi
      (fun x => (hρpos x).le) hρc.measurable hρint heq' hρeq

/-- Corollary 4.22 `M:O:cor:negative-canonical` (M L5559-5561), centering at the thermal
equilibrium measure: for a fixed continuous periodic `V`, the bounded kernel
`negSpectralKernel d s c` (`s < 0`, `c > 0`), `m > d/2` and `B < ∞`, if `X_N ∼ P_{N,β}` is the
canonical Gibbs ensemble and `μ_β = ρ_β dx` its thermal equilibrium measure
(`IsThermalDensity`), the laws of `√N(μ_N - μ_β)` converge in `W_2` on `H^{-m}_0(𝕋^d)` to the
centered Gaussian laws with covariance `C_{β,μ_β}` (`O:eq:negative-cov`), uniformly for
`β ∈ [0,B]`. -/
theorem static_field_limit_canonical (hd : 1 ≤ d) (hs : s < 0) (c : ℝ) (hc : 0 < c) (m : ℝ)
    (hm : (d : ℝ) / 2 < m) (V : Torus d → ℝ) (hV : Continuous V) (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ ρ : Torus d → ℝ,
      IsThermalDensity (negSpectralKernel d s c) V β ρ → ∀ γ : Measure (NegSobolev d m),
        IsCenteredGaussianWithCov m γ
          (susceptibilityCov (negSpectralKernel d s c) (withDensityReal ρ) β) →
        wassersteinE 2
          (law (canonicalGibbs (negSpectralKernel d s c) V N β)
            (fun X : Config d N => etaE m X (withDensityReal ρ)))
          γ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := static_field_limit_mean hd hs c hc m hm B hB ε hε
  refine ⟨N₀, fun N hN β hβ ρ hρ γ hγ => ?_⟩
  have hprob := isProb_withDensityReal hρ.1
  have heq := canonicalGibbs_eq_modulatedGibbs (N := N) (negSpectralKernel d s c) V β ρ hρ
    (negSpectralKernel_even d s c) (fun x => by
      refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
      exact (negSpectralKernel_continuous d hs hc).comp (continuous_const.sub continuous_id))
  rw [heq]
  exact hN₀ N hN β hβ ρ hρ.1 γ hγ

/-- Corollary 4.22 (M L5560), centering at the exact first marginal `m_{N,β}` of the canonical
ensemble (`zetaE`; `meanEmpirical_eq_firstMarginal`): same data and same Gaussian targets as
`static_field_limit_canonical`, for `√N(μ_N - m_{N,β})`, uniformly for `β ∈ [0,B]`. -/
theorem static_field_limit_canonical_marginal (hd : 1 ≤ d) (hs : s < 0) (c : ℝ) (hc : 0 < c)
    (m : ℝ) (hm : (d : ℝ) / 2 < m) (V : Torus d → ℝ) (hV : Continuous V) (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ ρ : Torus d → ℝ,
      IsThermalDensity (negSpectralKernel d s c) V β ρ → ∀ γ : Measure (NegSobolev d m),
        IsCenteredGaussianWithCov m γ
          (susceptibilityCov (negSpectralKernel d s c) (withDensityReal ρ) β) →
        wassersteinE 2
          (law (canonicalGibbs (negSpectralKernel d s c) V N β)
            (fun X : Config d N => zetaE m (canonicalGibbs (negSpectralKernel d s c) V N β) X))
          γ ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := static_field_limit_marginal hd hs c hc m hm B hB ε hε
  refine ⟨N₀, fun N hN β hβ ρ hρ γ hγ => ?_⟩
  have hprob := isProb_withDensityReal hρ.1
  have heq := canonicalGibbs_eq_modulatedGibbs (N := N) (negSpectralKernel d s c) V β ρ hρ
    (negSpectralKernel_even d s c) (fun x => by
      refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
      exact (negSpectralKernel_continuous d hs hc).comp (continuous_const.sub continuous_id))
  rw [heq]
  exact hN₀ N hN β hβ ρ hρ.1 γ hγ

/-- Corollary 4.22, last sentence: at `β = 0` the canonical ensemble is the Haar product
measure. -/
theorem canonicalGibbs_zero (g V : Torus d → ℝ) :
    canonicalGibbs g V N 0 = (volume : Measure (Config d N)) := by
  unfold canonicalGibbs canonicalPartition
  simp

/-- Theorem 2.9, last sentence (line 992): if `V` is constant, `m_{N,β} = μ_β = dx` exactly,
for every `N` and `s < d`. -/
theorem firstMarginal_canonicalGibbs_const (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (c β : ℝ) (hβ : 0 < β) (hN : 1 ≤ N) :
    firstMarginal (canonicalGibbs (periodicRiesz d s) (fun _ => c) N β) = volume := by
  set g := periodicRiesz d s with hg
  set P := canonicalGibbs g (fun _ => c) N β with hP
  have hint := integrable_exp_canonical (N := N) hd hs0 hsd c β hβ.le
  have hZ : 0 < canonicalPartition g (fun _ => c) N β := by
    unfold canonicalPartition
    refine (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hint).mpr ?_
    have : Function.support (fun X : Config d N =>
        Real.exp (-β * canonicalHamiltonian g (fun _ => c) X)) = Set.univ := by
      ext X; simp [(Real.exp_pos _).ne']
    rw [this]; simp
  have hPuniv : P Set.univ = 1 := by
    rw [hP]; unfold canonicalGibbs
    rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      smul_eq_mul]
    have := ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)
    unfold canonicalPartition at hZ ⊢
    rw [← this]
    exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top
  haveI : IsProbabilityMeasure P := ⟨hPuniv⟩
  have hinv : ∀ t : Torus d, P.map (shiftEquiv t : Config d N ≃ᵐ Config d N) = P := by
    intro t
    rw [hP]; unfold canonicalGibbs
    rw [Measure.map_smul]
    congr 1
    refine map_withDensity_of_measurePreserving (shiftEquiv t) volume (shiftEquiv_measurePreserving t) _ ?_
    intro X
    have := canonicalHamiltonian_shift g c t X
    simp only [this]
    exact (shiftEquiv t).measurable.aemeasurable
  have h0 : 0 < N := hN
  unfold firstMarginal
  rw [dif_pos h0]
  set e0 : Config d N → Torus d := fun X => X ⟨0, h0⟩ with he0
  have he0m : Measurable e0 := measurable_pi_apply _
  haveI : (P.map e0).IsAddLeftInvariant := by
    refine ⟨fun t => ?_⟩
    have hm : Measurable (fun x : Torus d => t + x) := measurable_const.add measurable_id
    rw [Measure.map_map hm he0m]
    have : ((fun x : Torus d => t + x) ∘ e0) = e0 ∘ (shiftEquiv t : Config d N ≃ᵐ Config d N) := by
      funext X; rfl
    rw [this, ← Measure.map_map he0m (shiftEquiv t).measurable, hinv t]
  exact eq_volume_of_addLeftInvariant _ measure_univ

end StaticLimit

end HRS
