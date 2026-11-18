/-
# HRS.Equilibrium.PairCorrection — critical pair correction (EQ-01b)

Section 4 of the main manuscript, results 4.10-4.16 at the critical exponent `s = d/2`
(source lines 4449-4934):

* Lemma 4.10 `M:Q:lem:pin` (pointwise comparison after finitely many pins),
* Lemma 4.11 `M:Q:lem:integrals` (critical integrals with retained repulsion),
* Proposition 4.12 `M:Q:prop:moments` (pair and three-particle moments),
* Proposition 4.13 `M:Q:prop:poisson` (two-particle Poisson equation),
* Lemma 4.15 `M:Q:lem:triple-canonical` (canonical projections, singular bounds),
* Proposition 4.16 `M:Q:prop:normal-form` (exact normal form at finite `N`).

Proposition 4.17 (`M:Q:prop:integrated`) is a statement about the stationary particle process
and is not specified here (dynamics). Lemma 4.14 belongs to ADJ-01.

Standing hypotheses (source lines 4454, 4711): `d ≥ 2`, `s = d/2`, fixed `β > 0`, smooth `V`,
`μ = μ_β = ρ dx` the thermal equilibrium measure of `V`, `P_{N,β}` the canonical Gibbs law
(`canonicalGibbs`), `λ = β/N`, `δ_N = log(eN)/N`, `L_N = log(eN)`.

The weak calibrated reference `R_N` of the source is a proof object built from a heat
decomposition `g = q + k + c`. Lemma 4.10 is specified for the explicit family of weak
reference laws `pinnedReference` attached to any admissible `q` and any bounded common field
(source lines 4459-4473); its last display additionally takes the calibration identity
`Q:eq:calibration` and the two imported reference inputs of `Q:eq:reference-input` as
hypotheses. In Lemma 4.11 the retained repulsion `e^{-cλq}` is written with `g_+ = g + c'`
instead of `q`; the two differ by a bounded function, so the factors are comparable and the
statements are equivalent up to constants.
-/
import HRS.Equilibrium.PoleCavity
import HRS.External.WeakSpec

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ}

/-! ### Envelopes and statistics (source lines 4554-4605) -/

/-- `r(x,y) = min{1, |x - y|}` with the periodic Euclidean distance. -/
def rTrunc (x y : Torus d) : ℝ := min 1 (Torus.eucDist x y)

/-- `w(x,y) = 1 + r(x,y)^{-s}` (`Q:eq:envelopes`). Only used off the diagonal. -/
def wEnv (s : ℝ) (x y : Torus d) : ℝ := 1 + rTrunc x y ^ (-s)

/-- `ℓ(x,y) = 1 + log(1/r(x,y))` (`Q:eq:envelopes`). Only used off the diagonal. -/
def ellEnv (x y : Torus d) : ℝ := 1 + Real.log (1 / rTrunc x y)

/-- `L_N = log(eN)`. -/
def logEN (N : ℕ) : ℝ := Real.log (Real.exp 1 * N)

/-- Ordered deleted-diagonal pair sum `∑_{i≠j} b(x_i, x_j)`. -/
def pairSumOrdered {N : ℕ} (b : Torus d → Torus d → ℝ) (X : Config d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, b (X i) (X j)

/-- Sum over ordered triples of distinct labels `∑_{i,j,k distinct} g₃(x_i, x_j, x_k)`. -/
def tripleSum {N : ℕ} (g3 : Torus d → Torus d → Torus d → ℝ) (X : Config d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j, g3 (X i) (X j) (X k)

/-- `F_N(ψ) = N^{-3/2} ∑_{i≠j} ψ(x_i, x_j)` (`Q:eq:F-statistic`, source line 4602). -/
def Fstat {N : ℕ} (ψ : Torus d → Torus d → ℝ) (X : Config d N) : ℝ :=
  (N : ℝ) ^ (-(3 / 2 : ℝ)) * pairSumOrdered ψ X

/-- The gradient `∇_i Φ(X)` of a configuration function in the `i`-th particle. -/
def configGrad {N : ℕ} (Φ : Config d N → ℝ) (X : Config d N) (i : Fin N) : Euc d :=
  gradient (fun u : Euc d => Φ (Function.update X i (X i + Torus.mk u))) 0

/-- The Laplacian `Δ_i Φ(X)` in the `i`-th particle. -/
def configLap {N : ℕ} (Φ : Config d N → ℝ) (X : Config d N) (i : Fin N) : ℝ :=
  Laplacian.laplacian (fun u : Euc d => Φ (Function.update X i (X i + Torus.mk u))) 0

/-- `ψ` is symmetric. -/
def IsSymmPair (ψ : Torus d → Torus d → ℝ) : Prop := ∀ x y, ψ x y = ψ y x

/-- `ψ` is canonical (Hoeffding centred under `μ`, source line 4561): every row is
`μ`-integrable with integral zero. For a symmetric kernel this is centering in each variable. -/
def IsCanonicalPair (μ : Measure (Torus d)) (ψ : Torus d → Torus d → ℝ) : Prop :=
  ∀ x, Integrable (ψ x) μ ∧ ∫ y, ψ x y ∂μ = 0

/-- `g₃` is symmetric under all permutations of its three variables. -/
def IsSymmTriple (g3 : Torus d → Torus d → Torus d → ℝ) : Prop :=
  ∀ x y z, g3 x y z = g3 y x z ∧ g3 x y z = g3 x z y

/-- `g₃` is canonical: integral zero in the last variable for `x ≠ y` (for a symmetric `g₃`
this is centering in every variable; on `x = y` the triple envelope is not integrable). -/
def IsCanonicalTriple (μ : Measure (Torus d)) (g3 : Torus d → Torus d → Torus d → ℝ) : Prop :=
  ∀ x y, x ≠ y → Integrable (g3 x y) μ ∧ ∫ z, g3 x y z ∂μ = 0

/-- The periodic lift of a two-variable kernel to `ℝ^d × ℝ^d`. -/
def lift2 (ψ : Torus d → Torus d → ℝ) : Euc d × Euc d → ℝ :=
  fun p => ψ (Torus.mk p.1) (Torus.mk p.2)

/-- The (open) off-diagonal set in the covering space. -/
def offDiag (d : ℕ) : Set (Euc d × Euc d) := {p | Torus.mk p.1 ≠ Torus.mk p.2}

/-- The size and regularity conditions `Q:eq:psi-size` (source lines 4609-4613) with constant
`K`: smooth off the diagonal, `|ψ| ≤ K{1 + r^{2-s} + 1_{s=2}|log r|}`, `|∇ψ| ≤ K(1 + r^{1-s})`,
`|D²ψ| ≤ K(1 + r^{-s})` (full derivatives in `(x,y)`). -/
structure PsiSize (s K : ℝ) (ψ : Torus d → Torus d → ℝ) : Prop where
  smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)
  size : ∀ x y, x ≠ y →
    |ψ x y| ≤ K * (1 + rTrunc x y ^ (2 - s) + if s = 2 then |Real.log (rTrunc x y)| else 0)
  grad : ∀ p ∈ offDiag d,
    ‖fderiv ℝ (lift2 ψ) p‖ ≤ K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (1 - s))
  hess : ∀ p ∈ offDiag d,
    ‖iteratedFDeriv ℝ 2 (lift2 ψ) p‖ ≤ K * (1 + rTrunc (Torus.mk p.1) (Torus.mk p.2) ^ (-s))

/-! ### The weak reference (source lines 4454-4481) -/

/-- The weak reference law with `n` free coordinates, pair kernel `q`, common one-body field
`field` and external pins `A` (`Q:eq:reference-law` and the pinned laws `R_n^A`, source
lines 4459-4473): `∝ exp[∑_i field(y_i) - λ∑_{i<j} q(y_i - y_j) - λ∑_{i,a} q(y_i - a)] dμ^{⊗n}`. -/
def pinnedReference (q field : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam : ℝ) {a : ℕ}
    (A : Fin a → Torus d) : Measure (Config d n) :=
  tiltMeasure (Measure.pi fun _ : Fin n => μ)
    fun Y => ∑ i, field (Y i) - lam * pairSum q Y - lam * ∑ i, ∑ k, q (Y i - A k)

/-- The coordinate marginal `Law(y_i)`. -/
def coordMarginal {n : ℕ} (P : Measure (Config d n)) (i : Fin n) : Measure (Torus d) :=
  P.map fun Y => Y i

/-- The first marginal `π_N = R_N^{(1)}` of the unpinned `N`-particle weak reference with common
field `β q*μ + h`. -/
def weakRefMarginal (q h : Torus d → ℝ) (μ : Measure (Torus d)) (β : ℝ) (N : ℕ) :
    Measure (Torus d) :=
  firstMarginal (pinnedReference q (fun x => β * convMeasure q μ x + h x) μ N (β / N)
    (Fin.elim0 : Fin 0 → Torus d))

section Critical

variable {s : ℝ}

/-! ### Bridge to the weak-specification layer `HRS.External.WeakSpec`

`pinnedReference q (β q*μ + h) μ n (β/N) A` is the explicit pinned ensemble `pinnedLaw V (β/N) n A`
of the abstract layer, for the weak potential `V` with `φ = β q*μ + h`, `V.q x y = q(x - y)`,
`γ = γ₀`, `M = βγ₀ + 1`, `M' = 1` (`exists_weakPotential`, `pinnedReference_eq_pinnedLaw`). -/

theorem measurable_sub_torus : Measurable (fun p : Torus d × Torus d => p.1 - p.2) := by
  fun_prop

/-- Weak potential attached to an admissible pair kernel `q` and a bounded common field. -/
theorem exists_weakPotential (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (β γ₀ : ℝ)
    (hγ₀ : 0 < γ₀) (q h : Torus d → ℝ) (hq : Measurable q) (hq0 : ∀ z, 0 ≤ q z)
    (hqe : ∀ z, q (-z) = q z) (hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂μ ≤ ENNReal.ofReal γ₀)
    (hh : Measurable h) (hh1 : ∀ x, |h x| ≤ 1) (hβ : 0 < β) :
    ∃ V : External.WeakPotential μ, (∀ x y, V.q x y = q (x - y)) ∧
      V.φ = (fun x => β * convMeasure q μ x + h x) ∧ V.γ = γ₀ ∧ V.M = β * γ₀ + 1 ∧ V.M' = 1 := by
  have hmq : ∀ x, Measurable (fun y => q (x - y)) :=
    fun x => hq.comp (measurable_const.sub measurable_id)
  have hint : ∀ x, Integrable (fun y => q (x - y)) μ := by
    intro x
    refine ⟨(hmq x).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have : ∀ y, ‖q (x - y)‖ₑ = ENNReal.ofReal (q (x - y)) := fun y => by
      rw [Real.enorm_eq_ofReal (hq0 _)]
    simp_rw [this]
    exact (hrow x).trans_lt ENNReal.ofReal_lt_top
  have hrowR : ∀ x, ∫ y, q (x - y) ∂μ ≤ γ₀ := by
    intro x
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun y => hq0 _)
      (hmq x).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal hγ₀.le (hrow x)
  have hconv0 : ∀ x, 0 ≤ convMeasure q μ x := fun x => integral_nonneg fun y => hq0 _
  have hconv1 : ∀ x, convMeasure q μ x ≤ γ₀ := hrowR
  have hmconv : Measurable (convMeasure q μ) := by
    unfold convMeasure
    have : StronglyMeasurable (fun p : Torus d × Torus d => q (p.1 - p.2)) :=
      (hq.comp measurable_sub_torus).stronglyMeasurable
    exact this.integral_prod_right'.measurable
  have hmφ : Measurable (fun x => β * convMeasure q μ x + h x) := (hmconv.const_mul β).add hh
  have hφb : ∀ x, |β * convMeasure q μ x + h x| ≤ β * γ₀ + 1 := by
    intro x
    have := hconv0 x; have := hconv1 x; have := hh1 x
    rw [abs_le] at *
    constructor <;> nlinarith
  refine ⟨⟨fun x => β * convMeasure q μ x + h x, fun x y => q (x - y), β * γ₀ + 1, 1, γ₀,
    hmφ, ?_, fun x y => hq0 _, fun x y => ?_, hγ₀.le, fun x => (le_abs_self _).trans (hφb x), ?_, ?_,
    fun x => hint x, fun x => hrowR x⟩, fun x y => rfl, rfl, rfl, rfl, rfl⟩
  · exact (hq.comp measurable_sub_torus)
  · rw [← hqe (x - y)]; congr 1; abel
  · exact Integrable.of_bound hmφ.aestronglyMeasurable (β * γ₀ + 1)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hφb x)
  · have hib : ∀ x, ‖β * convMeasure q μ x + h x‖ ≤ β * γ₀ + 1 := fun x => by
      rw [Real.norm_eq_abs]; exact hφb x
    have : ∫ x, (-1 : ℝ) ∂μ ≤ ∫ x, (β * convMeasure q μ x + h x) ∂μ := by
      refine integral_mono (integrable_const _)
        (Integrable.of_bound hmφ.aestronglyMeasurable (β * γ₀ + 1)
          (Filter.Eventually.of_forall hib)) fun x => ?_
      have := hconv0 x; have := hh1 x
      rw [abs_le] at this
      nlinarith
    simpa using this

/-- `pinnedReference` is the pinned ensemble `pinnedLaw` of the weak-specification layer. -/
theorem pinnedReference_eq_pinnedLaw (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (V : External.WeakPotential μ) (q field : Torus d → ℝ) (hVq : ∀ x y, V.q x y = q (x - y))
    (hfield : V.φ = field) (n : ℕ) {lam : ℝ} (hlam : 0 ≤ lam) {a : ℕ} (A : Fin a → Torus d) :
    pinnedReference q field μ n lam A = External.pinnedLaw V lam n A := by
  open External in
  have hψ := isField_pinField V hlam A
  have hexp : ∀ Y : Fin n → Torus d,
      ∑ i, field (Y i) - lam * pairSum q Y - lam * ∑ i, ∑ k, q (Y i - A k)
        = ∑ i, External.pinField V lam A (Y i) - lam * External.pairEnergy V Y := by
    intro Y
    rw [External.pairEnergy_eq_sum_lt]
    unfold External.pinField pairSum
    simp_rw [hVq, hfield]
    have hI : ∀ i : Fin n, (Finset.univ.filter (fun j : Fin n => i < j)) = Finset.Ioi i := by
      intro i; ext j; simp
    simp_rw [hI]
    rw [Finset.sum_sub_distrib]
    simp_rw [← Finset.mul_sum]
    ring
  unfold pinnedReference tiltMeasure External.pinnedLaw External.fieldLaw
  simp_rw [hexp]
  unfold External.fieldDensity External.fieldWeight External.fieldNorm
  have hc : (∫⁻ y, ENNReal.ofReal (Real.exp (∑ i, External.pinField V lam A (y i)
        - lam * External.pairEnergy V y)) ∂(Measure.pi fun _ : Fin n => μ))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (External.fieldNorm_pos hψ.measurable V lam n).ne'
  refine (withDensity_smul' _ _ hc).symm.trans ?_
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

theorem pi_map_eval_prob (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (n : ℕ) (i : Fin n) :
    (Measure.pi fun _ : Fin n => μ).map (fun Y => Y i) = μ := by
  have := (measurePreserving_eval (fun _ : Fin n => μ) i).map_eq
  simpa using this

/-- Every coordinate marginal of a tilted product law is absolutely continuous w.r.t. `μ`
(the two `≪` conjuncts of Lemma 4.10). -/
theorem coordMarginal_tilt_ac (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (n : ℕ)
    (w : Config d n → ℝ) (i : Fin n) :
    coordMarginal (tiltMeasure (Measure.pi fun _ : Fin n => μ) w) i ≪ μ := by
  have h1 : tiltMeasure (Measure.pi fun _ : Fin n => μ) w ≪ Measure.pi fun _ : Fin n => μ := by
    unfold tiltMeasure
    exact (withDensity_absolutelyContinuous _ _).smul_left _
  have := h1.map (measurable_pi_apply i)
  unfold coordMarginal
  rwa [pi_map_eval_prob] at this

/- Route and status (EQ-01b, attempt 2: OPEN, and the pointwise clause is suspected FALSE as stated).

What the weak-specification layer (`HRS.External.WeakSpec`) gives, through the bridge above
(`pinnedReference = pinnedLaw`, `κ = weakKappa V β < 1/2` once `β γ₀` is small, `M = βγ₀+1`,
`M' = 1`): only TOTAL VARIATION statements for coordinate marginals,
`sup_A |P₁(y_j ∈ A) - P₂(y_j ∈ A)| ≤ C/N` (`rvh_pin_changed/_deleted/_removed/_comparison`),
the site-kernel bound `G_i ≤ C μ` (`weak_siteKernel_le`), hence the marginal density bounds, and
Wu's inequality (`weak_resampling`, `weak_linear_variance`).  The Rebeschini-van Handel comparison
`rvh_comparison` only controls bounded test functions through the sum of their SUP-oscillations
`∑_j Δ_j`.  The pointwise density at `z` is the expectation of the test function
`F_z(y) = e^{-λ∑_j q(y_j - z)}` (ratio of partition functions with the extra pin `z`), whose
coordinate oscillation is `≈ 1` (not `λ`) because a particle may sit on `z`; truncating `q` at `T`
gives `|ΔE F^{far}| ≲ λT` but the near part is then of size `β ρ_c^s`, not `λ`.  So the pointwise
bound `Cλ ∑_a(1 + q(z-a))` does NOT follow from the layer; it needs a weighted (position-aware)
Dobrushin comparison, i.e. the disagreement-measure recursion `Q:eq:measure-disagreement`
(maximal coupling of two heat-bath chains, or a Wasserstein version of `rvh_comparison` with the
weight `ω_z = 1 + q(z - ·)`, closed under `*w₀` only up to the resolvent series
`Q:eq:pin-resolvent`, using `twopole_vol`/`q3_vol`-type bounds).  This is not in the repository.

Defect of the statement (not repairable without a hypothesis): the resolvent term is
`λ ∑_a w₀^{*2}(z,a) ≍ λ q*q(z,a)`, of size `λ(1 + log₊ 1/|z-a|)` (and `log` is `≲ q` only when `q`
has the same local singularity as `g`, which the source assumes: "q ≥ 0 has the same local
singularity as g").  The statement here only assumes the UPPER envelope `q ≤ C_q(1 + r^{-s})`.
For `q = c r^{-s} 1_S(r)` with `S` a union of dyadic annuli (small `c`), `a` a single pin and
`z` with `q(z-a) = 0`, `|z - a| ≈ N^{-1/d}`, first-order perturbation theory gives
`ρ^a(z) - ρ^∅(z) ≈ β λ ρ(z) (q*q)(z,a) ≳ c² (log N)/N`, which is not `≤ C/N`.  Repair: add the
two-sided hypothesis `q z ≥ c₀ eucDist z 0 ^ (-s) - C₀`, or replace `1 + ∑ q(z - A k)` by
`1 + ∑ log₊(1/|z - A k|)` in the conclusion. -/

/-- Lemma 4.10 `M:Q:lem:pin` (source lines 4489-4496), `Q:eq:pin-bound`: there is a smallness
threshold `γ₀` such that for every admissible weak pair kernel `q` (nonnegative, even,
measurable, singularity at most that of `g`, row integral `sup_x ∫ q(x-y) μ(dy) ≤ γ₀`) and every
fixed number `a` of pins and `j` of removed coordinates there is `C` with: for every `N`, every
common field `β q*μ + h` with `‖h‖_∞ ≤ 1`, every pin configuration `A` and every free coordinate
`i` of `R_{N-j}^A`,
`|d(R_{N-j}^A)^{(i)}/dμ(z) - dπ_N/dμ(z)| ≤ C min{1, N⁻¹(1 + ∑_{a∈A} q(z - a))}` `μ`-a.e.
(Uniformity in a support cutoff is not encoded.) -/
theorem pin_comparison (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ (q : Torus d → ℝ) (Cq : ℝ), Measurable q → (∀ z, 0 ≤ q z) →
      (∀ z, q (-z) = q z) →
      (∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 → periodicRiesz d s z = q z + k z + c) →
      (∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s))) →
      (∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₀) →
      ∀ a j : ℕ, ∃ C : ℝ, ∀ N : ℕ, j + 2 ≤ N → ∀ h : Torus d → ℝ, Measurable h →
        (∀ x, |h x| ≤ 1) → ∀ (A : Fin a → Torus d) (i : Fin (N - j)),
          coordMarginal (pinnedReference q (fun x => β * convMeasure q (withDensityReal ρ) x + h x)
              (withDensityReal ρ) (N - j) (β / N) A) i ≪ withDensityReal ρ ∧
          weakRefMarginal q h (withDensityReal ρ) β N ≪ withDensityReal ρ ∧
          ∀ᵐ z ∂(withDensityReal ρ),
            |((coordMarginal (pinnedReference q
                  (fun x => β * convMeasure q (withDensityReal ρ) x + h x)
                  (withDensityReal ρ) (N - j) (β / N) A) i).rnDeriv (withDensityReal ρ) z).toReal -
              ((weakRefMarginal q h (withDensityReal ρ) β N).rnDeriv
                (withDensityReal ρ) z).toReal| ≤
              C * min 1 ((1 / (N : ℝ)) * (1 + ∑ k, q (z - A k))) := by
  sorry

/- Route and status (EQ-01b, open).  Source lines 4536-4550: cavity equation `Q:eq:weak-cavity-new`
for `b_N = dπ_N/dμ - 1`, pole-pressure bound `F''(t) ≤ CNλ²[1+|log λt|]` from pinned resampling
`Q:eq:resampling` (not a hypothesis here, and not in the repository), `D_N^q ≤ Cδ_N`, the unpinned
comparison of `pin_comparison` (`‖q*(π_N-ν_N)‖_∞ ≤ C/N`), then absorption `Q:eq:linf-absorb`.
Depends on `pin_comparison` and on the resampling variance bound for `R_n^A`. 
Attempt 2: still open.  Needs (i) the unpinned comparison `‖q*(π_N - ν_N)‖_∞ ≤ C/N`, i.e. the
pointwise (not TV) removed-coordinate bound of `pin_comparison` for `a = 0, j = 1` (true there: the
resolvent term is integrated against the pin marginal, giving `∫(1+log₊1/|z-x|)dx`; the layer only
gives TV), (ii) the pole-pressure bound `F''(t) ≤ CNλ²(1+|log λt|)`, which needs Wu's inequality for
the FRACTIONAL-pin ensembles `fieldLaw V (φ - tλ q(·,z)) λ n` (the layer's `weak_resampling` is only
for full pins `pinnedLaw`; `wu_resampling_uniform` applies to any `IsField`), (iii) the exact cavity
equation for `b_N`.  Not done.-/

/-- Lemma 4.10, display `Q:eq:reference-linf` (source lines 4497-4499): for the calibrated
reference, `‖dπ_N/dμ - 1‖_∞ ≤ C δ_N`. The calibrated common field is encoded by the
calibration identity `h_N = -β k*(π_N - μ)` modulo constants (`Q:eq:calibration`) with a
bounded kernel `k`; the two reference inputs used by the proof (`‖dπ_N/dμ - 1‖_{L²(μ)} ≤ C δ_N`
and `‖dπ_N/dμ - 1‖_∞ → 0`, part of `Q:eq:reference-input`) are hypotheses. -/
theorem reference_marginal_linf (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ (q : Torus d → ℝ) (Cq : ℝ), Measurable q → (∀ z, 0 ≤ q z) →
      (∀ z, q (-z) = q z) →
      (∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 → periodicRiesz d s z = q z + k z + c) →
      (∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s))) →
      (∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₀) →
      ∀ (k : Torus d → ℝ) (Ck : ℝ), Measurable k → (∀ z, |k z| ≤ Ck) →
      ∀ hN : ℕ → Torus d → ℝ, (∀ N, Measurable (hN N) ∧ ∀ x, |hN N x| ≤ 1) →
      (∀ N, 2 ≤ N → weakRefMarginal q (hN N) (withDensityReal ρ) β N ≪ withDensityReal ρ) →
      (∀ N, 2 ≤ N → ∃ cN : ℝ, ∀ x, hN N x = -β * ∫ y, k (x - y) *
          (((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1) ∂(withDensityReal ρ) + cN) →
      (∃ C₁ : ℝ, ∀ N, 2 ≤ N →
        eLpNorm (fun y => ((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C₁ * deltaN d s N)) →
      (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ᵐ y ∂(withDensityReal ρ),
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ ε) →
      ∃ C : ℝ, ∀ N, 2 ≤ N → ∀ᵐ y ∂(withDensityReal ρ),
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * deltaN d s N := by
  sorry

/-! ### Helpers for Lemma 4.11 (critical integrals with retained repulsion)

Route (source lines 4579-4598).  Everything is reduced to the radial profile
`W(t) = 1 + min{1,t}^{-s}` of `wEnv`, `d = 2s`, and the polar-coordinate formula on `ℝ^d`
(`lintegral_polar`, `lintegral_radial_torus`, an upper bound on the torus).
* `radial_B0/B1/B2/B3`: the one-pole integrals `∫ w`, `∫_{|z-x|<R} w ≤ C R^s`,
  `∫_{|z-x|≥ρ} w² ≤ C(1+log 1/ρ)`, `∫_{|z-x|≥ρ} w³ ≤ C ρ^{-s}` (all `d = 2s`).
* `wEnv_near/wEnv_far`: triangle-inequality comparisons of the two poles `w(x,z)`, `w(y,z)`
  on the balls of radius `r/2` around `x`, `y` and on the complement.
* `twopole_vol` (`Q:eq:two-pole-convolution`), `cap_vol` (`Q:eq:cap-radial`, split at `λ^{1/s}`),
  `q3_vol` (the `bc·min{1,λb}` term, three regions) and `pinprod_vol`
  (`Q:eq:pin-product-integral`, `min{1,u+v+w} ≤ min{1,u}+min{1,v}+min{1,w}`).
* `wEnv_le_gPlus` (`w ≤ A(1+g_+)`, from the local singularity of `g`), `exp_pow4_mu`
  (`φ⁴e^{-uφ} ≤ 24 min{φ,1/u}⁴`, from `conj_pow`) and `exp_moments` (`Q:eq:radial-moments`,
  from `conj_expo`, `conj_pow`).
The measure `μ = ρ dx` is bounded by `Λ dx` (`PoleCavityAux.lintegral_mu_le_vol`). -/

section Lemma411Aux

open Set Metric

namespace PairCorrAux


theorem lintegral_polar (hd : 1 ≤ d) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w : Euc d, F ‖w‖ =
      (d : ℝ≥0∞) * volume (ball (0 : Euc d) 1) *
        ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (d - 1)) * F t := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have hmp := (volume : Measure (Euc d)).measurePreserving_homeomorphUnitSphereProd
  have hemb := (homeomorphUnitSphereProd (Euc d)).measurableEmbedding
  have e1 : ∫⁻ w : Euc d, F ‖w‖ = ∫⁻ w : Euc d in ({0}ᶜ : Set (Euc d)), F ‖w‖ := by
    rw [restrict_compl_singleton]
  rw [e1, ← lintegral_subtype_comap (measurableSet_singleton _).compl]
  have e2 := hmp.lintegral_comp_emb hemb (fun p => F (p.2 : ℝ))
  simp only [homeomorphUnitSphereProd_apply_snd_coe] at e2
  rw [e2, lintegral_prod _ (by fun_prop)]
  have e3 : ∫⁻ t : Ioi (0:ℝ), F t ∂(Measure.volumeIoiPow (d - 1)) =
      ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (d - 1)) * F t := by
    simp only [Measure.volumeIoiPow]
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    rw [← lintegral_subtype_comap measurableSet_Ioi (fun t : ℝ => ENNReal.ofReal (t ^ (d - 1)) * F t)]
    rfl
  simp only []
  rw [hfr, lintegral_const, Measure.toSphere_apply_univ, hfr, e3]
  rw [mul_comm]


theorem eucDist_symm' (x y : Torus d) : Torus.eucDist x y = Torus.eucDist y x := by
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_sub_rev]

theorem eucDist_mk_zero' {w : Euc d} (hw : ∀ i, |w i| ≤ 1 / 2) :
    Torus.eucDist (Torus.mk w) 0 = ‖w‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ‖((Torus.mk w : Torus d) i - (0 : Torus d) i)‖ = |w i| := by
    have : ((Torus.mk w : Torus d) i - (0 : Torus d) i) = ((w i : ℝ) : UnitAddCircle) := by
      simp [Torus.mk]
    rw [this]
    refine (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) one_ne_zero).2 ?_
    rw [abs_one]
    have := hw i
    linarith
  rw [h2, Real.norm_eq_abs]

theorem eucDist_add_left (x z : Torus d) : Torus.eucDist x (x + z) = Torus.eucDist 0 z := by
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, Pi.zero_apply]
  rw [show x i - (x i + z i) = -z i by abel, norm_neg, zero_sub, norm_neg]

theorem continuous_eucDist' (x₀ : Torus d) : Continuous (fun x : Torus d => Torus.eucDist x x₀) := by
  unfold Torus.eucDist
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_norm.comp ((continuous_apply i).sub continuous_const))).pow 2

theorem measurable_eucDist' (x : Torus d) : Measurable (fun z : Torus d => Torus.eucDist x z) := by
  have := continuous_eucDist' (d := d) x
  simp_rw [eucDist_symm' x]
  exact this.measurable

theorem lintegral_radial_torus (hd : 1 ≤ d) (x : Torus d) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z : Torus d, F (Torus.eucDist x z) ≤
      (d : ℝ≥0∞) * volume (ball (0 : Euc d) 1) *
        ∫⁻ t in Set.Ioc (0:ℝ) (d + 1), ENNReal.ofReal (t ^ (d - 1)) * F t := by
  have e0 : ∫⁻ z : Torus d, F (Torus.eucDist x z) = ∫⁻ z : Torus d, F (Torus.eucDist 0 z) := by
    rw [← lintegral_add_left_eq_self (fun z : Torus d => F (Torus.eucDist x z)) x]
    simp_rw [eucDist_add_left]
  rw [e0, KernelAux.lintegral_torus_box (fun z => F (Torus.eucDist 0 z))]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have h1 := hmp.setLIntegral_comp_preimage_emb hemb
    (fun y => F (Torus.eucDist 0 (KernelAux.boxPt y))) (KernelAux.Box d)
  rw [← h1]
  set D : ℝ := d + 1
  have hsub : (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d) ⊆ ball (0 : Euc d) D := by
    intro w hw
    have hw' : ∀ i, |w i| ≤ 1 / 2 := fun i => KernelAux.Box_abs_le hw i
    rw [mem_ball_zero_iff, EuclideanSpace.norm_eq]
    have hD : (0:ℝ) < D := by positivity
    rw [Real.sqrt_lt' hD]
    have : ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin d, (1/2 : ℝ) ^ 2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hw' i) 2
    have h2 : ∑ _i : Fin d, (1/2 : ℝ) ^ 2 = d / 4 := by simp; ring
    have : (d : ℝ) / 4 < D ^ 2 := by
      simp only [D]; nlinarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
    linarith
  calc ∫⁻ w in (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d),
          F (Torus.eucDist 0 (KernelAux.boxPt (@WithLp.ofLp 2 (Fin d → ℝ) w)))
      ≤ ∫⁻ w in ball (0 : Euc d) D, F ‖w‖ := by
        have hms : MeasurableSet ((@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d)) :=
          (KernelAux.measurableSet_Box d).preimage hmp.measurable
        calc _ = ∫⁻ w in (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d), F ‖w‖ := by
              refine setLIntegral_congr_fun hms fun w hw => ?_
              have hw' : ∀ i, |w i| ≤ 1 / 2 := fun i => KernelAux.Box_abs_le hw i
              rw [eucDist_symm']
              exact congrArg F (eucDist_mk_zero' hw')
          _ ≤ _ := lintegral_mono_set hsub
    _ = ∫⁻ w : Euc d, (Set.Iio D).indicator F ‖w‖ := by
        rw [← lintegral_indicator measurableSet_ball]
        refine lintegral_congr fun w => ?_
        by_cases hw : w ∈ ball (0 : Euc d) D
        · rw [Set.indicator_of_mem hw, Set.indicator_of_mem]
          simpa using hw
        · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem]
          simpa using hw
    _ = _ := by
        rw [lintegral_polar hd _ (hF.indicator measurableSet_Iio)]
        congr 1
        have : ∀ t : ℝ, ENNReal.ofReal (t ^ (d - 1)) * (Set.Iio D).indicator F t =
            (Set.Iio D).indicator (fun t => ENNReal.ofReal (t ^ (d - 1)) * F t) t := by
          intro t
          by_cases ht : t ∈ Set.Iio D
          · simp [Set.indicator_of_mem ht]
          · simp [Set.indicator_of_notMem ht]
        simp_rw [this]
        rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
        rw [← setLIntegral_congr Ioo_ae_eq_Ioc]
        congr 2
        ext t; simp [D, and_comm]


open PoleCavityAux in
theorem lintegral_Ioc_rpow (p : ℝ) (hp : -1 < p) (R : ℝ) (hR : 0 < R) :
    ∫⁻ t in Set.Ioc (0:ℝ) R, ENNReal.ofReal (t ^ p) = ENNReal.ofReal (R ^ (p + 1) / (p + 1)) := by
  rw [lintegral_Ioc_ofReal 0 R hR.le (fun t => t ^ p)
    (intervalIntegral.intervalIntegrable_rpow' hp) (fun t ht => Real.rpow_nonneg ht.1.le _)]
  congr 1
  rw [integral_rpow (Or.inl hp)]
  simp [Real.zero_rpow (by linarith : p + 1 ≠ 0)]

open PoleCavityAux in
theorem lintegral_Ioc_rpow_neg (p : ℝ) (hp : p < -1) (ρ D : ℝ) (hρ : 0 < ρ) (hρD : ρ ≤ D) :
    ∫⁻ t in Set.Ioc ρ D, ENNReal.ofReal (t ^ p) ≤ ENNReal.ofReal (ρ ^ (p + 1) / (-(p + 1))) := by
  have hcont : ContinuousOn (fun t : ℝ => t ^ p) (Set.uIcc ρ D) := by
    refine ContinuousOn.rpow_const continuousOn_id fun x hx => Or.inl ?_
    rw [Set.uIcc_of_le hρD] at hx
    exact (lt_of_lt_of_le hρ hx.1).ne'
  rw [lintegral_Ioc_ofReal ρ D hρD (fun t => t ^ p) hcont.intervalIntegrable
    (fun t ht => Real.rpow_nonneg (lt_of_lt_of_le hρ ht.1.le).le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [integral_rpow (Or.inr ⟨hp.ne, by
    rw [Set.uIcc_of_le hρD]; intro h; exact absurd h.1 (not_le.2 hρ)⟩)]
  have h1 : 0 ≤ D ^ (p + 1) := Real.rpow_nonneg (hρ.le.trans hρD) _
  have h2 : p + 1 < 0 := by linarith
  rw [show (D ^ (p + 1) - ρ ^ (p + 1)) / (p + 1) = (ρ ^ (p + 1) - D ^ (p + 1)) / (-(p + 1)) by
    rw [div_neg, ← neg_div, neg_sub]]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

open PoleCavityAux in
theorem lintegral_Ioc_inv (ρ D : ℝ) (hρ : 0 < ρ) (hρD : ρ ≤ D) :
    ∫⁻ t in Set.Ioc ρ D, ENNReal.ofReal (t⁻¹) = ENNReal.ofReal (Real.log (D / ρ)) := by
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.uIcc ρ D) := by
    refine continuousOn_inv₀.mono fun x hx => ?_
    rw [Set.uIcc_of_le hρD] at hx
    exact (lt_of_lt_of_le hρ hx.1).ne'
  rw [lintegral_Ioc_ofReal ρ D hρD (fun t => t⁻¹) hcont.intervalIntegrable
    (fun t ht => inv_nonneg.2 (lt_of_lt_of_le hρ ht.1.le).le)]
  rw [integral_inv_of_pos hρ (hρ.trans_le hρD)]

theorem lintegral_Ioc_indicator_Iio (G f : ℝ → ℝ≥0∞) (R D : ℝ) (hR : R ≤ D) :
    ∫⁻ t in Set.Ioc (0:ℝ) D, G t * (Set.Iio R).indicator f t = ∫⁻ t in Set.Ioc (0:ℝ) R, G t * f t := by
  have : ∀ t : ℝ, G t * (Set.Iio R).indicator f t = (Set.Iio R).indicator (fun t => G t * f t) t := by
    intro t
    by_cases ht : t ∈ Set.Iio R
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  simp_rw [this]
  rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have h1 : Set.Iio R ∩ Set.Ioc (0:ℝ) D =ᵐ[volume] Set.Ioc (0:ℝ) R := by
    have : Set.Iio R ∩ Set.Ioc (0:ℝ) D = Set.Ioo 0 R := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioc, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, h2.le.trans hR⟩
    rw [this]; exact Ioo_ae_eq_Ioc
  exact setLIntegral_congr h1

theorem lintegral_Ioc_indicator_Ici (G f : ℝ → ℝ≥0∞) (ρ D : ℝ) (hρ : 0 < ρ) :
    ∫⁻ t in Set.Ioc (0:ℝ) D, G t * (Set.Ici ρ).indicator f t = ∫⁻ t in Set.Ioc ρ D, G t * f t := by
  have : ∀ t : ℝ, G t * (Set.Ici ρ).indicator f t = (Set.Ici ρ).indicator (fun t => G t * f t) t := by
    intro t
    by_cases ht : t ∈ Set.Ici ρ
    · simp [Set.indicator_of_mem ht]
    · simp [Set.indicator_of_notMem ht]
  simp_rw [this]
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
  have h1 : Set.Ici ρ ∩ Set.Ioc (0:ℝ) D =ᵐ[volume] Set.Ioc ρ D := by
    have : Set.Ici ρ ∩ Set.Ioc (0:ℝ) D = Set.Icc ρ D := by
      ext t; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioc, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, hρ.trans_le h1, h2⟩
    rw [this]; exact Ioc_ae_eq_Icc.symm
  exact setLIntegral_congr h1


/-- The radial profile of `wEnv`. -/
def Wr (s t : ℝ) : ℝ := 1 + (min 1 t) ^ (-s)

theorem measurable_Wr (s : ℝ) : Measurable (Wr s) := by
  unfold Wr
  exact measurable_const.add ((measurable_const.min measurable_id).pow_const _)

/-- The constant of the polar-coordinate bound. -/
def cd (d : ℕ) : ℝ≥0∞ := (d : ℝ≥0∞) * volume (ball (0 : Euc d) 1)

theorem cd_ne_top (d : ℕ) : cd d ≠ ∞ :=
  ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) measure_ball_lt_top.ne

theorem radial_B1 {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (x : Torus d) (R : ℝ)
    (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ∫⁻ z, {z : Torus d | Torus.eucDist x z < R}.indicator
        (fun z => ENNReal.ofReal (wEnv s x z)) z ≤
      cd d * ENNReal.ofReal ((1 / d + 1 / s) * R ^ s) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hF : Measurable ((Set.Iio R).indicator (fun t => ENNReal.ofReal (Wr s t))) :=
    (ENNReal.measurable_ofReal.comp (measurable_Wr s)).indicator measurableSet_Iio
  have h0 : ∀ z : Torus d, {z : Torus d | Torus.eucDist x z < R}.indicator
      (fun z => ENNReal.ofReal (wEnv s x z)) z =
      (Set.Iio R).indicator (fun t => ENNReal.ofReal (Wr s t)) (Torus.eucDist x z) := by
    intro z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Iio]
    rfl
  simp_rw [h0]
  refine (lintegral_radial_torus (by omega) x _ hF).trans ?_
  unfold cd
  gcongr
  rw [lintegral_Ioc_indicator_Iio _ _ R (d + 1) (by linarith)]
  have hpt : ∀ t ∈ Set.Ioc (0:ℝ) R, ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (Wr s t) =
      ENNReal.ofReal (t ^ ((d:ℝ) - 1)) + ENNReal.ofReal (t ^ (s - 1)) := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have hmin : min 1 t = t := min_eq_right (ht.2.trans hR1)
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (Real.rpow_nonneg ht0.le _)
      (Real.rpow_nonneg ht0.le _)]
    congr 1
    unfold Wr
    rw [hmin]
    have e1 : t ^ (d - 1) = t ^ ((d:ℝ) - 1) := by
      rw [← Real.rpow_natCast]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
    have e2 : t ^ ((d:ℝ) - 1) * t ^ (-s) = t ^ (s - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; rw [hcrit]; ring
    rw [e1, mul_add, mul_one, e2]
  rw [setLIntegral_congr_fun measurableSet_Ioc hpt]
  rw [lintegral_add_left (f := fun x : ℝ => ENNReal.ofReal (x ^ ((d:ℝ) - 1)))
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)),
    lintegral_Ioc_rpow _ (by linarith) R hR0, lintegral_Ioc_rpow _ (by linarith) R hR0]
  rw [sub_add_cancel, sub_add_cancel]
  have hd0 : (0:ℝ) < d := by linarith
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : R ^ (d:ℝ) = R ^ (d : ℕ) := by
    rw [Real.rpow_natCast]
  have h3 : R ^ (d : ℕ) ≤ R ^ s := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hR0 hR1 (by rw [hcrit]; linarith)
  rw [h1]
  have : R ^ (d:ℕ) / d + R ^ s / s ≤ (1 / d + 1 / s) * R ^ s := by
    have := div_le_div_of_nonneg_right h3 hd0.le
    calc _ ≤ R ^ s / d + R ^ s / s := by linarith
      _ = _ := by ring
  exact this


theorem Wr_pow_le (s : ℝ) (hs : 0 < s) (k : ℕ) (t : ℝ) (ht : 0 < t) :
    Wr s t ^ k ≤ 2 ^ k * (1 + t ^ (-(k * s))) := by
  have hnn : 0 ≤ t ^ (-(k * s)) := Real.rpow_nonneg ht.le _
  by_cases h1 : t ≤ 1
  · have hm : min 1 t = t := min_eq_right h1
    have hts : 1 ≤ t ^ (-s) := by
      have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht h1 (by linarith : -s ≤ 0)
      exact this
    have hW : Wr s t ≤ 2 * t ^ (-s) := by unfold Wr; rw [hm]; linarith
    have hW0 : 0 ≤ Wr s t := by unfold Wr; rw [hm]; positivity
    calc Wr s t ^ k ≤ (2 * t ^ (-s)) ^ k := pow_le_pow_left₀ hW0 hW k
      _ = 2 ^ k * t ^ (-(k * s)) := by
        rw [mul_pow, ← Real.rpow_natCast (t ^ (-s)) k, ← Real.rpow_mul ht.le]
        congr 2; ring
      _ ≤ _ := by
        have : (0:ℝ) < 2 ^ k := by positivity
        nlinarith
  · push Not at h1
    have hW : Wr s t = 2 := by unfold Wr; rw [min_eq_left h1.le]; simp; norm_num
    rw [hW]
    have : (0:ℝ) < 2 ^ k := by positivity
    nlinarith

theorem radial_B2 {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (x : Torus d) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ z, {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
        (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z ≤
      cd d * ENNReal.ofReal (4 * (((d:ℝ) + 1) ^ d / d + Real.log (((d:ℝ) + 1) / ρ))) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hd0 : (0:ℝ) < d := by linarith
  have hF : Measurable ((Set.Ici ρ).indicator (fun t => ENNReal.ofReal (Wr s t ^ 2))) :=
    (ENNReal.measurable_ofReal.comp ((measurable_Wr s).pow_const _)).indicator measurableSet_Ici
  have h0 : ∀ z : Torus d, {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
      (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z =
      (Set.Ici ρ).indicator (fun t => ENNReal.ofReal (Wr s t ^ 2)) (Torus.eucDist x z) := by
    intro z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ici]
    rfl
  simp_rw [h0]
  refine (lintegral_radial_torus (by omega) x _ hF).trans ?_
  unfold cd
  gcongr
  rw [lintegral_Ioc_indicator_Ici _ _ ρ (d + 1) hρ0]
  have hD : ρ ≤ (d:ℝ) + 1 := by linarith
  have hpt : ∀ t ∈ Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (Wr s t ^ 2) ≤
      ENNReal.ofReal 4 * (ENNReal.ofReal (t ^ ((d:ℝ) - 1)) + ENNReal.ofReal t⁻¹) := by
    intro t ht
    have ht0 : 0 < t := hρ0.trans_le ht.1.le
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : t ^ (d - 1) = t ^ ((d:ℝ) - 1) := by
      rw [← Real.rpow_natCast]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
    have e2 : t ^ ((d:ℝ) - 1) * t ^ (-((2:ℕ) * s)) = t⁻¹ := by
      rw [← Real.rpow_add ht0, ← Real.rpow_neg_one]; congr 1; rw [hcrit]; push_cast; ring
    have h := Wr_pow_le s hs0 2 t ht0
    have hp : 0 ≤ t ^ ((d:ℝ) - 1) := Real.rpow_nonneg ht0.le _
    rw [e1]
    calc t ^ ((d:ℝ) - 1) * Wr s t ^ 2 ≤ t ^ ((d:ℝ) - 1) * (2 ^ 2 * (1 + t ^ (-((2:ℕ) * s)))) :=
          mul_le_mul_of_nonneg_left h hp
      _ = 4 * t ^ ((d:ℝ) - 1) + 4 * (t ^ ((d:ℝ) - 1) * t ^ (-((2:ℕ) * s))) := by ring
      _ = _ := by rw [e2]; ring
  calc ∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (Wr s t ^ 2)
      ≤ ∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal 4 *
          (ENNReal.ofReal (t ^ ((d:ℝ) - 1)) + ENNReal.ofReal t⁻¹) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ENNReal.ofReal 4 * ((∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ ((d:ℝ) - 1))) +
          ∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal t⁻¹) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (f := fun x : ℝ => ENNReal.ofReal (x ^ ((d:ℝ) - 1)))
          (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))]
    _ ≤ ENNReal.ofReal 4 * (ENNReal.ofReal (((d:ℝ) + 1) ^ d / d) +
          ENNReal.ofReal (Real.log (((d:ℝ) + 1) / ρ))) := by
        gcongr
        · calc ∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ ((d:ℝ) - 1))
              ≤ ∫⁻ t in Set.Ioc (0:ℝ) ((d:ℝ) + 1), ENNReal.ofReal (t ^ ((d:ℝ) - 1)) :=
                lintegral_mono_set (Set.Ioc_subset_Ioc_left hρ0.le)
            _ = _ := by
              rw [lintegral_Ioc_rpow _ (by linarith) _ (by linarith), sub_add_cancel,
                ← Real.rpow_natCast]
        · exact (lintegral_Ioc_inv ρ _ hρ0 hD).le
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (Real.log_nonneg (by rw [le_div_iff₀ hρ0]; linarith)),
          ← ENNReal.ofReal_mul (by norm_num)]


theorem radial_B3 {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (x : Torus d) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ z, {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
        (fun z => ENNReal.ofReal (wEnv s x z ^ 3)) z ≤
      cd d * ENNReal.ofReal (8 * (((d:ℝ) + 1) ^ d / d + ρ ^ (-s) / s)) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hd0 : (0:ℝ) < d := by linarith
  have hF : Measurable ((Set.Ici ρ).indicator (fun t => ENNReal.ofReal (Wr s t ^ 3))) :=
    (ENNReal.measurable_ofReal.comp ((measurable_Wr s).pow_const _)).indicator measurableSet_Ici
  have h0 : ∀ z : Torus d, {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
      (fun z => ENNReal.ofReal (wEnv s x z ^ 3)) z =
      (Set.Ici ρ).indicator (fun t => ENNReal.ofReal (Wr s t ^ 3)) (Torus.eucDist x z) := by
    intro z
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ici]
    rfl
  simp_rw [h0]
  refine (lintegral_radial_torus (by omega) x _ hF).trans ?_
  unfold cd
  gcongr
  rw [lintegral_Ioc_indicator_Ici _ _ ρ (d + 1) hρ0]
  have hD : ρ ≤ (d:ℝ) + 1 := by linarith
  have hpt : ∀ t ∈ Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (Wr s t ^ 3) ≤
      ENNReal.ofReal 8 * (ENNReal.ofReal (t ^ ((d:ℝ) - 1)) + ENNReal.ofReal (t ^ (-s - 1))) := by
    intro t ht
    have ht0 : 0 < t := hρ0.trans_le ht.1.le
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : t ^ (d - 1) = t ^ ((d:ℝ) - 1) := by
      rw [← Real.rpow_natCast]; congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ d)]; ring
    have e2 : t ^ ((d:ℝ) - 1) * t ^ (-((3:ℕ) * s)) = t ^ (-s - 1) := by
      rw [← Real.rpow_add ht0]; congr 1; rw [hcrit]; push_cast; ring
    have h := Wr_pow_le s hs0 3 t ht0
    have hp : 0 ≤ t ^ ((d:ℝ) - 1) := Real.rpow_nonneg ht0.le _
    rw [e1]
    calc t ^ ((d:ℝ) - 1) * Wr s t ^ 3 ≤ t ^ ((d:ℝ) - 1) * (2 ^ 3 * (1 + t ^ (-((3:ℕ) * s)))) :=
          mul_le_mul_of_nonneg_left h hp
      _ = 8 * t ^ ((d:ℝ) - 1) + 8 * (t ^ ((d:ℝ) - 1) * t ^ (-((3:ℕ) * s))) := by ring
      _ = _ := by rw [e2]; ring
  calc ∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ (d - 1)) * ENNReal.ofReal (Wr s t ^ 3)
      ≤ ∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal 8 *
          (ENNReal.ofReal (t ^ ((d:ℝ) - 1)) + ENNReal.ofReal (t ^ (-s - 1))) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = ENNReal.ofReal 8 * ((∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ ((d:ℝ) - 1))) +
          ∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ (-s - 1))) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (f := fun x : ℝ => ENNReal.ofReal (x ^ ((d:ℝ) - 1)))
          (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))]
    _ ≤ ENNReal.ofReal 8 * (ENNReal.ofReal (((d:ℝ) + 1) ^ d / d) +
          ENNReal.ofReal (ρ ^ (-s) / s)) := by
        gcongr
        · calc ∫⁻ t in Set.Ioc ρ ((d:ℝ) + 1), ENNReal.ofReal (t ^ ((d:ℝ) - 1))
              ≤ ∫⁻ t in Set.Ioc (0:ℝ) ((d:ℝ) + 1), ENNReal.ofReal (t ^ ((d:ℝ) - 1)) :=
                lintegral_mono_set (Set.Ioc_subset_Ioc_left hρ0.le)
            _ = _ := by
              rw [lintegral_Ioc_rpow _ (by linarith) _ (by linarith), sub_add_cancel,
                ← Real.rpow_natCast]
        · refine (lintegral_Ioc_rpow_neg (-s - 1) (by linarith) ρ _ hρ0 hD).trans ?_
          refine le_of_eq ?_
          congr 1
          rw [show -s - 1 + 1 = -s by ring, neg_neg]
    _ = _ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num)]


theorem eucDist_self' (x : Torus d) : Torus.eucDist x x = 0 := by simp [Torus.eucDist]

theorem eucDist_nonneg' (x y : Torus d) : 0 ≤ Torus.eucDist x y := Real.sqrt_nonneg _

theorem eucDist_triangle (x y z : Torus d) :
    Torus.eucDist x z ≤ Torus.eucDist x y + Torus.eucDist y z := by
  set a : Euc d := WithLp.toLp 2 (fun i => ‖x i - y i‖) with ha
  set b : Euc d := WithLp.toLp 2 (fun i => ‖y i - z i‖) with hb
  have hna : ‖a‖ = Torus.eucDist x y := by
    rw [EuclideanSpace.norm_eq]; simp [ha, Torus.eucDist]
  have hnb : ‖b‖ = Torus.eucDist y z := by
    rw [EuclideanSpace.norm_eq]; simp [hb, Torus.eucDist]
  have hle : Torus.eucDist x z ≤ ‖a + b‖ := by
    unfold Torus.eucDist
    rw [EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have h1 : ‖x i - z i‖ ≤ ‖x i - y i‖ + ‖y i - z i‖ := by
      have := norm_add_le (x i - y i) (y i - z i)
      rwa [show x i - y i + (y i - z i) = x i - z i by abel] at this
    have hab : (a + b) i = ‖x i - y i‖ + ‖y i - z i‖ := by simp [ha, hb]
    rw [hab, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc _ ≤ ‖a + b‖ := hle
    _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ = _ := by rw [hna, hnb]

theorem eucDist_eq_zero' (x y : Torus d) : Torus.eucDist x y = 0 ↔ x = y := by
  unfold Torus.eucDist
  rw [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => by positivity)]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)]
  constructor
  · intro h
    funext i
    have := h i (Finset.mem_univ i)
    have h2 : ‖x i - y i‖ = 0 := by simpa using this
    exact sub_eq_zero.1 (norm_eq_zero.1 h2)
  · intro h i _
    rw [h]; simp

theorem rTrunc_symm (x y : Torus d) : rTrunc x y = rTrunc y x := by
  unfold rTrunc; rw [eucDist_symm']

theorem wEnv_symm (s : ℝ) (x y : Torus d) : wEnv s x y = wEnv s y x := by
  unfold wEnv; rw [rTrunc_symm]

theorem rTrunc_pos {x y : Torus d} (h : x ≠ y) : 0 < rTrunc x y := by
  unfold rTrunc
  refine lt_min one_pos ?_
  exact lt_of_le_of_ne (eucDist_nonneg' x y) (fun h0 => h ((eucDist_eq_zero' x y).1 h0.symm))

theorem rTrunc_le_one (x y : Torus d) : rTrunc x y ≤ 1 := min_le_left _ _

theorem rTrunc_le_dist (x y : Torus d) : rTrunc x y ≤ Torus.eucDist x y := min_le_right _ _

theorem rTrunc_nonneg (x y : Torus d) : 0 ≤ rTrunc x y := le_min zero_le_one (eucDist_nonneg' x y)

theorem one_le_wEnv (s : ℝ) (x y : Torus d) : 1 ≤ wEnv s x y := by
  unfold wEnv
  have := Real.rpow_nonneg (rTrunc_nonneg x y) (-s)
  linarith

theorem wEnv_le_of_ge {s : ℝ} (hs : 0 < s) {x y : Torus d} {u : ℝ} (hu : 0 < u)
    (h : u ≤ rTrunc x y) : wEnv s x y ≤ 1 + u ^ (-s) := by
  unfold wEnv
  have := Real.rpow_le_rpow_of_nonpos hu h (by linarith : -s ≤ 0)
  linarith


theorem two_rpow_aux {s : ℝ} {r : ℝ} (hr : 0 < r) {k : ℝ} (hk : 0 < k) :
    (r / k) ^ (-s) = k ^ s * r ^ (-s) := by
  rw [Real.div_rpow hr.le hk.le, Real.rpow_neg hk.le, div_inv_eq_mul, mul_comm]

/-- If `p` is close to `z`, then `q` is far from `z`. -/
theorem wEnv_near {s : ℝ} (hs : 0 < s) {p q : Torus d} (hpq : p ≠ q) {z : Torus d}
    (hz : Torus.eucDist p z < rTrunc p q / 2) :
    wEnv s q z ≤ 2 ^ s * wEnv s p q := by
  have hr := rTrunc_pos hpq
  have h1 : rTrunc p q / 2 ≤ rTrunc q z := by
    show rTrunc p q / 2 ≤ min 1 (Torus.eucDist q z)
    refine le_min (by have := rTrunc_le_one p q; linarith) ?_
    have t1 := eucDist_triangle p z q
    rw [eucDist_symm' z q] at t1
    have := rTrunc_le_dist p q
    linarith
  have h2 := wEnv_le_of_ge hs (x := q) (y := z) (by positivity) h1
  rw [two_rpow_aux hr (by norm_num : (0:ℝ) < 2)] at h2
  unfold wEnv at *
  have : (1:ℝ) ≤ 2 ^ s := Real.one_le_rpow (by norm_num) hs.le
  nlinarith [Real.rpow_nonneg (rTrunc_nonneg p q) (-s)]

theorem rTrunc_le_three {p q z : Torus d} (hpq : p ≠ q)
    (hq : rTrunc p q / 2 ≤ Torus.eucDist q z) : rTrunc p z ≤ 3 * rTrunc q z := by
  have hr := rTrunc_pos hpq
  by_cases hA : 1 / 3 ≤ Torus.eucDist q z
  · have : 1 ≤ 3 * rTrunc q z := by
      unfold rTrunc
      have : 1 / 3 ≤ min 1 (Torus.eucDist q z) := le_min (by norm_num) hA
      linarith
    exact (rTrunc_le_one p z).trans this
  · push Not at hA
    have hr1 : rTrunc p q < 1 := by linarith
    have hrp : rTrunc p q = Torus.eucDist p q := by
      unfold rTrunc at hr1 ⊢
      exact min_eq_right (by by_contra h; push Not at h; rw [min_eq_left h.le] at hr1; exact lt_irrefl _ hr1)
    have hqz : rTrunc q z = Torus.eucDist q z := by
      unfold rTrunc; exact min_eq_right (by linarith)
    have t1 := eucDist_triangle p q z
    calc rTrunc p z ≤ Torus.eucDist p z := rTrunc_le_dist p z
      _ ≤ 3 * rTrunc q z := by rw [hqz]; rw [hrp] at hq; linarith

theorem wEnv_far {s : ℝ} (hs : 0 < s) {p q z : Torus d} (hpq : p ≠ q)
    (hp : rTrunc p q / 2 ≤ Torus.eucDist p z) (hq : rTrunc p q / 2 ≤ Torus.eucDist q z) :
    wEnv s q z ≤ 3 ^ s * wEnv s p z := by
  have hr := rTrunc_pos hpq
  have h3 := rTrunc_le_three hpq hq
  have hpz : 0 < rTrunc p z := by
    unfold rTrunc
    exact lt_min one_pos (by linarith)
  have h1 : rTrunc p z / 3 ≤ rTrunc q z := by linarith
  have h2 := wEnv_le_of_ge hs (x := q) (y := z) (by positivity) h1
  rw [two_rpow_aux hpz (by norm_num : (0:ℝ) < 3)] at h2
  unfold wEnv at *
  have : (1:ℝ) ≤ 3 ^ s := Real.one_le_rpow (by norm_num) hs.le
  nlinarith [Real.rpow_nonneg (rTrunc_nonneg p z) (-s)]


/-- Real version of the constant `cd`. -/
def cdR (d : ℕ) : ℝ := (cd d).toReal

theorem cdR_nonneg (d : ℕ) : 0 ≤ cdR d := ENNReal.toReal_nonneg

theorem cd_mul_ofReal (d : ℕ) (y : ℝ) :
    cd d * ENNReal.ofReal y = ENNReal.ofReal (cdR d * y) := by
  rw [ENNReal.ofReal_mul (cdR_nonneg d), cdR, ENNReal.ofReal_toReal (cd_ne_top d)]

theorem radial_B1' {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (x : Torus d) (R : ℝ)
    (hR0 : 0 < R) (hR1 : R ≤ 1) :
    ∫⁻ z, {z : Torus d | Torus.eucDist x z < R}.indicator
        (fun z => ENNReal.ofReal (wEnv s x z)) z ≤
      ENNReal.ofReal (cdR d * ((1 / d + 1 / s) * R ^ s)) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  rw [← cd_mul_ofReal d]
  exact radial_B1 hd hcrit x R hR0 hR1

theorem radial_B2' {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (x : Torus d) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ z, {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
        (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z ≤
      ENNReal.ofReal (cdR d * (4 * (((d:ℝ) + 1) ^ d / d + Real.log (((d:ℝ) + 1) / ρ)))) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  rw [← cd_mul_ofReal d]
  exact radial_B2 hd hcrit x ρ hρ0 hρ1


theorem radial_B3' {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (x : Torus d) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∫⁻ z, {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
        (fun z => ENNReal.ofReal (wEnv s x z ^ 3)) z ≤
      ENNReal.ofReal (cdR d * (8 * (((d:ℝ) + 1) ^ d / d + ρ ^ (-s) / s))) := by
  rw [← cd_mul_ofReal d]
  exact radial_B3 hd hcrit x ρ hρ0 hρ1

theorem radial_B0 {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (x : Torus d) :
    ∫⁻ z, ENNReal.ofReal (wEnv s x z) ≤
      ENNReal.ofReal (cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2) := by
  have hpt : ∀ z : Torus d, ENNReal.ofReal (wEnv s x z) ≤
      {z : Torus d | Torus.eucDist x z < 1}.indicator (fun z => ENNReal.ofReal (wEnv s x z)) z +
        ENNReal.ofReal 2 := by
    intro z
    by_cases h : Torus.eucDist x z < 1
    · rw [Set.indicator_of_mem (show z ∈ {z : Torus d | Torus.eucDist x z < 1} from h)]
      exact le_self_add
    · push Not at h
      rw [Set.indicator_of_notMem (show z ∉ {z : Torus d | Torus.eucDist x z < 1} from by
        simpa using h), zero_add]
      refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
      unfold wEnv rTrunc
      rw [min_eq_left h]; norm_num
  calc ∫⁻ z, ENNReal.ofReal (wEnv s x z) ≤ ∫⁻ z, ({z : Torus d | Torus.eucDist x z < 1}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z)) z + ENNReal.ofReal 2) := lintegral_mono hpt
    _ = (∫⁻ z, {z : Torus d | Torus.eucDist x z < 1}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z)) z) + ENNReal.ofReal 2 := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
        simp
    _ ≤ ENNReal.ofReal (cdR d * ((1 / d + 1 / s) * 1 ^ s)) + ENNReal.ofReal 2 := by
        gcongr
        exact radial_B1' hd hcrit x 1 one_pos le_rfl
    _ = _ := by
        have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
        have hs0 : 0 < s := by rw [hcrit]; linarith
        rw [← ENNReal.ofReal_add (by have := cdR_nonneg d; positivity) (by norm_num)]


theorem measurable_wEnv (s : ℝ) (x : Torus d) : Measurable (fun z : Torus d => wEnv s x z) := by
  unfold wEnv rTrunc
  exact measurable_const.add ((measurable_const.min (measurable_eucDist' x)).pow_const _)

theorem measurable_ind_near (s : ℝ) (x : Torus d) (ρ : ℝ) (k : ℕ) :
    Measurable ({z : Torus d | Torus.eucDist x z < ρ}.indicator
      (fun z => ENNReal.ofReal (wEnv s x z ^ k))) :=
  (ENNReal.measurable_ofReal.comp ((measurable_wEnv s x).pow_const k)).indicator
    (measurableSet_lt (measurable_eucDist' x) measurable_const)

theorem measurable_ind_far (s : ℝ) (x : Torus d) (ρ : ℝ) (k : ℕ) :
    Measurable ({z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
      (fun z => ENNReal.ofReal (wEnv s x z ^ k))) :=
  (ENNReal.measurable_ofReal.comp ((measurable_wEnv s x).pow_const k)).indicator
    (measurableSet_le measurable_const (measurable_eucDist' x))

theorem log_one_div_nonneg (x y : Torus d) : 0 ≤ Real.log (1 / rTrunc x y) := by
  rcases eq_or_ne x y with h | h
  · subst h
    have : rTrunc x x = 0 := by unfold rTrunc; rw [eucDist_self' x]; simp
    rw [this]; simp
  · refine Real.log_nonneg ?_
    rw [le_div_iff₀ (rTrunc_pos h)]; simpa using rTrunc_le_one x y

theorem twopole_vol {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Torus d, x ≠ y →
      ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z) ≤ ENNReal.ofReal (C * ellEnv x y) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hd0 : (0:ℝ) < d := by linarith
  have hcd := cdR_nonneg d
  set K1 : ℝ := (1 / (d:ℝ) + 1 / s) with hK1
  have hK1p : 0 < K1 := by positivity
  set E : ℝ := ((d:ℝ) + 1) ^ d / d with hE
  have hE0 : 0 ≤ E := by positivity
  set A : ℝ := 4 * 2 ^ s * (cdR d * K1) + 3 ^ s * (cdR d * (4 * (E + Real.log (2 * ((d:ℝ) + 1))))) with hA
  set B : ℝ := 3 ^ s * (cdR d * 4) with hB
  have h2s : (1:ℝ) ≤ 2 ^ s := Real.one_le_rpow (by norm_num) hs0.le
  have h3s : (1:ℝ) ≤ 3 ^ s := Real.one_le_rpow (by norm_num) hs0.le
  have hlog2 : 0 ≤ Real.log (2 * ((d:ℝ) + 1)) := Real.log_nonneg (by linarith)
  refine ⟨A + B, by positivity, fun x y hxy => ?_⟩
  have hr := rTrunc_pos hxy
  have hr1 := rTrunc_le_one x y
  set r := rTrunc x y with hrdef
  set ρ := r / 2 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by linarith
  set a := wEnv s x y with ha
  have ha0 : 0 ≤ a := by linarith [one_le_wEnv s x y]
  -- pointwise decomposition
  have hpt : ∀ z : Torus d, ENNReal.ofReal (wEnv s x z * wEnv s y z) ≤
      ENNReal.ofReal (2 ^ s * a) * {z : Torus d | Torus.eucDist x z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z)) z +
      ENNReal.ofReal (2 ^ s * a) * {z : Torus d | Torus.eucDist y z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s y z)) z +
      ENNReal.ofReal (3 ^ s) * {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z := by
    intro z
    have hb := one_le_wEnv s x z
    have hc := one_le_wEnv s y z
    by_cases h1 : Torus.eucDist x z < ρ
    · have hcle := wEnv_near hs0 hxy h1
      rw [Set.indicator_of_mem (show z ∈ {z : Torus d | Torus.eucDist x z < ρ} from h1)]
      calc ENNReal.ofReal (wEnv s x z * wEnv s y z)
          ≤ ENNReal.ofReal (2 ^ s * a) * ENNReal.ofReal (wEnv s x z) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            nlinarith
        _ ≤ _ := by
            refine le_trans ?_ le_self_add
            exact le_self_add
    · push Not at h1
      by_cases h2 : Torus.eucDist y z < ρ
      · have hble : wEnv s x z ≤ 2 ^ s * a := by
          have := wEnv_near hs0 (p := y) (q := x) hxy.symm (z := z)
            (by rw [rTrunc_symm y x]; exact h2)
          rwa [wEnv_symm s y x] at this
        rw [Set.indicator_of_mem (show z ∈ {z : Torus d | Torus.eucDist y z < ρ} from h2)]
        calc ENNReal.ofReal (wEnv s x z * wEnv s y z)
            ≤ ENNReal.ofReal (2 ^ s * a) * ENNReal.ofReal (wEnv s y z) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              nlinarith
          _ ≤ _ := by
              refine le_trans ?_ le_self_add
              exact le_add_self
      · push Not at h2
        have hcle : wEnv s y z ≤ 3 ^ s * wEnv s x z := wEnv_far hs0 hxy h1 h2
        rw [Set.indicator_of_mem (show z ∈ {z : Torus d | ρ ≤ Torus.eucDist x z} from h1)]
        calc ENNReal.ofReal (wEnv s x z * wEnv s y z)
            ≤ ENNReal.ofReal (3 ^ s) * ENNReal.ofReal (wEnv s x z ^ 2) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              nlinarith
          _ ≤ _ := le_add_self
  have hm1 := measurable_ind_near s x ρ 1
  have hm2 := measurable_ind_near s y ρ 1
  have hm3 := measurable_ind_far s x ρ 2
  simp only [pow_one] at hm1 hm2
  have hB1 := radial_B1' hd hcrit x ρ hρ0 hρ1
  have hB1' := radial_B1' hd hcrit y ρ hρ0 hρ1
  have hB2 := radial_B2' hd hcrit x ρ hρ0 hρ1
  have hL := log_one_div_nonneg x y
  calc ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z)
      ≤ ∫⁻ z, (ENNReal.ofReal (2 ^ s * a) * {z : Torus d | Torus.eucDist x z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z)) z +
      ENNReal.ofReal (2 ^ s * a) * {z : Torus d | Torus.eucDist y z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s y z)) z +
      ENNReal.ofReal (3 ^ s) * {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z) := lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ s * a) * (∫⁻ z, {z : Torus d | Torus.eucDist x z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z)) z) +
        ENNReal.ofReal (2 ^ s * a) * (∫⁻ z, {z : Torus d | Torus.eucDist y z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s y z)) z) +
        ENNReal.ofReal (3 ^ s) * (∫⁻ z, {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z) := by
        have hmm : Measurable (fun z : Torus d => ENNReal.ofReal (2 ^ s * a) *
            {z : Torus d | Torus.eucDist x z < ρ}.indicator
              (fun z => ENNReal.ofReal (wEnv s x z)) z +
            ENNReal.ofReal (2 ^ s * a) * {z : Torus d | Torus.eucDist y z < ρ}.indicator
              (fun z => ENNReal.ofReal (wEnv s y z)) z) :=
          (hm1.const_mul _).add (hm2.const_mul _)
        rw [lintegral_add_left hmm, lintegral_add_left (hm1.const_mul _),
          lintegral_const_mul _ hm1, lintegral_const_mul _ hm2, lintegral_const_mul _ hm3]
    _ ≤ ENNReal.ofReal (2 ^ s * a) * ENNReal.ofReal (cdR d * (K1 * ρ ^ s)) +
        ENNReal.ofReal (2 ^ s * a) * ENNReal.ofReal (cdR d * (K1 * ρ ^ s)) +
        ENNReal.ofReal (3 ^ s) * ENNReal.ofReal (cdR d * (4 * (E + Real.log (((d:ℝ) + 1) / ρ)))) := by
        gcongr
    _ = ENNReal.ofReal (2 * (2 ^ s * a) * (cdR d * (K1 * ρ ^ s)) +
          3 ^ s * (cdR d * (4 * (E + Real.log (((d:ℝ) + 1) / ρ))))) := by
        have hlg : 0 ≤ Real.log (((d:ℝ) + 1) / ρ) :=
          Real.log_nonneg (by rw [le_div_iff₀ hρ0]; linarith)
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hr0 : 0 ≤ r := hr.le
        have hrs : r ^ s ≤ 1 := Real.rpow_le_one hr0 hr1 hs0.le
        have hρs : ρ ^ s ≤ r ^ s := Real.rpow_le_rpow hρ0.le (by linarith) hs0.le
        have har : a * r ^ s = r ^ s + 1 := by
          have h : r ^ (-s) * r ^ s = 1 := by rw [← Real.rpow_add hr]; simp
          rw [ha]; unfold wEnv; rw [← hrdef]
          linear_combination h
        have hlog : Real.log (((d:ℝ) + 1) / ρ) = Real.log (2 * ((d:ℝ) + 1)) + Real.log (1 / r) := by
          rw [← Real.log_mul (by positivity) (by positivity)]
          congr 1
          rw [hρdef]; field_simp
        have hfirst : 2 * (2 ^ s * a) * (cdR d * (K1 * ρ ^ s)) ≤ 4 * 2 ^ s * (cdR d * K1) := by
          have h1 : a * ρ ^ s ≤ 2 := by nlinarith
          have h2 : 0 ≤ 2 ^ s * (cdR d * K1) := by positivity
          calc 2 * (2 ^ s * a) * (cdR d * (K1 * ρ ^ s)) = 2 * (2 ^ s * (cdR d * K1)) * (a * ρ ^ s) := by ring
            _ ≤ 2 * (2 ^ s * (cdR d * K1)) * 2 := by gcongr
            _ = _ := by ring
        have hsecond : 3 ^ s * (cdR d * (4 * (E + Real.log (((d:ℝ) + 1) / ρ)))) =
            3 ^ s * (cdR d * (4 * (E + Real.log (2 * ((d:ℝ) + 1))))) + B * Real.log (1 / r) := by
          rw [hlog, hB]; ring
        have hAnn : 0 ≤ A := by positivity
        have hBnn : 0 ≤ B := by positivity
        rw [ellEnv]
        have hA2 : 0 ≤ A * Real.log (1 / r) := by positivity
        nlinarith [hfirst, hsecond, mul_nonneg hBnn hL]


theorem cap_vol {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ x : Torus d,
      ∫⁻ z, ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) ≤
        ENNReal.ofReal (C * lam * (1 + |Real.log lam|)) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hd0 : (0:ℝ) < d := by linarith
  have hcd := cdR_nonneg d
  set K1 : ℝ := (1 / (d:ℝ) + 1 / s) with hK1
  have hK1p : 0 < K1 := by positivity
  set E : ℝ := ((d:ℝ) + 1) ^ d / d with hE
  have hE0 : 0 ≤ E := by positivity
  have hlogd : 0 ≤ Real.log ((d:ℝ) + 1) := Real.log_nonneg (by linarith)
  set C1 : ℝ := cdR d * K1 + cdR d * (4 * (E + Real.log ((d:ℝ) + 1) + 1 / s)) with hC1
  set C0 : ℝ := cdR d * K1 + 2 with hC0
  have hC1n : 0 ≤ C1 := by positivity
  have hC0n : 0 ≤ C0 := by positivity
  refine ⟨C1 + C0, by positivity, fun lam hlam x => ?_⟩
  have hlg : 0 ≤ |Real.log lam| := abs_nonneg _
  by_cases hl1 : 1 ≤ lam
  · -- large lambda: use ∫ w
    have hpt : ∀ z : Torus d, ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) ≤
        ENNReal.ofReal (wEnv s x z) := by
      intro z
      refine ENNReal.ofReal_le_ofReal ?_
      have := one_le_wEnv s x z
      nlinarith [min_le_left 1 (lam * wEnv s x z)]
    refine (lintegral_mono hpt).trans ((radial_B0 hd hcrit x).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.one_rpow, mul_one]
    nlinarith [mul_nonneg hC1n hlam.le, mul_nonneg hC1n (mul_nonneg hlam.le hlg), mul_nonneg hC0n hlg,
      mul_nonneg hC0n (mul_nonneg hlam.le hlg)]
  · push Not at hl1
    set R : ℝ := lam ^ (1 / s) with hR
    have hR0 : 0 < R := Real.rpow_pos_of_pos hlam _
    have hR1 : R ≤ 1 := Real.rpow_le_one hlam.le hl1.le (by positivity)
    have hRs : R ^ s = lam := by
      rw [hR, ← Real.rpow_mul hlam.le, one_div_mul_cancel hs0.ne', Real.rpow_one]
    have hpt : ∀ z : Torus d, ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) ≤
        {z : Torus d | Torus.eucDist x z < R}.indicator (fun z => ENNReal.ofReal (wEnv s x z)) z +
          ENNReal.ofReal lam * {z : Torus d | R ≤ Torus.eucDist x z}.indicator
            (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z := by
      intro z
      have hb := one_le_wEnv s x z
      by_cases h : Torus.eucDist x z < R
      · rw [Set.indicator_of_mem (show z ∈ {z : Torus d | Torus.eucDist x z < R} from h)]
        refine le_trans ?_ le_self_add
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [min_le_left 1 (lam * wEnv s x z)]
      · push Not at h
        rw [Set.indicator_of_mem (show z ∈ {z : Torus d | R ≤ Torus.eucDist x z} from h)]
        refine le_trans ?_ le_add_self
        rw [← ENNReal.ofReal_mul hlam.le]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [min_le_right 1 (lam * wEnv s x z)]
    have hm1 := measurable_ind_near s x R 1
    simp only [pow_one] at hm1
    have hm3 := measurable_ind_far s x R 2
    have hB1 := radial_B1' hd hcrit x R hR0 hR1
    have hB2 := radial_B2' hd hcrit x R hR0 hR1
    have hlogR : Real.log (((d:ℝ) + 1) / R) = Real.log ((d:ℝ) + 1) + (1 / s) * |Real.log lam| := by
      rw [Real.log_div (by positivity) hR0.ne', hR, Real.log_rpow hlam]
      rw [abs_of_neg (Real.log_neg hlam hl1)]
      ring
    calc ∫⁻ z, ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z))
        ≤ ∫⁻ z, ({z : Torus d | Torus.eucDist x z < R}.indicator
            (fun z => ENNReal.ofReal (wEnv s x z)) z +
          ENNReal.ofReal lam * {z : Torus d | R ≤ Torus.eucDist x z}.indicator
            (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z) := lintegral_mono hpt
      _ = (∫⁻ z, {z : Torus d | Torus.eucDist x z < R}.indicator
            (fun z => ENNReal.ofReal (wEnv s x z)) z) +
          ENNReal.ofReal lam * ∫⁻ z, {z : Torus d | R ≤ Torus.eucDist x z}.indicator
            (fun z => ENNReal.ofReal (wEnv s x z ^ 2)) z := by
          rw [lintegral_add_left hm1, lintegral_const_mul _ hm3]
      _ ≤ ENNReal.ofReal (cdR d * (K1 * R ^ s)) + ENNReal.ofReal lam *
            ENNReal.ofReal (cdR d * (4 * (E + Real.log (((d:ℝ) + 1) / R)))) := by
          gcongr
      _ = ENNReal.ofReal (cdR d * (K1 * R ^ s) + lam * (cdR d * (4 * (E + Real.log (((d:ℝ) + 1) / R))))) := by
          rw [← ENNReal.ofReal_mul hlam.le, ← ENNReal.ofReal_add (by positivity)
            (by rw [hlogR]; positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hRs, hlogR]
          have : cdR d * (K1 * lam) + lam * (cdR d * (4 * (E + (Real.log ((d:ℝ) + 1) + 1 / s * |Real.log lam|)))) ≤
              C1 * lam * (1 + |Real.log lam|) := by
            rw [hC1]
            have hll : 0 ≤ lam * |Real.log lam| := mul_nonneg hlam.le hlg
            have h5 : 0 ≤ cdR d * K1 * (lam * |Real.log lam|) := by positivity
            have h6 : 0 ≤ cdR d * (4 * (1 / s)) * lam := by positivity
            have h7 : 0 ≤ cdR d * (4 * (E + Real.log ((d:ℝ) + 1))) * (lam * |Real.log lam|) := by positivity
            nlinarith [h5, h6, h7]
          nlinarith [mul_nonneg hC0n hlam.le, mul_nonneg hC0n (mul_nonneg hlam.le hlg)]


set_option maxHeartbeats 1000000 in
theorem q3_vol {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ x y : Torus d, x ≠ y →
      ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z)) ≤
        ENNReal.ofReal (C * lam * wEnv s x y * (1 + |Real.log lam|)) := by
  obtain ⟨Ccap, hCcap0, hcap⟩ := cap_vol (d := d) hd hcrit
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hd0 : (0:ℝ) < d := by linarith
  have hcd := cdR_nonneg d
  set K1 : ℝ := (1 / (d:ℝ) + 1 / s) with hK1
  have hK1p : 0 < K1 := by positivity
  set E : ℝ := ((d:ℝ) + 1) ^ d / d with hE
  have hE0 : 0 ≤ E := by positivity
  have h2s : (1:ℝ) ≤ 2 ^ s := Real.one_le_rpow (by norm_num) hs0.le
  have h3s : (1:ℝ) ≤ 3 ^ s := Real.one_le_rpow (by norm_num) hs0.le
  set C : ℝ := 2 ^ s * Ccap + 2 * (2 ^ s) ^ 2 * (cdR d * K1) + 3 ^ s * (cdR d * (8 * (E + 2 ^ s / s))) with hC
  have hCn : 0 ≤ C := by positivity
  refine ⟨C, hCn, fun lam hlam x y hxy => ?_⟩
  have hr := rTrunc_pos hxy
  have hr1 := rTrunc_le_one x y
  set r := rTrunc x y with hrdef
  set ρ := r / 2 with hρdef
  have hρ0 : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by linarith
  set a := wEnv s x y with ha
  have ha1 : 1 ≤ a := one_le_wEnv s x y
  have hlg : 0 ≤ |Real.log lam| := abs_nonneg _
  have hpt : ∀ z : Torus d, ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z)) ≤
      ENNReal.ofReal (2 ^ s * a) * ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) +
      ENNReal.ofReal (lam * (2 ^ s * a) ^ 2) * {z : Torus d | Torus.eucDist y z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s y z)) z +
      ENNReal.ofReal (3 ^ s * lam) * {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z ^ 3)) z := by
    intro z
    have hb := one_le_wEnv s x z
    have hc := one_le_wEnv s y z
    have hcb0 : 0 ≤ min 1 (lam * wEnv s x z) := le_min zero_le_one (by positivity)
    have hcb1 : min 1 (lam * wEnv s x z) ≤ lam * wEnv s x z := min_le_right _ _
    by_cases h1 : Torus.eucDist x z < ρ
    · have hcle := wEnv_near hs0 hxy h1
      calc ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z))
          ≤ ENNReal.ofReal (2 ^ s * a) * ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            refine ENNReal.ofReal_le_ofReal ?_
            have h0 : 0 ≤ wEnv s x z * min 1 (lam * wEnv s x z) := by positivity
            calc wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z)
                = (wEnv s x z * min 1 (lam * wEnv s x z)) * wEnv s y z := by ring
              _ ≤ (wEnv s x z * min 1 (lam * wEnv s x z)) * (2 ^ s * a) :=
                  mul_le_mul_of_nonneg_left hcle h0
              _ = _ := by ring
        _ ≤ _ := by
            refine le_trans ?_ le_self_add
            exact le_self_add
    · push Not at h1
      by_cases h2 : Torus.eucDist y z < ρ
      · have hble : wEnv s x z ≤ 2 ^ s * a := by
          have := wEnv_near hs0 (p := y) (q := x) hxy.symm (z := z)
            (by rw [rTrunc_symm y x]; exact h2)
          rwa [wEnv_symm s y x] at this
        rw [Set.indicator_of_mem (show z ∈ {z : Torus d | Torus.eucDist y z < ρ} from h2)]
        calc ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z))
            ≤ ENNReal.ofReal (lam * (2 ^ s * a) ^ 2) * ENNReal.ofReal (wEnv s y z) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              have hb2 : wEnv s x z ^ 2 ≤ (2 ^ s * a) ^ 2 := pow_le_pow_left₀ (by linarith) hble 2
              calc wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z)
                  ≤ wEnv s x z * wEnv s y z * (lam * wEnv s x z) := by gcongr
                _ = lam * wEnv s x z ^ 2 * wEnv s y z := by ring
                _ ≤ lam * (2 ^ s * a) ^ 2 * wEnv s y z := by gcongr
          _ ≤ _ := by
              refine le_trans ?_ le_self_add
              exact le_add_self
      · push Not at h2
        have hcle : wEnv s y z ≤ 3 ^ s * wEnv s x z := wEnv_far hs0 hxy h1 h2
        rw [Set.indicator_of_mem (show z ∈ {z : Torus d | ρ ≤ Torus.eucDist x z} from h1)]
        calc ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z))
            ≤ ENNReal.ofReal (3 ^ s * lam) * ENNReal.ofReal (wEnv s x z ^ 3) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              refine ENNReal.ofReal_le_ofReal ?_
              calc wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z)
                  ≤ wEnv s x z * (3 ^ s * wEnv s x z) * (lam * wEnv s x z) := by gcongr
                _ = 3 ^ s * lam * wEnv s x z ^ 3 := by ring
          _ ≤ _ := le_add_self
  have hmb := measurable_wEnv s x
  have hm0 : Measurable (fun z : Torus d => ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z))) :=
    ENNReal.measurable_ofReal.comp (hmb.mul (measurable_const.min (measurable_const.mul hmb)))
  have hm2 := measurable_ind_near s y ρ 1
  simp only [pow_one] at hm2
  have hm3 := measurable_ind_far s x ρ 3
  have hB1 := radial_B1' hd hcrit y ρ hρ0 hρ1
  have hB3 := radial_B3' hd hcrit x ρ hρ0 hρ1
  have hcp := hcap lam hlam x
  calc ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z))
      ≤ ∫⁻ z, (ENNReal.ofReal (2 ^ s * a) * ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) +
      ENNReal.ofReal (lam * (2 ^ s * a) ^ 2) * {z : Torus d | Torus.eucDist y z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s y z)) z +
      ENNReal.ofReal (3 ^ s * lam) * {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z ^ 3)) z) := lintegral_mono hpt
    _ = ENNReal.ofReal (2 ^ s * a) * (∫⁻ z, ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z))) +
        ENNReal.ofReal (lam * (2 ^ s * a) ^ 2) * (∫⁻ z, {z : Torus d | Torus.eucDist y z < ρ}.indicator
          (fun z => ENNReal.ofReal (wEnv s y z)) z) +
        ENNReal.ofReal (3 ^ s * lam) * (∫⁻ z, {z : Torus d | ρ ≤ Torus.eucDist x z}.indicator
          (fun z => ENNReal.ofReal (wEnv s x z ^ 3)) z) := by
        have hmm : Measurable (fun z : Torus d => ENNReal.ofReal (2 ^ s * a) *
            ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) +
            ENNReal.ofReal (lam * (2 ^ s * a) ^ 2) * {z : Torus d | Torus.eucDist y z < ρ}.indicator
              (fun z => ENNReal.ofReal (wEnv s y z)) z) :=
          (hm0.const_mul _).add (hm2.const_mul _)
        rw [lintegral_add_left hmm, lintegral_add_left (hm0.const_mul _),
          lintegral_const_mul _ hm0, lintegral_const_mul _ hm2, lintegral_const_mul _ hm3]
    _ ≤ ENNReal.ofReal (2 ^ s * a) * ENNReal.ofReal (Ccap * lam * (1 + |Real.log lam|)) +
        ENNReal.ofReal (lam * (2 ^ s * a) ^ 2) * ENNReal.ofReal (cdR d * (K1 * ρ ^ s)) +
        ENNReal.ofReal (3 ^ s * lam) * ENNReal.ofReal (cdR d * (8 * (E + ρ ^ (-s) / s))) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ s * a * (Ccap * lam * (1 + |Real.log lam|)) +
          lam * (2 ^ s * a) ^ 2 * (cdR d * (K1 * ρ ^ s)) +
          3 ^ s * lam * (cdR d * (8 * (E + ρ ^ (-s) / s)))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hr0 : 0 ≤ r := hr.le
        have hrs : r ^ s ≤ 1 := Real.rpow_le_one hr0 hr1 hs0.le
        have hρs : ρ ^ s ≤ r ^ s := Real.rpow_le_rpow hρ0.le (by linarith) hs0.le
        have har : a * r ^ s = r ^ s + 1 := by
          have h : r ^ (-s) * r ^ s = 1 := by rw [← Real.rpow_add hr]; simp
          rw [ha]; unfold wEnv; rw [← hrdef]
          linear_combination h
        have hρneg : ρ ^ (-s) = 2 ^ s * r ^ (-s) := two_rpow_aux hr (by norm_num : (0:ℝ) < 2)
        have hrneg : r ^ (-s) ≤ a := by
          rw [ha]; unfold wEnv; rw [← hrdef]; linarith
        have hrneg0 : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr0 _
        have hlam0 := hlam.le
        have hq : 0 ≤ (cdR d * K1) := by positivity
        have hsecond : lam * (2 ^ s * a) ^ 2 * (cdR d * (K1 * ρ ^ s)) ≤
            lam * a * (2 * (2 ^ s) ^ 2 * (cdR d * K1)) := by
          have h1 : a * ρ ^ s ≤ 2 := by
            calc a * ρ ^ s ≤ a * r ^ s := mul_le_mul_of_nonneg_left hρs (by linarith)
              _ = r ^ s + 1 := har
              _ ≤ 2 := by linarith
          have h2 : 0 ≤ lam * ((2 ^ s) ^ 2 * (cdR d * K1)) := by positivity
          calc lam * (2 ^ s * a) ^ 2 * (cdR d * (K1 * ρ ^ s))
              = lam * ((2 ^ s) ^ 2 * (cdR d * K1)) * (a * (a * ρ ^ s)) := by ring
            _ ≤ lam * ((2 ^ s) ^ 2 * (cdR d * K1)) * (a * 2) := by gcongr
            _ = _ := by ring
        have hthird : 3 ^ s * lam * (cdR d * (8 * (E + ρ ^ (-s) / s))) ≤
            lam * a * (3 ^ s * (cdR d * (8 * (E + 2 ^ s / s)))) := by
          have h1 : ρ ^ (-s) ≤ 2 ^ s * a := by
            rw [hρneg]; exact mul_le_mul_of_nonneg_left hrneg (by positivity)
          have h3 : E + ρ ^ (-s) / s ≤ a * (E + 2 ^ s / s) := by
            have : ρ ^ (-s) / s ≤ 2 ^ s * a / s := div_le_div_of_nonneg_right h1 hs0.le
            have h4 : E ≤ a * E := le_mul_of_one_le_left hE0 ha1
            calc E + ρ ^ (-s) / s ≤ a * E + 2 ^ s * a / s := by linarith
              _ = _ := by ring
          have h5 : 0 ≤ 3 ^ s * lam * (cdR d * 8) := by positivity
          calc 3 ^ s * lam * (cdR d * (8 * (E + ρ ^ (-s) / s)))
              = 3 ^ s * lam * (cdR d * 8) * (E + ρ ^ (-s) / s) := by ring
            _ ≤ 3 ^ s * lam * (cdR d * 8) * (a * (E + 2 ^ s / s)) := by gcongr
            _ = _ := by ring
        have hfirst : 2 ^ s * a * (Ccap * lam * (1 + |Real.log lam|)) =
            lam * a * (2 ^ s * Ccap) * (1 + |Real.log lam|) := by ring
        have hlaC : 0 ≤ lam * a * (2 * (2 ^ s) ^ 2 * (cdR d * K1)) := by positivity
        have hlaD : 0 ≤ lam * a * (3 ^ s * (cdR d * (8 * (E + 2 ^ s / s)))) := by positivity
        have hlaF : 0 ≤ lam * a * (2 ^ s * Ccap) := by positivity
        have : 1 ≤ 1 + |Real.log lam| := by linarith
        calc _ ≤ lam * a * (2 ^ s * Ccap) * (1 + |Real.log lam|) +
              lam * a * (2 * (2 ^ s) ^ 2 * (cdR d * K1)) +
              lam * a * (3 ^ s * (cdR d * (8 * (E + 2 ^ s / s)))) := by
              rw [hfirst]; linarith
          _ ≤ lam * a * (2 ^ s * Ccap) * (1 + |Real.log lam|) +
              lam * a * (2 * (2 ^ s) ^ 2 * (cdR d * K1)) * (1 + |Real.log lam|) +
              lam * a * (3 ^ s * (cdR d * (8 * (E + 2 ^ s / s)))) * (1 + |Real.log lam|) := by
              have e1 := le_mul_of_one_le_right hlaC this
              have e2 := le_mul_of_one_le_right hlaD this
              linarith
          _ = C * lam * a * (1 + |Real.log lam|) := by rw [hC]; ring


theorem min_cap_le (lam b c : ℝ) (hl : 0 ≤ lam) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    min 1 (lam * (1 + b + c)) ≤ lam + min 1 (lam * b) + min 1 (lam * c) := by
  have h1 : 0 ≤ min 1 (lam * b) := le_min zero_le_one (by positivity)
  have h2 : 0 ≤ min 1 (lam * c) := le_min zero_le_one (by positivity)
  by_cases hA : 1 ≤ lam
  · have : min 1 (lam * (1 + b + c)) ≤ 1 := min_le_left _ _
    linarith
  · by_cases hB : 1 ≤ lam * b
    · have : min 1 (lam * (1 + b + c)) ≤ 1 := min_le_left _ _
      have : min 1 (lam * b) = 1 := min_eq_left hB
      linarith
    · by_cases hC : 1 ≤ lam * c
      · have : min 1 (lam * (1 + b + c)) ≤ 1 := min_le_left _ _
        have : min 1 (lam * c) = 1 := min_eq_left hC
        linarith
      · push Not at hB hC
        have e1 : min 1 (lam * b) = lam * b := min_eq_right hB.le
        have e2 : min 1 (lam * c) = lam * c := min_eq_right hC.le
        rw [e1, e2]
        have := min_le_right 1 (lam * (1 + b + c))
        linarith [this]



set_option maxHeartbeats 1000000 in
theorem pinprod_vol {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → ∀ x y : Torus d, x ≠ y →
      ∫⁻ z, ENNReal.ofReal ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z +
          wEnv s x z * wEnv s y z) * min 1 (lam * (1 + wEnv s x z + wEnv s y z))) ≤
        ENNReal.ofReal (C * lam * wEnv s x y * (1 + |Real.log lam| + ellEnv x y)) := by
  obtain ⟨Ccap, hCcap0, hcap⟩ := cap_vol (d := d) hd hcrit
  obtain ⟨Cq, hCq0, hq3⟩ := q3_vol (d := d) hd hcrit
  obtain ⟨Cp, hCp0, hpole⟩ := twopole_vol (d := d) hd hcrit
  set C0 : ℝ := cdR d * ((1 / (d:ℝ) + 1 / s) * 1 ^ s) + 2 with hC0
  have hcd := cdR_nonneg d
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hC0n : 0 ≤ C0 := by positivity
  refine ⟨2 * C0 + 3 * Cp + 2 * Ccap + 2 * Cq, by positivity, fun lam hlam x y hxy => ?_⟩
  set a := wEnv s x y with ha
  have ha1 : 1 ≤ a := one_le_wEnv s x y
  have hlg : 0 ≤ |Real.log lam| := abs_nonneg _
  have hell : 1 ≤ ellEnv x y := by
    unfold ellEnv; linarith [log_one_div_nonneg x y]
  have mb := measurable_wEnv s x
  have mc := measurable_wEnv s y
  -- pointwise bound
  have hpt : ∀ z : Torus d, ENNReal.ofReal ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z +
          wEnv s x z * wEnv s y z) * min 1 (lam * (1 + wEnv s x z + wEnv s y z))) ≤
      ENNReal.ofReal (lam * a) * ENNReal.ofReal (wEnv s x z) +
      ENNReal.ofReal (lam * a) * ENNReal.ofReal (wEnv s y z) +
      ENNReal.ofReal (3 * (lam * a)) * ENNReal.ofReal (wEnv s x z * wEnv s y z) +
      ENNReal.ofReal a * ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) +
      ENNReal.ofReal a * ENNReal.ofReal (wEnv s y z * min 1 (lam * wEnv s y z)) +
      ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z)) +
      ENNReal.ofReal (wEnv s y z * wEnv s x z * min 1 (lam * wEnv s y z)) := by
    intro z
    set b := wEnv s x z with hb
    set c := wEnv s y z with hc
    have hb1 : 1 ≤ b := one_le_wEnv s x z
    have hc1 : 1 ≤ c := one_le_wEnv s y z
    set cb := min 1 (lam * b) with hcb
    set cc := min 1 (lam * c) with hcc
    have hcb0 : 0 ≤ cb := le_min zero_le_one (by positivity)
    have hcc0 : 0 ≤ cc := le_min zero_le_one (by positivity)
    have hcb1 : cb ≤ lam * b := min_le_right _ _
    have hcc1 : cc ≤ lam * c := min_le_right _ _
    have hm := min_cap_le lam b c hlam.le (by linarith) (by linarith)
    have hm0 : 0 ≤ min 1 (lam * (1 + b + c)) := le_min zero_le_one (by positivity)
    have hS : 0 ≤ a * b + a * c + b * c := by positivity
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e1 : (a * b + a * c + b * c) * min 1 (lam * (1 + b + c)) ≤
        (a * b + a * c + b * c) * (lam + cb + cc) := mul_le_mul_of_nonneg_left hm hS
    have e2 : a * b * cc ≤ lam * a * (b * c) := by
      calc a * b * cc ≤ a * b * (lam * c) := mul_le_mul_of_nonneg_left hcc1 (by positivity)
        _ = lam * a * (b * c) := by ring
    have e3 : a * c * cb ≤ lam * a * (b * c) := by
      calc a * c * cb ≤ a * c * (lam * b) := mul_le_mul_of_nonneg_left hcb1 (by positivity)
        _ = lam * a * (b * c) := by ring
    have e4 : b * c * lam ≤ lam * a * (b * c) := by
      have : 0 ≤ lam * (b * c) := by positivity
      calc b * c * lam = lam * (b * c) * 1 := by ring
        _ ≤ lam * (b * c) * a := mul_le_mul_of_nonneg_left ha1 this
        _ = _ := by ring
    have e5 : (a * b + a * c + b * c) * (lam + cb + cc) =
        lam * a * b + lam * a * c + b * c * lam + a * (b * cb) + a * b * cc + a * c * cb +
          a * (c * cc) + b * c * cb + c * b * cc := by ring
    nlinarith [e1, e2, e3, e4, e5]
  have hB0x := radial_B0 hd hcrit x
  have hB0y := radial_B0 hd hcrit y
  have hpl := hpole x y hxy
  have hcx := hcap lam hlam x
  have hcy := hcap lam hlam y
  have hq1 := hq3 lam hlam x y hxy
  have hq2 := hq3 lam hlam y x hxy.symm
  rw [wEnv_symm s y x] at hq2
  calc ∫⁻ z, ENNReal.ofReal ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z +
          wEnv s x z * wEnv s y z) * min 1 (lam * (1 + wEnv s x z + wEnv s y z)))
      ≤ ∫⁻ z, (ENNReal.ofReal (lam * a) * ENNReal.ofReal (wEnv s x z) +
      ENNReal.ofReal (lam * a) * ENNReal.ofReal (wEnv s y z) +
      ENNReal.ofReal (3 * (lam * a)) * ENNReal.ofReal (wEnv s x z * wEnv s y z) +
      ENNReal.ofReal a * ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z)) +
      ENNReal.ofReal a * ENNReal.ofReal (wEnv s y z * min 1 (lam * wEnv s y z)) +
      ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z)) +
      ENNReal.ofReal (wEnv s y z * wEnv s x z * min 1 (lam * wEnv s y z))) := lintegral_mono hpt
    _ = ENNReal.ofReal (lam * a) * (∫⁻ z, ENNReal.ofReal (wEnv s x z)) +
      ENNReal.ofReal (lam * a) * (∫⁻ z, ENNReal.ofReal (wEnv s y z)) +
      ENNReal.ofReal (3 * (lam * a)) * (∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z)) +
      ENNReal.ofReal a * (∫⁻ z, ENNReal.ofReal (wEnv s x z * min 1 (lam * wEnv s x z))) +
      ENNReal.ofReal a * (∫⁻ z, ENNReal.ofReal (wEnv s y z * min 1 (lam * wEnv s y z))) +
      (∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z * min 1 (lam * wEnv s x z))) +
      (∫⁻ z, ENNReal.ofReal (wEnv s y z * wEnv s x z * min 1 (lam * wEnv s y z))) := by
        rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
          lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
          lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
          lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ (by fun_prop),
          lintegral_const_mul _ (by fun_prop)]
    _ ≤ ENNReal.ofReal (lam * a) * ENNReal.ofReal C0 +
      ENNReal.ofReal (lam * a) * ENNReal.ofReal C0 +
      ENNReal.ofReal (3 * (lam * a)) * ENNReal.ofReal (Cp * ellEnv x y) +
      ENNReal.ofReal a * ENNReal.ofReal (Ccap * lam * (1 + |Real.log lam|)) +
      ENNReal.ofReal a * ENNReal.ofReal (Ccap * lam * (1 + |Real.log lam|)) +
      ENNReal.ofReal (Cq * lam * a * (1 + |Real.log lam|)) +
      ENNReal.ofReal (Cq * lam * a * (1 + |Real.log lam|)) := by
        gcongr
    _ = ENNReal.ofReal (lam * a * C0 + lam * a * C0 + 3 * (lam * a) * (Cp * ellEnv x y) +
          a * (Ccap * lam * (1 + |Real.log lam|)) + a * (Ccap * lam * (1 + |Real.log lam|)) +
          Cq * lam * a * (1 + |Real.log lam|) + Cq * lam * a * (1 + |Real.log lam|)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hT : 0 ≤ lam * a := by positivity
        have hM : 1 ≤ 1 + |Real.log lam| + ellEnv x y := by linarith
        have hX : 1 + |Real.log lam| ≤ 1 + |Real.log lam| + ellEnv x y := by linarith
        have hl : ellEnv x y ≤ 1 + |Real.log lam| + ellEnv x y := by linarith
        have f1 : lam * a * C0 ≤ lam * a * C0 * (1 + |Real.log lam| + ellEnv x y) :=
          le_mul_of_one_le_right (by positivity) hM
        have f2 : lam * a * (Cp * ellEnv x y) ≤ lam * a * Cp * (1 + |Real.log lam| + ellEnv x y) := by
          calc lam * a * (Cp * ellEnv x y) = lam * a * Cp * ellEnv x y := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hl (by positivity)
        have f3 : a * (Ccap * lam * (1 + |Real.log lam|)) ≤
            lam * a * Ccap * (1 + |Real.log lam| + ellEnv x y) := by
          calc a * (Ccap * lam * (1 + |Real.log lam|)) = lam * a * Ccap * (1 + |Real.log lam|) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)
        have f4 : Cq * lam * a * (1 + |Real.log lam|) ≤
            lam * a * Cq * (1 + |Real.log lam| + ellEnv x y) := by
          calc Cq * lam * a * (1 + |Real.log lam|) = lam * a * Cq * (1 + |Real.log lam|) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hX (by positivity)
        calc _ ≤ 2 * (lam * a * C0 * (1 + |Real.log lam| + ellEnv x y)) +
              3 * (lam * a * Cp * (1 + |Real.log lam| + ellEnv x y)) +
              2 * (lam * a * Ccap * (1 + |Real.log lam| + ellEnv x y)) +
              2 * (lam * a * Cq * (1 + |Real.log lam| + ellEnv x y)) := by
              nlinarith [f1, f2, f3, f4]
          _ = _ := by ring



theorem pow4_exp_le (a u : ℝ) (ha : 0 ≤ a) (hu : 0 < u) :
    a ^ 4 * Real.exp (-u * a) ≤ 24 * min a (1 / u) ^ 4 := by
  rcases le_or_gt a (1 / u) with h | h
  · rw [min_eq_left h]
    have : Real.exp (-u * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have h4 : 0 ≤ a ^ 4 := by positivity
    nlinarith
  · rw [min_eq_right h.le]
    have hua : 0 ≤ u * a := by positivity
    have h1 := Real.pow_div_factorial_le_exp (u * a) hua 4
    have hf : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hf] at h1
    have hE : 0 < Real.exp (-u * a) := Real.exp_pos _
    have h4 : Real.exp (u * a) * Real.exp (-u * a) = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : (u * a) ^ 4 * Real.exp (-u * a) ≤ 24 := by
      have := mul_le_mul_of_nonneg_right h1 hE.le
      rw [h4] at this
      have e : (u * a) ^ 4 / 24 * Real.exp (-u * a) = (u * a) ^ 4 * Real.exp (-u * a) / 24 := by ring
      linarith
    have hu4 : 0 < u ^ 4 := by positivity
    calc a ^ 4 * Real.exp (-u * a) = ((u * a) ^ 4 * Real.exp (-u * a)) / u ^ 4 := by
          field_simp
      _ ≤ 24 / u ^ 4 := div_le_div_of_nonneg_right h5 hu4.le
      _ = 24 * (1 / u) ^ 4 := by field_simp


theorem exp_pow4_mu {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (1 / u) ^ 2) := by
  have := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨Cv, hCv, hv⟩ := PoleCavityAux.conj_pow hd hcrit c hc ρ hρ 4 (by norm_num)
  refine ⟨max (24 * Cv) 384, by positivity, fun u hu hu1 x => ?_⟩
  set H : ℝ := 1 / u with hH
  have hH1 : 1 ≤ H := by rw [hH, le_div_iff₀ hu]; linarith
  have hpt : ∀ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y))) ≤
      ENNReal.ofReal 24 * ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) := by
    intro y
    rw [← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := pow4_exp_le (gPlus d s c (x - y)) u (hc _) hu
    rw [show gTrunc d s c H (x - y) ^ (4:ℝ) = gTrunc d s c H (x - y) ^ 4 by
      rw [← Real.rpow_natCast]; norm_num]
    exact this
  calc _ ≤ ∫⁻ y, ENNReal.ofReal 24 * ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) ∂(withDensityReal ρ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal 24 * ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) ∂(withDensityReal ρ) := by
        rw [lintegral_const_mul']
        exact ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (max (24 * Cv) 384 * H ^ 2) := by
        rcases le_or_gt 2 H with h2 | h2
        · have := hv H h2 x
          calc _ ≤ ENNReal.ofReal 24 * ENNReal.ofReal (Cv * H ^ ((4:ℝ) - 2)) := by gcongr
            _ = ENNReal.ofReal (24 * (Cv * H ^ ((4:ℝ) - 2))) := (ENNReal.ofReal_mul (by norm_num)).symm
            _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              rw [show ((4:ℝ) - 2) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
              have := le_max_left (24 * Cv) 384
              have hH2 : 0 ≤ H ^ 2 := by positivity
              nlinarith
        · have hb : ∀ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) ≤ ENNReal.ofReal 16 := by
            intro y
            refine ENNReal.ofReal_le_ofReal ?_
            have h0 : 0 ≤ gTrunc d s c H (x - y) := le_min (hc _) (by linarith)
            have : gTrunc d s c H (x - y) ≤ 2 := (min_le_right _ _).trans h2.le
            rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
            calc gTrunc d s c H (x - y) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ h0 this 4
              _ = 16 := by norm_num
          calc ENNReal.ofReal 24 * ∫⁻ y, ENNReal.ofReal (gTrunc d s c H (x - y) ^ (4:ℝ)) ∂(withDensityReal ρ)
              ≤ ENNReal.ofReal 24 * ∫⁻ y, ENNReal.ofReal 16 ∂(withDensityReal ρ) :=
                mul_le_mul' le_rfl (lintegral_mono hb)
            _ = ENNReal.ofReal 24 * ENNReal.ofReal 16 := by simp
            _ = ENNReal.ofReal 384 := by rw [← ENNReal.ofReal_mul (by norm_num)]; norm_num
            _ ≤ _ := by
              refine ENNReal.ofReal_le_ofReal ?_
              have := le_max_right (24 * Cv) 384
              have hH2 : 1 ≤ H ^ 2 := one_le_pow₀ hH1
              nlinarith
    _ = _ := by rw [hH]


theorem exists_box' (z : Torus d) : ∃ y ∈ KernelAux.Box d, KernelAux.boxPt y = z := by
  refine ⟨fun i => ((AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i) : Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) : ℝ),
    fun i => ?_, ?_⟩
  · exact (AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i)).2
  · funext i
    simp [KernelAux.boxPt]

theorem eucDist_sub_zero (x y : Torus d) : Torus.eucDist x y = Torus.eucDist (x - y) 0 := by
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem exists_sing_lower' {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) :
    ∃ (R δ : ℝ), 0 < δ ∧ ∀ w : Euc d, ‖w‖ < δ → w ≠ 0 →
      ‖w‖ ^ (-s) - R ≤ periodicRiesz d s (Torus.mk w) := by
  obtain ⟨r, δ, hδ, hr, hsing⟩ := periodicRiesz_local_singularity hd hs0 hsd
  have hrc : Continuous r := PoleCavityAux.continuous_of_lift'
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  have hbdd : BddBelow (Set.range r) := (isCompact_range hrc).bddBelow
  obtain ⟨b, hb⟩ := hbdd
  refine ⟨-b, δ, hδ, fun w hw hw0 => ?_⟩
  rw [hsing w hw hw0]
  have := hb ⟨Torus.mk w, rfl⟩
  linarith

theorem wEnv_le_gPlus {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ A : ℝ, 0 < A ∧ ∀ x y : Torus d, wEnv s x y ≤ A * (1 + gPlus d s c (x - y)) := by
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨R, δ, hδ, hlow⟩ := exists_sing_lower' hd hs0 hsd
  set δ' : ℝ := min δ 1 with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ one_pos
  have hδ'1 : δ' ≤ 1 := min_le_right _ _
  set A : ℝ := 1 + |R| + |c| + δ' ^ (-s) with hA
  have hApos : 0 < A := by
    have : 0 ≤ δ' ^ (-s) := Real.rpow_nonneg hδ'0.le _
    positivity
  refine ⟨A, hApos, fun x y => ?_⟩
  have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
  obtain ⟨y0, hyB, hy0⟩ := exists_box' (x - y)
  set w0 : Euc d := WithLp.toLp 2 y0 with hw0
  have hmk : Torus.mk w0 = x - y := hy0
  have hw0' : ∀ i, |w0 i| ≤ 1 / 2 := fun i => KernelAux.Box_abs_le hyB i
  have hdist : Torus.eucDist x y = ‖w0‖ := by
    rw [eucDist_sub_zero, ← hmk]; exact eucDist_mk_zero' hw0'
  have hrT : rTrunc x y = min 1 ‖w0‖ := by unfold rTrunc; rw [hdist]
  have hA1 : 0 ≤ δ' ^ (-s) := Real.rpow_nonneg hδ'0.le _
  by_cases hbig : δ' ≤ ‖w0‖
  · have hr1 : δ' ≤ rTrunc x y := by rw [hrT]; exact le_min hδ'1 hbig
    have := wEnv_le_of_ge hs0 hδ'0 hr1
    have h2 : 1 + δ' ^ (-s) ≤ A := by rw [hA]; linarith [abs_nonneg R, abs_nonneg c]
    nlinarith
  · push Not at hbig
    by_cases hz : w0 = 0
    · have : rTrunc x y = 0 := by rw [hrT, hz]; simp
      unfold wEnv; rw [this]
      rw [Real.zero_rpow (by linarith : -s ≠ 0)]
      nlinarith [abs_nonneg R, abs_nonneg c]
    · have hlt : ‖w0‖ < δ := lt_of_lt_of_le hbig (min_le_left _ _)
      have h1 := hlow w0 hlt hz
      rw [hmk] at h1
      have hn1 : ‖w0‖ ≤ 1 := by
        have := min_le_right δ 1
        linarith
      have hrT' : rTrunc x y = ‖w0‖ := by rw [hrT]; exact min_eq_right hn1
      have : wEnv s x y = 1 + ‖w0‖ ^ (-s) := by unfold wEnv; rw [hrT']
      rw [this]
      unfold gPlus at hg0 ⊢
      have hR : R ≤ |R| := le_abs_self R
      have hcc : -c ≤ |c| := neg_le_abs c
      have hA1' : 1 ≤ A := by rw [hA]; linarith [abs_nonneg R, abs_nonneg c]
      have hpos : 0 ≤ periodicRiesz d s (x - y) + c := hg0
      nlinarith [abs_nonneg R, abs_nonneg c]


theorem logEN_eq (N : ℕ) (hN : 1 ≤ N) : logEN N = 1 + Real.log N := by
  unfold logEN
  have : (N : ℝ) ≠ 0 := by positivity
  rw [Real.log_mul (Real.exp_ne_zero 1) this, Real.log_exp]

set_option maxHeartbeats 1000000 in
theorem exp_moments {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      (∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(κ / N) * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(κ / N) * gPlus d s c (x - y)))
          ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (N : ℝ) ^ 2)) := by
  have := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨A, hA, hAw⟩ := wEnv_le_gPlus hd hcrit c hc
  obtain ⟨C5, hC5, h5⟩ := PoleCavityAux.conj_expo hd hcrit c hc ρ hρ
  obtain ⟨C4, hC4, h4⟩ := exp_pow4_mu hd hcrit c hc ρ hρ
  set C2 : ℝ := 2 * A ^ 2 * (1 + C5 * (1 + |Real.log κ|) + C5) with hC2
  set C4' : ℝ := 8 * A ^ 4 * (1 + C4 * (1 / κ + 1) ^ 2) with hC4'
  refine ⟨max C2 C4', by positivity, fun N hN x => ?_⟩
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) < N := by linarith
  set u : ℝ := min (κ / N) 1 with hu
  have hu0 : 0 < u := lt_min (by positivity) one_pos
  have hu1 : u ≤ 1 := min_le_right _ _
  have huk : u ≤ κ / N := min_le_left _ _
  have hlogu : |Real.log u| ≤ Real.log N + |Real.log κ| := by
    have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
    rcases le_or_gt 1 (κ / N) with h | h
    · rw [hu, min_eq_right h, Real.log_one]; simp; positivity
    · rw [hu, min_eq_left h.le, Real.log_div hκ.ne' hN0.ne']
      calc |Real.log κ - Real.log N| ≤ |Real.log κ| + |Real.log N| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hlN]; ring
  have hexp : ∀ g : ℝ, 0 ≤ g → Real.exp (-(κ / N) * g) ≤ Real.exp (-u * g) := by
    intro g hg
    exact Real.exp_le_exp.2 (by nlinarith)
  have hE1 : ∀ g : ℝ, 0 ≤ g → Real.exp (-u * g) ≤ 1 := by
    intro g hg
    exact Real.exp_le_one_iff.2 (by nlinarith)
  have hlogEN := logEN_eq N (by omega)
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hC2n : 0 ≤ C2 := by positivity
  have hC4n : 0 ≤ C4' := by positivity
  constructor
  · -- second moment
    have hpt : ∀ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(κ / N) * gPlus d s c (x - y))) ≤
        ENNReal.ofReal (2 * A ^ 2) * (ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) +
          ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))) := by
      intro y
      have hg := hc (x - y)
      set g := gPlus d s c (x - y) with hgdef
      have hg0 : 0 ≤ g := hg
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw := hAw x y
      have hw1 := one_le_wEnv s x y
      have hw2 : wEnv s x y ^ 2 ≤ (A * (1 + g)) ^ 2 := pow_le_pow_left₀ (by linarith) hw 2
      have he := hexp g hg0
      have hE0 := Real.exp_pos (-u * g)
      calc wEnv s x y ^ 2 * Real.exp (-(κ / N) * g)
          ≤ (A * (1 + g)) ^ 2 * Real.exp (-u * g) := by
            apply mul_le_mul hw2 he (Real.exp_pos _).le (by positivity)
        _ ≤ 2 * A ^ 2 * (Real.exp (-u * g) + g ^ 2 * Real.exp (-u * g)) := by
            have : (A * (1 + g)) ^ 2 ≤ 2 * A ^ 2 * (1 + g ^ 2) := by nlinarith [sq_nonneg (1 - g), sq_nonneg A]
            calc (A * (1 + g)) ^ 2 * Real.exp (-u * g) ≤ 2 * A ^ 2 * (1 + g ^ 2) * Real.exp (-u * g) :=
                  mul_le_mul_of_nonneg_right this hE0.le
              _ = _ := by ring
    calc ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(κ / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (2 * A ^ 2) * (ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) +
          ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))) ∂(withDensityReal ρ) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 * A ^ 2) * ((∫⁻ y, ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)) +
          ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)) := by
          have hmx : Measurable (fun y : Torus d => ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y)))) := by
            have : Measurable (fun y : Torus d => gPlus d s c (x - y)) :=
              (PoleCavityAux.measurable_gPlus hd (by rw [hcrit]; positivity) (by rw [hcrit]; linarith) c).comp
                (measurable_const.sub measurable_id)
            fun_prop
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmx]
      _ ≤ ENNReal.ofReal (2 * A ^ 2) * (ENNReal.ofReal 1 + ENNReal.ofReal (C5 * (1 + |Real.log u|))) := by
          gcongr
          · calc ∫⁻ y, ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)
                ≤ ∫⁻ y, ENNReal.ofReal 1 ∂(withDensityReal ρ) :=
                  lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hE1 _ (hc _))
              _ = ENNReal.ofReal 1 := by simp
          · exact h5 u hu0 hu1 x
      _ = ENNReal.ofReal (2 * A ^ 2 * (1 + C5 * (1 + |Real.log u|))) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (max C2 C4' * logEN N) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hlogEN]
          have hm := le_max_left C2 C4'
          have : 2 * A ^ 2 * (1 + C5 * (1 + |Real.log u|)) ≤ C2 * (1 + Real.log N) := by
            rw [hC2]
            have step : 1 + C5 * (1 + |Real.log u|) ≤
                (1 + C5 * (1 + |Real.log κ|) + C5) * (1 + Real.log N) := by
              have e1 : C5 * (1 + |Real.log u|) ≤ C5 * (1 + Real.log N + |Real.log κ|) :=
                mul_le_mul_of_nonneg_left (by linarith) hC5.le
              have e2 := mul_nonneg hC5.le hlN
              have e3 := mul_nonneg (mul_nonneg hC5.le (abs_nonneg (Real.log κ))) hlN
              nlinarith [e1, e2, e3, hlN]
            calc 2 * A ^ 2 * (1 + C5 * (1 + |Real.log u|))
                ≤ 2 * A ^ 2 * ((1 + C5 * (1 + |Real.log κ|) + C5) * (1 + Real.log N)) :=
                  mul_le_mul_of_nonneg_left step (by positivity)
              _ = _ := by ring
          nlinarith [mul_le_mul_of_nonneg_right hm (by linarith : (0:ℝ) ≤ 1 + Real.log N)]
  · -- fourth moment
    have hpt : ∀ y, ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(κ / N) * gPlus d s c (x - y))) ≤
        ENNReal.ofReal (8 * A ^ 4) * (ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) +
          ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y)))) := by
      intro y
      have hg := hc (x - y)
      set g := gPlus d s c (x - y) with hgdef
      have hg0 : 0 ≤ g := hg
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hw := hAw x y
      have hw1 := one_le_wEnv s x y
      have hw2 : wEnv s x y ^ 4 ≤ (A * (1 + g)) ^ 4 := pow_le_pow_left₀ (by linarith) hw 4
      have he := hexp g hg0
      have hE0 := Real.exp_pos (-u * g)
      calc wEnv s x y ^ 4 * Real.exp (-(κ / N) * g)
          ≤ (A * (1 + g)) ^ 4 * Real.exp (-u * g) := by
            apply mul_le_mul hw2 he (Real.exp_pos _).le (by positivity)
        _ ≤ 8 * A ^ 4 * (Real.exp (-u * g) + g ^ 4 * Real.exp (-u * g)) := by
            have : (A * (1 + g)) ^ 4 ≤ 8 * A ^ 4 * (1 + g ^ 4) := by
              have h1 : (1 + g) ^ 4 ≤ 8 * (1 + g ^ 4) := by
                nlinarith [sq_nonneg (1 - g), sq_nonneg (1 + g), sq_nonneg (g ^ 2 - 1),
                  sq_nonneg (g - 1), mul_nonneg hg0 hg0, sq_nonneg (g ^ 2 - g)]
              calc (A * (1 + g)) ^ 4 = A ^ 4 * (1 + g) ^ 4 := by ring
                _ ≤ A ^ 4 * (8 * (1 + g ^ 4)) := mul_le_mul_of_nonneg_left h1 (by positivity)
                _ = _ := by ring
            calc (A * (1 + g)) ^ 4 * Real.exp (-u * g) ≤ 8 * A ^ 4 * (1 + g ^ 4) * Real.exp (-u * g) :=
                  mul_le_mul_of_nonneg_right this hE0.le
              _ = _ := by ring
    have hinvu : 1 / u ≤ N * (1 / κ + 1) := by
      rcases le_or_gt 1 (κ / N) with h | h
      · rw [hu, min_eq_right h]
        have : (1:ℝ) ≤ N * (1 / κ + 1) := by
          have : 0 ≤ (N:ℝ) * (1 / κ) := by positivity
          have e : (N:ℝ) * (1 / κ + 1) = N * (1 / κ) + N := by ring
          linarith
        simpa using this
      · rw [hu, min_eq_left h.le]
        have : 1 / (κ / N) = N / κ := by field_simp
        rw [this]
        have : (N:ℝ) / κ = N * (1 / κ) := by ring
        rw [this]
        have e : (N:ℝ) * (1 / κ + 1) = N * (1 / κ) + N := by ring
        linarith
    calc ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(κ / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ∫⁻ y, ENNReal.ofReal (8 * A ^ 4) * (ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) +
          ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y)))) ∂(withDensityReal ρ) :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (8 * A ^ 4) * ((∫⁻ y, ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)) +
          ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 4 * Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)) := by
          have hmx : Measurable (fun y : Torus d => ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y)))) := by
            have : Measurable (fun y : Torus d => gPlus d s c (x - y)) :=
              (PoleCavityAux.measurable_gPlus hd (by rw [hcrit]; positivity) (by rw [hcrit]; linarith) c).comp
                (measurable_const.sub measurable_id)
            fun_prop
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hmx]
      _ ≤ ENNReal.ofReal (8 * A ^ 4) * (ENNReal.ofReal 1 + ENNReal.ofReal (C4 * (1 / u) ^ 2)) := by
          gcongr
          · calc ∫⁻ y, ENNReal.ofReal (Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ)
                ≤ ∫⁻ y, ENNReal.ofReal 1 ∂(withDensityReal ρ) :=
                  lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hE1 _ (hc _))
              _ = ENNReal.ofReal 1 := by simp
          · exact h4 u hu0 hu1 x
      _ = ENNReal.ofReal (8 * A ^ 4 * (1 + C4 * (1 / u) ^ 2)) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal (max C2 C4' * (N : ℝ) ^ 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hm := le_max_right C2 C4'
          have hu2 : (1 / u) ^ 2 ≤ (N * (1 / κ + 1)) ^ 2 :=
            pow_le_pow_left₀ (one_div_nonneg.2 hu0.le) hinvu 2
          have hN2' : 1 ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
          have : 8 * A ^ 4 * (1 + C4 * (1 / u) ^ 2) ≤ C4' * (N : ℝ) ^ 2 := by
            rw [hC4']
            have h1 : C4 * (1 / u) ^ 2 ≤ C4 * (1 / κ + 1) ^ 2 * (N : ℝ) ^ 2 := by
              calc C4 * (1 / u) ^ 2 ≤ C4 * (N * (1 / κ + 1)) ^ 2 := mul_le_mul_of_nonneg_left hu2 hC4.le
                _ = _ := by ring
            have h2 : 1 ≤ (N : ℝ) ^ 2 := hN2'
            have h8 : 0 ≤ 8 * A ^ 4 := by positivity
            calc 8 * A ^ 4 * (1 + C4 * (1 / u) ^ 2)
                ≤ 8 * A ^ 4 * ((N : ℝ) ^ 2 + C4 * (1 / κ + 1) ^ 2 * (N : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left (by linarith) h8
              _ = _ := by ring
          nlinarith [mul_le_mul_of_nonneg_right hm (by positivity : (0:ℝ) ≤ (N:ℝ) ^ 2)]


end PairCorrAux

end Lemma411Aux

/-- Lemma 4.11 `M:Q:lem:integrals` (source lines 4563-4577): for each fixed `a > 0`, uniformly
on the torus and in `N ≥ 2`, with `λ = β/N` and the retained repulsion written with `g_+`,
`Q:eq:radial-moments`, `Q:eq:two-pole-convolution` and `Q:eq:pin-product-integral` (off the
corresponding diagonals). -/
theorem critical_envelope_integrals (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ a > 0, ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      (∀ x : Torus d,
        ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(a * (β / N)) * gPlus d s c (x - y)))
            ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * logEN N) ∧
        ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(a * (β / N)) * gPlus d s c (x - y)))
            ∂(withDensityReal ρ) ≤ ENNReal.ofReal (C * (N : ℝ) ^ 2)) ∧
      (∀ x y : Torus d, x ≠ y →
        ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * ellEnv x y)) ∧
      (∀ x y : Torus d, x ≠ y →
        ∫⁻ z, ENNReal.ofReal
            ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) *
              min 1 ((β / N) * (1 + wEnv s x z + wEnv s y z))) ∂(withDensityReal ρ) ≤
          ENNReal.ofReal (C * (β / N) * wEnv s x y * (logEN N + ellEnv x y))) := by
  intro a ha
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨Ce, hCe0, hexp⟩ := PairCorrAux.exp_moments hd hcrit c hc ρ hρ (a * β) (by positivity)
  obtain ⟨Cp, hCp0, hpole⟩ := PairCorrAux.twopole_vol (d := d) hd hcrit
  obtain ⟨Cq, hCq0, hpin⟩ := PairCorrAux.pinprod_vol (d := d) hd hcrit
  set C : ℝ := max Ce (max (Λ * Cp) (Λ * Cq * (1 + |Real.log β|))) with hC
  have hCe : Ce ≤ C := le_max_left _ _
  have hC2 : Λ * Cp ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Λ * Cq * (1 + |Real.log β|) ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, fun N hN => ⟨fun x => ?_, fun x y hxy => ?_, fun x y hxy => ?_⟩⟩
  · have hN1 : 1 ≤ N := by omega
    have hL : 0 ≤ logEN N := by
      rw [PairCorrAux.logEN_eq N hN1]; linarith [Real.log_nonneg (by exact_mod_cast hN1 : (1:ℝ) ≤ N)]
    have e : a * (β / N) = a * β / N := by ring
    rw [e]
    obtain ⟨h1, h2⟩ := hexp N hN x
    exact ⟨h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCe hL)),
      h2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCe (by positivity)))⟩
  · calc ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal (wEnv s x z * wEnv s y z) :=
          PoleCavityAux.lintegral_mu_le_vol hΛ _
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (Cp * ellEnv x y) := by gcongr; exact hpole x y hxy
      _ = ENNReal.ofReal (Λ * (Cp * ellEnv x y)) := (ENNReal.ofReal_mul hΛ0.le).symm
      _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : 0 ≤ ellEnv x y := by
          unfold ellEnv; linarith [PairCorrAux.log_one_div_nonneg x y]
        calc Λ * (Cp * ellEnv x y) = (Λ * Cp) * ellEnv x y := by ring
          _ ≤ C * ellEnv x y := mul_le_mul_of_nonneg_right hC2 this
  · have hN1 : 1 ≤ N := by omega
    have hN0 : (0:ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hlam : 0 < β / N := by positivity
    have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    have hlog : |Real.log (β / N)| ≤ |Real.log β| + Real.log N := by
      rw [Real.log_div hβ.ne' hN0.ne']
      calc |Real.log β - Real.log N| ≤ |Real.log β| + |Real.log N| := abs_sub _ _
        _ = _ := by rw [abs_of_nonneg hlogN]
    have hell : 1 ≤ ellEnv x y := by
      unfold ellEnv; linarith [PairCorrAux.log_one_div_nonneg x y]
    have hLN := PairCorrAux.logEN_eq N hN1
    calc ∫⁻ z, ENNReal.ofReal
            ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) *
              min 1 ((β / N) * (1 + wEnv s x z + wEnv s y z))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal Λ * ∫⁻ z, ENNReal.ofReal
            ((wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z) *
              min 1 ((β / N) * (1 + wEnv s x z + wEnv s y z))) :=
          PoleCavityAux.lintegral_mu_le_vol hΛ _
      _ ≤ ENNReal.ofReal Λ * ENNReal.ofReal (Cq * (β / N) * wEnv s x y *
            (1 + |Real.log (β / N)| + ellEnv x y)) := by
          gcongr; exact hpin (β / N) hlam x y hxy
      _ = ENNReal.ofReal (Λ * (Cq * (β / N) * wEnv s x y * (1 + |Real.log (β / N)| + ellEnv x y))) :=
          (ENNReal.ofReal_mul hΛ0.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hw1 := PairCorrAux.one_le_wEnv s x y
          have h1 : 1 + |Real.log (β / N)| + ellEnv x y ≤
              (1 + |Real.log β|) * (logEN N + ellEnv x y) := by
            rw [hLN]
            nlinarith [abs_nonneg (Real.log β), mul_nonneg (abs_nonneg (Real.log β)) hlogN,
              mul_nonneg (abs_nonneg (Real.log β)) (by linarith : (0:ℝ) ≤ ellEnv x y)]
          have h0 : 0 ≤ Λ * Cq * ((β / N) * wEnv s x y) := by positivity
          calc Λ * (Cq * (β / N) * wEnv s x y * (1 + |Real.log (β / N)| + ellEnv x y))
              = Λ * Cq * ((β / N) * wEnv s x y) * (1 + |Real.log (β / N)| + ellEnv x y) := by ring
            _ ≤ Λ * Cq * ((β / N) * wEnv s x y) * ((1 + |Real.log β|) * (logEN N + ellEnv x y)) :=
                mul_le_mul_of_nonneg_left h1 h0
            _ = (Λ * Cq * (1 + |Real.log β|)) * (β / N) * wEnv s x y * (logEN N + ellEnv x y) := by ring
            _ ≤ C * (β / N) * wEnv s x y * (logEN N + ellEnv x y) := by
                have : 0 ≤ (β / N) * wEnv s x y * (logEN N + ellEnv x y) := by
                  have : 0 ≤ logEN N := by
                    rw [hLN]; linarith
                  positivity
                calc (Λ * Cq * (1 + |Real.log β|)) * (β / N) * wEnv s x y * (logEN N + ellEnv x y)
                    = (Λ * Cq * (1 + |Real.log β|)) * ((β / N) * wEnv s x y * (logEN N + ellEnv x y)) := by ring
                  _ ≤ C * ((β / N) * wEnv s x y * (logEN N + ellEnv x y)) :=
                      mul_le_mul_of_nonneg_right hC3 this
                  _ = _ := by ring

/- Route and status (EQ-01b, open).  Source lines 4607-4636 via `Q:eq:resampling`, `dP_{N,β}/dR_N ≤ C`
and `Q:eq:reference-input` (the Efron-Stein type variance bound for the weak reference and the
domination of `P_{N,β}` by `R_N` are inputs of the reference construction, not available in the
repository), followed by the integrals of `critical_envelope_integrals` (Lemma 4.11, proved). 
Attempt 2: blocked on a missing input.  The statement is about `canonicalGibbs`; the proof needs
`dP_{N,β}/dR_N ≤ C` for the calibrated weak reference `R_N` (Prop 5.5 / the `R_N` of Section 5, not
constructed in the repository; `Energy/WeakReference.lean` has `weak_marginal_aux` sorry'd) and
`Q:eq:reference-input` for `R_N`.  `weak_resampling` / `weak_linear_variance` would then give
`Q:eq:resampling`.-/

/-- Proposition 4.12 `M:Q:prop:moments` (source lines 4607-4636), under `P_{N,β}`, with
constants homogeneous quadratic in the kernel bound `K`:
`Q:eq:psi-moments` `Var F_N(ψ) + E ∑_i |∇_i F_N(ψ)|² ≤ C K²/N`;
`Q:eq:j-moments` `Var F_N(j) ≤ C K² L_N/N` for canonical symmetric `|j| ≤ K w`;
`Q:eq:b-moments` `Var[N^{-5/2} ∑_{i≠j} b] ≤ C K²/N` for symmetric `|b| ≤ K w²`;
`Q:eq:triple-moments` `Var[N^{-5/2} ∑_{distinct} g₃] ≤ C K² L_N²/N²` for symmetric canonical
`g₃` with `Q:eq:triple-size`. -/
theorem pair_moments (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ C₀ : ℝ,
      (∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), Measurable (Function.uncurry ψ) → IsSymmPair ψ →
        IsCanonicalPair (withDensityReal ρ) ψ → PsiSize s K ψ → ∀ N : ℕ, 2 ≤ N →
          evariance (Fstat ψ) (canonicalGibbs (periodicRiesz d s) V N β) +
              ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
                ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 / N)) ∧
      (∀ (K : ℝ) (j : Torus d → Torus d → ℝ), Measurable (Function.uncurry j) → IsSymmPair j →
        IsCanonicalPair (withDensityReal ρ) j → (∀ x y, x ≠ y → |j x y| ≤ K * wEnv s x y) →
        ∀ N : ℕ, 2 ≤ N →
          evariance (Fstat j) (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 * logEN N / N)) ∧
      (∀ (K : ℝ) (b : Torus d → Torus d → ℝ), Measurable (Function.uncurry b) → IsSymmPair b →
        (∀ x y, x ≠ y → |b x y| ≤ K * wEnv s x y ^ 2) → ∀ N : ℕ, 2 ≤ N →
          evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X)
              (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 / N)) ∧
      (∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
        Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
        IsSymmTriple g3 → IsCanonicalTriple (withDensityReal ρ) g3 →
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤
          K * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) →
        ∀ N : ℕ, 2 ≤ N →
          evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X)
              (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 * logEN N ^ 2 / (N : ℝ) ^ 2)) := by
  sorry

/-! ### The two-particle Poisson equation (source lines 4709-4735) -/

/-- `F_μ = ∇(g*μ)` (source line 4711; for `μ = ρ dx` smooth this is the principal-value force
`∇g*μ`, without a non-integrable Bochner integral at `d = 2`). -/
def forceField (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (x : Torus d) : Euc d :=
  Torus.grad (convMeasure (periodicRiesz d s) (withDensityReal ρ)) x

/-- `Jf(x) = ∫ ∇g(x-y)·∇f(y) μ(dy) = ∑_j ∂_j [g*(ρ ∂_j f)](x)` (`Q:eq:backward`; the source
notes that at `d = 2` the integral is a principal value equal to this derivative). -/
def Jop (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  Torus.div (fun z => WithLp.toLp 2 fun j =>
    convFun (periodicRiesz d s) (fun y => ρ y * Torus.partialDeriv j f y) z) x

/-- `Bf = β⁻¹ Δf - (∇V + F_μ)·∇f` (`Q:eq:backward`, `ν = β⁻¹`). -/
def Bop (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ)
    (x : Torus d) : ℝ :=
  β⁻¹ * Torus.laplacian f x - inner ℝ (Torus.grad V x + forceField d s ρ x) (Torus.grad f x)

/-- The projected backward generator `𝒜 f = P_μ[Bf + Jf]` (`Q:eq:backward`). -/
def projGen (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ) :
    Torus d → ℝ :=
  projMean (withDensityReal ρ) fun x => Bop d s V β ρ f x + Jop d s ρ f x

/-- `𝒜_x ψ(x,y)`: the generator acting in the first variable. -/
def genFst (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ)
    (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  projGen d s V β ρ (fun z => ψ z y) x

/-- `𝒜_y ψ(x,y)`: the generator acting in the second variable. -/
def genSnd (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ)
    (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  projGen d s V β ρ (fun z => ψ x z) y

/-- `𝒥ψ = (P_x J_x + P_y J_y) ψ` (source line 4869). -/
def Jpair (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  projMean (withDensityReal ρ) (fun z => Jop d s ρ (fun w => ψ w y) z) x +
    projMean (withDensityReal ρ) (fun z => Jop d s ρ (fun w => ψ x w) z) y

/-- `h_f(x,y) = (∇f(x) - ∇f(y))·∇g(x-y)` (`Q:eq:H-source`, also `E:eq:hphi`). -/
def hTransport (d : ℕ) (s : ℝ) (f : Torus d → ℝ) (x y : Torus d) : ℝ :=
  inner ℝ (Torus.grad f x - Torus.grad f y) (periodicRieszGrad d s (x - y))

/-- Canonical (double) centering `(P_μ ⊗ P_μ) h`. -/
def canonicalCenter (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  h x y - ∫ y', h x y' ∂μ - ∫ x', h x' y ∂μ + ∫ x', ∫ y', h x' y' ∂μ ∂μ

/-- `H_f = ½ P_x P_y h_f` (`Q:eq:H-source`). -/
def Hsource (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ) (x y : Torus d) : ℝ :=
  (1 / 2) * canonicalCenter (withDensityReal ρ) (hTransport d s f) x y

/-- `a_f(x) = ½ ∫ h_f(x,y) μ(dy)` (`Q:eq:H-source`). -/
def aCoef (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (f : Torus d → ℝ) (x : Torus d) : ℝ :=
  (1 / 2) * ∫ y, hTransport d s f x y ∂(withDensityReal ρ)

/-- `|f|_K = ∑_{1≤|α|≤K} ‖D^α f‖_∞`, represented by the equivalent seminorm
`∑_{1 ≤ j ≤ K} sup ‖D^j f‖` (`Q:eq:test-seminorm`). -/
def posSeminorm (K : ℕ) (f : Torus d → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 K, ⨆ x, ‖iteratedFDeriv ℝ j (Torus.lift f) x‖

/-- The conclusions of Proposition 4.13 for a single test `f` with kernel constant `K₁`:
`ψ` symmetric, canonical, `Q:eq:psi-size` with constant `K₁`, the Poisson equation
`-(𝒜_x + 𝒜_y) ψ = H_f` pointwise off the diagonal, and `𝒥ψ` canonical with `|𝒥ψ| ≤ K₁ w`. -/
structure IsPairCorrector (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) (ρ : Torus d → ℝ)
    (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ) : Prop where
  measurable : Measurable (Function.uncurry ψ)
  symm : IsSymmPair ψ
  canonical : IsCanonicalPair (withDensityReal ρ) ψ
  size : PsiSize s K₁ ψ
  poisson : ∀ x y, x ≠ y → -(genFst d s V β ρ ψ x y + genSnd d s V β ρ ψ x y) = Hsource d s ρ f x y
  jpair_canonical : IsCanonicalPair (withDensityReal ρ) (Jpair d s ρ ψ)
  jpair_bound : ∀ x y, x ≠ y → |Jpair d s ρ ψ x y| ≤ K₁ * wEnv s x y

/- Route and status (EQ-01b, open).  Needs the periodic pair inverse (Lemma 4.14,
`periodic_pair_inverse`, ADJ-01) for `-(𝒜_x+𝒜_y)`, a Schauder/regularity bootstrap for the
singular pair equation giving `Q:eq:psi-size` with constant `C|f|_K`, the bounds on `𝒥ψ` and the
`L²` bound on `a_f`; none of this is in the repository. 
Attempt 2: `periodic_pair_inverse` (Lemma 4.14) only inverts doubly centered kernels in `C^J`;
`H_f` is singular (`~ r^{-s-1}`) on the diagonal, so the singular-source analysis
(local parametrix + Schauder bootstrap giving `Q:eq:psi-size`, bounds on `𝒥ψ`, `a_f`) is still
missing; Prop 4.25 does not supply it.-/

/-- Proposition 4.13 `M:Q:prop:poisson` (source lines 4729-4735), `Q:eq:pair-poisson`: a map
`f ↦ ψ_f`, linear on smooth tests, into symmetric canonical kernels with
`-(𝒜_x + 𝒜_y) ψ_f = H_f` pointwise off the diagonal, the bounds `Q:eq:psi-size` with constant
`C|f|_K` (`K = 8d + 80`), `𝒥ψ_f` canonical and `≤ C|f|_K w`, and `a_f` bounded with
`‖a_f‖_{L²(μ)} ≤ C|f|_K`. The distributional form of the equation and the bounds for "any
required finite number of tangential derivatives up to four" are not encoded. -/
theorem pair_poisson (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ (Ψ : (Torus d → ℝ) → Torus d → Torus d → ℝ) (C : ℝ),
      (∀ (f f' : Torus d → ℝ) (a b : ℝ), Torus.IsSmooth f → Torus.IsSmooth f' →
        Ψ (a • f + b • f') = a • Ψ f + b • Ψ f') ∧
      ∀ f : Torus d → ℝ, Torus.IsSmooth f →
        IsPairCorrector d s V β ρ f (C * posSeminorm (8 * d + 80) f) (Ψ f) ∧
        (∃ M : ℝ, ∀ x, |aCoef d s ρ f x| ≤ M) ∧
        eLpNorm (aCoef d s ρ f) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * posSeminorm (8 * d + 80) f) := by
  sorry

/-! ### The lifted generator identity (source lines 4865-4934) -/

/-- `K(x,z) = ∇g(x-z) - F_μ(x)` (`Q:eq:centered-force`). -/
def centeredForce (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (x z : Torus d) : Euc d :=
  periodicRieszGrad d s (x - z) - forceField d s ρ x

/-- `∇_x ψ(x,y)`. -/
def gradFst (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : Euc d := Torus.grad (fun z => ψ z y) x

/-- `∇_y ψ(x,y)`. -/
def gradSnd (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : Euc d := Torus.grad (fun z => ψ x z) y

/-- `T_ψ(x,y,z) = -K(x,z)·∇_xψ(x,y) - K(y,z)·∇_yψ(x,y)` (`Q:eq:T-unsym`). -/
def Tpsi (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (x y z : Torus d) : ℝ :=
  -inner ℝ (centeredForce d s ρ x z) (gradFst ψ x y) - inner ℝ (centeredForce d s ρ y z) (gradSnd ψ x y)

/-- `G_ψ = T̄_ψ - ⅓[𝒥ψ(x,y) + 𝒥ψ(x,z) + 𝒥ψ(y,z)]`, with
`T̄_ψ = ⅓[T_ψ(x,y,z) + T_ψ(x,z,y) + T_ψ(y,z,x)]` (`Q:eq:T-sym`, `Q:eq:T-canonical`). -/
def Gpsi (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (x y z : Torus d) : ℝ :=
  (1 / 3) * (Tpsi d s ρ ψ x y z + Tpsi d s ρ ψ x z y + Tpsi d s ρ ψ y z x) -
    (1 / 3) * (Jpair d s ρ ψ x y + Jpair d s ρ ψ x z + Jpair d s ρ ψ y z)

/-- `V_ψ(x,y) = F_μ(x)·∇_xψ(x,y) + F_μ(y)·∇_yψ(x,y)` (`Q:eq:Vpair`). -/
def Vpsi (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  inner ℝ (forceField d s ρ x) (gradFst ψ x y) + inner ℝ (forceField d s ρ y) (gradSnd ψ x y)

/-- `B_ψ(x,y) = ∇g(x-y)·(∇_x - ∇_y)ψ(x,y) - 2 V_ψ(x,y)` (`Q:eq:Bpair`). -/
def Bpsi (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → Torus d → ℝ) (x y : Torus d) : ℝ :=
  inner ℝ (periodicRieszGrad d s (x - y)) (gradFst ψ x y - gradSnd ψ x y) - 2 * Vpsi d s ρ ψ x y

/- Route and status (EQ-01b, open).  Source lines 4885-4905.  Symmetry of `G_ψ` and `B_ψ` is
algebraic (uses `ψ` symmetric and `∇g` odd).  Canonicity needs `∫K(x,z)μ(dz)=0` (principal value
at `d = 2`), the integration by parts `μ_y[J_yψ(x,y)] = -∫F_μ·∇_zψ(x,z)μ(dz)` and Fubini for the
symmetrised (absolutely integrable) combination; the envelope needs the segment/Hessian bound
`Q:eq:gradient-difference-bound` on the torus and `|∇g| ≤ C(1+r^{-s-1})`
(`periodicRiesz_grad_bound`), `‖F_μ‖_∞ < ∞`. 
Attempt 2: not started; needs the principal-value identities `∫K(x,z)μ(dz)=0` (`F_μ = ∇(g*μ)`
equals the PV of `∇g*μ` at `d = 2`) and the singular integration by parts for `Jop`, none of which
are in the repository.-/

/-- Lemma 4.15 `M:Q:lem:triple-canonical` (source lines 4882-4884), stated for every kernel
with the conclusions of Proposition 4.13 (the proof uses only those): `G_ψ` is symmetric and
canonical and satisfies `Q:eq:triple-size` with coefficient `C K₁`; `B_ψ` is symmetric and
bounded by `C K₁ w²`. -/
theorem triple_canonical (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ →
        IsSymmTriple (Gpsi d s ρ ψ) ∧ IsCanonicalTriple (withDensityReal ρ) (Gpsi d s ρ ψ) ∧
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |Gpsi d s ρ ψ x y z| ≤
          C * K₁ * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) ∧
        IsSymmPair (Bpsi d s ρ ψ) ∧
        (∀ x y, x ≠ y → |Bpsi d s ρ ψ x y| ≤ C * K₁ * wEnv s x y ^ 2) := by
  sorry

/-- The generator of the canonical gradient particle dynamics,
`𝓛Φ = ∑_i [β⁻¹ Δ_i Φ - (∇V(x_i) + N⁻¹ ∑_{j≠i} ∇g(x_i - x_j))·∇_i Φ]`. -/
def particleGen (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (β : ℝ) {N : ℕ} (Φ : Config d N → ℝ)
    (X : Config d N) : ℝ :=
  ∑ i, (β⁻¹ * configLap Φ X i -
    inner ℝ (Torus.grad V (X i) + (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
      periodicRieszGrad d s (X i - X j)) (configGrad Φ X i))

/-- `E_N(ψ) = -(2/N) F_N(𝒥ψ) + N^{-5/2} ∑_{distinct} G_ψ - N^{-5/2} ∑_{i≠j} B_ψ`
(`Q:eq:error-statistic`). -/
def errStat (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) {N : ℕ} (ψ : Torus d → Torus d → ℝ)
    (X : Config d N) : ℝ :=
  -(2 / (N : ℝ)) * Fstat (Jpair d s ρ ψ) X + (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum (Gpsi d s ρ ψ) X
    - (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered (Bpsi d s ρ ψ) X

/-- Centering under a law: `F̂ = F - E_P[F]`. -/
def centeredUnder {α : Type*} [MeasurableSpace α] (P : Measure α) (F : α → ℝ) : α → ℝ :=
  fun a => F a - ∫ b, F b ∂P

/- Route and status (EQ-01b, open).  Source lines 4907-4933: the algebraic identity
`(√N/2)D_μ(h_f) = -𝓛F_N(ψ) + E_N(ψ) - (2/N)ζ_N(a_f)` off collisions (expanding `Δ_i`, `∇_i` of
`∑ψ(x_i,x_j)` with the Poisson equation and `triple_canonical`), stationarity `E 𝓛F_N(ψ) = 0`
(integration by parts against `canonicalGibbs` for a kernel singular on collisions), integrability
of `quadStat` under `P_{N,β}`, and the `L²` bounds from `pair_moments` (open). 
Attempt 2: depends on `pair_moments`, `pair_poisson`, `triple_canonical` (all open) and on
integration by parts against `canonicalGibbs` with collision singularities; not started.-/

/-- Proposition 4.16 `M:Q:prop:normal-form` (source lines 4907-4933), stated for every kernel
`ψ` with the conclusions of Proposition 4.13 for `f` (constant `K₁`): with the actual
stationary centering of every term, off collisions,
`𝓡_N(f) := (√N/2){D_μ(h_f) - E D_μ(h_f)} = -𝓛 F̂_N(ψ) + Ê_N(ψ) - (2/N) ζ_N(a_f)`, and
`‖F̂_N(ψ)‖_{L²} + (E ∑_i |∇_i F_N(ψ)|²)^{1/2} + ‖Ê_N(ψ)‖_{L²} + N⁻¹‖ζ_N(a_f)‖_{L²}
  ≤ C (K₁ + |f|_K) N^{-1/2}` (for `ψ = ψ_f`, `K₁ = C|f|_K`). The generator-domain form of the
identity is not encoded; the integrability conjuncts rule out junk centering constants. -/
theorem normal_form (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ → ∀ N : ℕ, 2 ≤ N →
        Integrable (quadStat (hTransport d s f) (withDensityReal ρ))
            (canonicalGibbs (periodicRiesz d s) V N β) ∧
        Integrable (Fstat (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) ∧
        Integrable (errStat d s ρ (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) ∧
        (∀ X : Config d N, X ∉ collisionSet d N →
          Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
              (quadStat (hTransport d s f) (withDensityReal ρ)) X =
            -particleGen d s V β (Fstat ψ) X +
              centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρ ψ) X -
              (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X)) ∧
        eLpNorm (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (Fstat ψ)) 2
              (canonicalGibbs (periodicRiesz d s) V N β) +
            (∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
              ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ (1 / 2 : ℝ) +
            eLpNorm (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρ ψ)) 2
              (canonicalGibbs (periodicRiesz d s) V N β) +
            ENNReal.ofReal (1 / (N : ℝ)) *
              eLpNorm (fun X : Config d N => Real.sqrt N *
                  centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                    (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X) 2
                (canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal (C * (K₁ + posSeminorm (8 * d + 80) f) * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  sorry

end Critical

end HRS

end
