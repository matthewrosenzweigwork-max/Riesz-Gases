import HRS.PDE.MeanFieldDefs
import HRS.Dynamics.Setup
import HRS.Sections.Q38bAux5

/-!
# HRS.Sections.Sec3 — Proposition 3.46 (the physical high-temperature endpoint)

Statement drafts (all proofs are `sorry`) for the row

* `M:O:prop:beta-zero` (Proposition 3.46, TeX M L3313-3326).

Representation decisions (to be recorded in `docs/ISSUES.md`):

* "The homogeneous periodic stationary Gaussian fluctuation `Z_β`" (M L3314) is the stationary
  Gaussian field of `H:eq:susceptibility` (M L925-935) / `C:eq:stationary-cov` (M L5908-5913) for the
  homogeneous model `V = 0`, `ρ_β = 1`, represented by the predicate `IsStationaryGaussianField`
  below: a measurable, almost surely continuous `E_m`-valued process whose finite-dimensional laws
  against smooth tests are the centred Gaussians with covariance `PDE.stationaryLagCov` (the
  susceptibility form transported by the equilibrium semigroup).  Existence of such a process is
  not part of the statement (it is the stationary construction of M L9096-9115).
* "A nonzero normalized real Fourier coordinate" is `⟨Z^t, e_k⟩ = NegSobolev.eval (Z t ω) (realMode k)`
  for `k ≠ 0`, with `e_k = Torus.realMode k` the `L²`-orthonormal real mode.
* Non-tightness "as `β ↓ 0`" is stated along every sequence `β_n → 0+` (the strongest reading; the
  proof, M L3328-3330, shows the modulus-of-continuity condition fails along any such sequence),
  for the laws of the continuous coordinate paths on `C([0,T];ℝ)`.
* The rescaled-clock equation `O:eq:hot-clock` is the strong-solution predicate `IsStrongSolution`
  for the dynamics data `hotDyn` (`M = -βI`, potential `βV`, `β_N⁻¹ = 1`): the drift is
  `-β(∇V(x_i) + N⁻¹∑_{j≠i}∇γ(x_i-x_j))` and the noise is `√2 dB`.  The endpoint `β = 0` is the
  same data with zero drift (independent Brownian motions).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {d : ℕ}

/-- The stationary Gaussian field with the equilibrium (susceptibility) covariance (M L925-935,
L5908-5913, L9096-9115) for the gradient model with potential `V`, thermal density `ρβ` and inverse
temperature `β`, realised as a measurable, a.s. continuous `E_m = H^{-m}_0`-valued process on
`[0,∞)` whose finite-dimensional laws against smooth tests `φ_a` at times `τ_a ≥ 0` are the centred
Gaussians with covariance `PDE.stationaryLagCov` (`Σ_{ab} = C_β(φ_a, S_β(τ_b-τ_a) φ_b)` for
`τ_a ≤ τ_b`).  Existence is not asserted by the predicate. -/
structure IsStationaryGaussianField {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (s β : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (V ρβ : Torus d → ℝ) (m : ℝ)
    (Z : ℝ → Ω → NegSobolev d m) : Prop where
  meas : ∀ t, Measurable (Z t)
  cont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0)
  gaussian : ∀ (p : ℕ) (τ : Fin p → ℝ) (φ : Fin p → Torus d → ℝ),
    (∀ a, 0 ≤ τ a) → (∀ a, Torus.IsSmooth (φ a)) →
    law P (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) :
        EuclideanSpace ℝ (Fin p))) =
      ProbabilityTheory.multivariateGaussian 0
        (PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ) ρβ τ φ)

/-- The coordinate path `t ↦ ⟨Z^t, φ⟩`, `0 ≤ t ≤ T`, as an element of `C([0,T];ℝ)`
(the zero path when the trajectory is not continuous, which happens on a null set only). -/
def coordPath {m : ℝ} (T : ℝ) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) (φ : Torus d → ℝ)
    (ω : Ω) : C(Set.Icc (0 : ℝ) T, ℝ) :=
  open Classical in
  if h : Continuous fun t : Set.Icc (0 : ℝ) T => NegSobolev.eval (Z t ω) φ then ⟨_, h⟩ else 0

/-- The rescaled ("hot") clock dynamics of `O:eq:hot-clock` (M L3318-3321): constant matrix
`M = -β I`, one-body potential `βV` and `β_N⁻¹ = 1`, so that
`particleDrift = -β(∇V(x_i) + N⁻¹∑_{j≠i}∇γ(x_i-x_j))` and the noise is `√2 dB_i`.
Defined for every `β ≥ 0`; `β = 0` is the independent-diffusion endpoint. -/
def hotDyn (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (β : ℝ) : DynData d :=
  ⟨s, (-β) • (1 : Matrix (Fin d) (Fin d) ℝ), fun x => β * V x, 1, hs0, hsd, zero_le_one⟩

/-- Proposition 3.46 (`M:O:prop:beta-zero`, TeX M L3313-3326), first sentence: for the homogeneous
stationary Gaussian fluctuation (`V = 0`, `ρ_β = 1`), a nonzero normalized real Fourier coordinate
has the covariance `O:eq:beta-cov`
`E[Z_β^t Z_β^u] = exp[-(2π|k|)²(β⁻¹ + ĝ(k))|t-u|] / (1 + β ĝ(k))`.
Technical hypotheses: `2 ≤ d` (standing assumption of Section 3, M L417); `t, u ≥ 0` (the process
is indexed by `[0,∞)`); `d/2 < m` (the TeX fixes no index: the coordinate is a real Fourier
coordinate; `m > d/2` is the range in which the stationary field exists in `E_m`, because the equal-time
variance is bounded below by a constant times `1/(1+βĝ(k))` for every mode, so the second moment of the
`H^{-m}` norm is `∑⟨k⟩^{-2m}` times a bounded quantity; below it the predicate is unsatisfiable). -/
theorem hot_covariance (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (m : ℝ)
    (hm : (d : ℝ) / 2 < m)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℝ → Ω → NegSobolev d m)
    (hZ : IsStationaryGaussianField P s β hs0 hsd hβ (fun _ => 0) (fun _ => 1) m Z)
    (k : NonzeroLattice d) (t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u) :
    ∫ ω, NegSobolev.eval (Z t ω) (Torus.realMode k) * NegSobolev.eval (Z u ω) (Torus.realMode k) ∂P =
      Real.exp (-((2 * Real.pi * Lattice.enorm k.1) ^ 2 * (β⁻¹ + rieszCoeff d s k.1)) * |t - u|) /
        (1 + β * rieszCoeff d s k.1) := by
  classical
  let τ : Fin 2 → ℝ := ![t, u]
  let φ : Fin 2 → Torus d → ℝ := fun _ => Torus.realMode k
  have hτ : ∀ a, 0 ≤ τ a := by
    intro a
    fin_cases a
    · exact ht
    · exact hu
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun _ => q38b_isSmooth_realMode k
  have hlaw := hZ.gaussian 2 τ φ hτ hφ
  rw [q38b_lagCov_eq (by omega : 2 ≤ d) hs0 hsd hβ k τ hτ] at hlaw
  have hmeas : ∀ a : Fin 2, Measurable fun ω => NegSobolev.eval (Z (τ a) ω) (φ a) :=
    fun a => (q38b_measurable_eval_realMode k).comp (hZ.meas (τ a))
  have hWm : Measurable fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) :
      EuclideanSpace ℝ (Fin 2)) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp (measurable_pi_iff.2 hmeas)
  have hrate : 0 ≤ q38b_rate d s β k := by
    unfold q38b_rate
    have h1 := q42_rieszCoeff_nonneg (by omega : 2 ≤ d) hs0 hsd k.1
    have h2 : 0 ≤ β⁻¹ := inv_nonneg.2 hβ.le
    positivity
  have hA : 0 ≤ (1 + β * rieszCoeff d s k.1)⁻¹ :=
    inv_nonneg.2 (q42_one_add_pos (by omega : 2 ≤ d) hs0 hsd hβ k.1).le
  have hS := q38b_posSemidef_two _ _ hA hrate τ
  have key := q38b_gauss_prod P _ hWm.aemeasurable _ hS hlaw
  have e1 : (fun ω => NegSobolev.eval (Z t ω) (Torus.realMode k) *
      NegSobolev.eval (Z u ω) (Torus.realMode k)) =
      fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) :
        EuclideanSpace ℝ (Fin 2)) 0 *
        (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) :
          EuclideanSpace ℝ (Fin 2)) 1 := by
    funext ω
    rfl
  rw [e1, key]
  simp only [Matrix.of_apply, τ, Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold q38b_rate
  rw [div_eq_inv_mul]

/-- `q38b_continuous_eval_realMode`: the coordinate `F ↦ ⟨F, e_k⟩` is continuous on `E_m`. -/
lemma q38b_continuous_eval_realMode {m : ℝ} (k : NonzeroLattice d) :
    Continuous (fun F : NegSobolev d m => NegSobolev.eval F (Torus.realMode k)) := by
  have : (fun F : NegSobolev d m => NegSobolev.eval F (Torus.realMode k)) =
      fun F => Lattice.jp k.1 ^ m * NegSobolev.coord F k := by
    funext F
    rw [q38b_eval_realMode]
    rfl
  rw [this]
  exact continuous_const.mul (q38b_continuous_coord k)

/-- `q38b_coordPath_apply`: on a continuous trajectory the coordinate path is the coordinate. -/
lemma q38b_coordPath_apply {m : ℝ} (T : ℝ) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m)
    (k : NonzeroLattice d) (ω : Ω) (hω : ContinuousOn (fun t => Z t ω) (Set.Ici 0))
    (s : Set.Icc (0 : ℝ) T) :
    coordPath T Z (Torus.realMode k) ω s = NegSobolev.eval (Z s ω) (Torus.realMode k) := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => NegSobolev.eval (Z t ω) (Torus.realMode k) := by
    have h1 : ContinuousOn (fun t => NegSobolev.eval (Z t ω) (Torus.realMode k)) (Set.Ici 0) :=
      (q38b_continuous_eval_realMode k).comp_continuousOn hω
    exact h1.comp_continuous continuous_subtype_val (fun t => t.2.1)
  unfold coordPath
  rw [dif_pos hc]
  rfl

/-- `q38b_aemeasurable_coordPath`: the coordinate path map is a.e. measurable. -/
lemma q38b_aemeasurable_coordPath {m : ℝ} (T : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → Ω → NegSobolev d m) (hmeas : ∀ t, Measurable (Z t))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0)) (k : NonzeroLattice d) :
    AEMeasurable (coordPath T Z (Torus.realMode k)) P := by
  classical
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hcont)
  let g : Ω → C(Set.Icc (0 : ℝ) T, ℝ) := fun ω =>
    if ω ∈ N then 0 else coordPath T Z (Torus.realMode k) ω
  have hg : Measurable g := by
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have hfun : (fun ω => g ω s) =
        fun ω => if ω ∈ N then 0 else NegSobolev.eval (Z s ω) (Torus.realMode k) := by
      funext ω
      by_cases hω : ω ∈ N
      · simp [g, hω]
      · have hc : ContinuousOn (fun t => Z t ω) (Set.Ici 0) := by
          by_contra hnc
          exact hω (hNsub hnc)
        simp only [g, hω, if_false]
        exact q38b_coordPath_apply T Z k ω hc s
    rw [hfun]
    exact Measurable.ite hNm measurable_const
      ((q38b_measurable_eval_realMode k).comp (hmeas s))
  refine ⟨g, hg, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  simp [g, hω]

/-- `q38b_event_lower`: a lower bound for the probability that the coordinate moves by `≥ 1`
between times `0` and `h` (homogeneous stationary Gaussian field with variance `≥ 1` for the
increment). -/
lemma q38b_event_lower (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (m : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℝ → Ω → NegSobolev d m)
    (hZ : IsStationaryGaussianField P s β hs0 hsd hβ (fun _ => 0) (fun _ => 1) m Z)
    (k : NonzeroLattice d) {h : ℝ} (hh : 0 ≤ h)
    (hv : 1 ≤ 2 * (1 + β * rieszCoeff d s k.1)⁻¹ -
      2 * ((1 + β * rieszCoeff d s k.1)⁻¹ * Real.exp (-(q38b_rate d s β k) * h))) :
    ProbabilityTheory.gaussianReal 0 1 {x : ℝ | 1 ≤ |x|} ≤
      P {ω | 1 ≤ |NegSobolev.eval (Z 0 ω) (Torus.realMode k) -
        NegSobolev.eval (Z h ω) (Torus.realMode k)|} := by
  classical
  let τ : Fin 2 → ℝ := ![0, h]
  let φ : Fin 2 → Torus d → ℝ := fun _ => Torus.realMode k
  have hτ : ∀ a, 0 ≤ τ a := by
    intro a
    fin_cases a
    · exact le_rfl
    · exact hh
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun _ => q38b_isSmooth_realMode k
  have hlaw := hZ.gaussian 2 τ φ hτ hφ
  rw [q38b_lagCov_eq hd hs0 hsd hβ k τ hτ] at hlaw
  have hmeas : ∀ a : Fin 2, Measurable fun ω => NegSobolev.eval (Z (τ a) ω) (φ a) :=
    fun a => (q38b_measurable_eval_realMode k).comp (hZ.meas (τ a))
  have hWm : Measurable fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) :
      EuclideanSpace ℝ (Fin 2)) :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp (measurable_pi_iff.2 hmeas)
  have hrate : 0 ≤ q38b_rate d s β k := by
    unfold q38b_rate
    have h1 := q42_rieszCoeff_nonneg hd hs0 hsd k.1
    have h2 : 0 ≤ β⁻¹ := inv_nonneg.2 hβ.le
    positivity
  have hA : 0 ≤ (1 + β * rieszCoeff d s k.1)⁻¹ :=
    inv_nonneg.2 (q42_one_add_pos hd hs0 hsd hβ k.1).le
  have hS := q38b_posSemidef_two _ _ hA hrate τ
  have hDm : Measurable fun x : EuclideanSpace ℝ (Fin 2) => x 0 - x 1 := by fun_prop
  have hmap := q38b_gauss_diff_map _ hS
  set W : Ω → EuclideanSpace ℝ (Fin 2) :=
    fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) :
      EuclideanSpace ℝ (Fin 2)) with hW
  rw [← hlaw] at hmap
  have hmap2 : P.map (fun ω => W ω 0 - W ω 1) = ProbabilityTheory.gaussianReal 0
      (2 * (1 + β * rieszCoeff d s k.1)⁻¹ -
        2 * ((1 + β * rieszCoeff d s k.1)⁻¹ * Real.exp (-(q38b_rate d s β k) * h))).toNNReal := by
    have e1 : P.map (fun ω => W ω 0 - W ω 1) = (P.map W).map (fun x : EuclideanSpace ℝ (Fin 2) => x 0 - x 1) :=
      (Measure.map_map hDm hWm).symm
    rw [e1, hmap]
    congr 2
    simp only [Matrix.of_apply, τ, Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, abs_zero,
      mul_zero, Real.exp_zero, mul_one, zero_sub, abs_neg, abs_of_nonneg hh]
    ring
  have hWm0 : Measurable fun ω => W ω 0 - W ω 1 := hDm.comp hWm
  have hev : P {ω | 1 ≤ |NegSobolev.eval (Z 0 ω) (Torus.realMode k) -
        NegSobolev.eval (Z h ω) (Torus.realMode k)|} =
      (P.map fun ω => W ω 0 - W ω 1) {x : ℝ | 1 ≤ |x|} := by
    rw [Measure.map_apply hWm0 (measurableSet_le measurable_const (by fun_prop))]
    rfl
  rw [hev, hmap2]
  refine q38b_gaussian_lower ?_
  have : (1 : ℝ≥0) = (1 : ℝ).toNNReal := by simp
  rw [this]
  exact Real.toNNReal_le_toNNReal hv

/-- Proposition 3.46, second sentence (`M:O:prop:beta-zero`, M L3314-3315): the path laws of a
nonzero normalized real Fourier coordinate of the homogeneous stationary Gaussian fluctuation are
not tight in `C([0,T];ℝ)` as `β ↓ 0`.  Stated along every sequence `β_n → 0+` (with an arbitrary
probability space `Ω n` and field `Z n` for each `n`): the family of laws of the coordinate paths
`t ↦ ⟨Z_{β_n}^t, e_k⟩` is not a tight set of measures (Mathlib `IsTightMeasureSet`).
Technical hypotheses: `2 ≤ d`, `0 < T`, `d/2 < m` (see `hot_covariance`: the TeX fixes no index and the
field exists in `E_m` only for `m > d/2`). -/
theorem hot_not_tight (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℝ)
    (hm : (d : ℝ) / 2 < m)
    (k : NonzeroLattice d) (T : ℝ) (hT : 0 < T) (β : ℕ → ℝ) (hβpos : ∀ n, 0 < β n)
    (hβ0 : Tendsto β atTop (𝓝 0))
    (Ω : ℕ → Type) [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    (Z : ∀ n, ℝ → Ω n → NegSobolev d m)
    (hZ : ∀ n, IsStationaryGaussianField (P n) s (β n) hs0 hsd (hβpos n) (fun _ => 0)
      (fun _ => 1) m (Z n)) :
    ¬ IsTightMeasureSet
        (Set.range fun n => (P n).map (coordPath T (Z n) (Torus.realMode k))) := by
  classical
  intro htight
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  set c1 : ℝ≥0∞ := ProbabilityTheory.gaussianReal 0 1 {x : ℝ | 1 ≤ |x|} with hc1def
  have hc1 : c1 ≠ 0 := q38b_gaussian_pos
  have hc1top : c1 ≠ ∞ := measure_ne_top _ _
  obtain ⟨K, hKc, hK⟩ := htight (c1 / 2) (ENNReal.half_pos hc1)
  obtain ⟨δ, hδ, hδK⟩ := q38b_equicont hKc (one_pos : (0 : ℝ) < 1)
  set h : ℝ := min T (δ / 2) with hhdef
  have hh0 : 0 < h := lt_min hT (by linarith)
  have hhT : h ≤ T := min_le_left _ _
  have hhδ : h < δ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  set g : ℝ := rieszCoeff d s k.1 with hgdef
  have hg0 : 0 ≤ g := q42_rieszCoeff_nonneg hd hs0 hsd k.1
  set a0 : ℝ := (2 * Real.pi * Lattice.enorm k.1) ^ 2 with ha0
  have ha0pos : 0 < a0 := by
    have := q38b_enorm_pos k
    have := Real.pi_pos
    positivity
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have ev1 : ∀ᶠ n in atTop, β n < 1 / (3 * (g + 1)) :=
    hβ0.eventually (Iio_mem_nhds (by positivity))
  have ev2 : ∀ᶠ n in atTop, β n < a0 * h / Real.log 4 :=
    hβ0.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨n, hn1, hn2⟩ := (ev1.and ev2).exists
  have hb := hβpos n
  set b : ℝ := β n with hbdef
  set A : ℝ := (1 + b * g)⁻¹ with hAdef
  have hAmul : A * (1 + b * g) = 1 := inv_mul_cancel₀ (by positivity)
  have hApos : 0 < A := by positivity
  have hbg : b * (3 * (g + 1)) < 1 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * (g + 1))).1 hn1
    linarith
  have hA34 : 3 / 4 ≤ A := by
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_nonneg hb.le hg0]
  have hrate : q38b_rate d s b k * h = a0 * h * b⁻¹ + a0 * g * h := by
    unfold q38b_rate
    simp only [ha0, hgdef, hbdef]
    ring
  have hlogb : Real.log 4 < a0 * h * b⁻¹ := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < Real.log 4)).1 hn2
    rw [← div_eq_mul_inv, lt_div_iff₀ hb]
    nlinarith
  have hc4 : Real.exp (-(q38b_rate d s b k) * h) ≤ 1 / 4 := by
    have h1 : -(q38b_rate d s b k) * h ≤ -Real.log 4 := by
      have : 0 ≤ a0 * g * h := by positivity
      nlinarith
    calc Real.exp (-(q38b_rate d s b k) * h) ≤ Real.exp (-Real.log 4) := Real.exp_le_exp.2 h1
      _ = 1 / 4 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hc0 : 0 ≤ Real.exp (-(q38b_rate d s b k) * h) := (Real.exp_pos _).le
  have hv : 1 ≤ 2 * (1 + β n * rieszCoeff d s k.1)⁻¹ -
      2 * ((1 + β n * rieszCoeff d s k.1)⁻¹ * Real.exp (-(q38b_rate d s b k) * h)) := by
    show 1 ≤ 2 * A - 2 * (A * Real.exp (-(q38b_rate d s b k) * h))
    nlinarith [mul_nonneg (sub_nonneg.2 hA34) (sub_nonneg.2 hc4)]
  have hlow := q38b_event_lower hd hs0 hsd (hβpos n) m (P n) (Z n) (hZ n) k hh0.le hv
  have hae := q38b_aemeasurable_coordPath T (P n) (Z n) (hZ n).meas (hZ n).cont k
  have hKm : MeasurableSet Kᶜ := hKc.isClosed.measurableSet.compl
  have hKn := hK _ ⟨n, rfl⟩
  rw [Measure.map_apply_of_aemeasurable hae hKm] at hKn
  have hsub : (P n) {ω | 1 ≤ |NegSobolev.eval (Z n 0 ω) (Torus.realMode k) -
        NegSobolev.eval (Z n h ω) (Torus.realMode k)|} ≤
      (P n) (coordPath T (Z n) (Torus.realMode k) ⁻¹' Kᶜ) := by
    refine measure_mono_ae ?_
    filter_upwards [(hZ n).cont] with ω hω hmem
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff] at hmem ⊢
    intro hK'
    have hd0 : dist (⟨0, ⟨le_rfl, hT.le⟩⟩ : Set.Icc (0 : ℝ) T) ⟨h, ⟨hh0.le, hhT⟩⟩ < δ := by
      simpa [Subtype.dist_eq, Real.dist_eq, abs_of_pos hh0] using hhδ
    have := hδK _ hK' _ _ hd0
    rw [q38b_coordPath_apply T (Z n) k ω hω, q38b_coordPath_apply T (Z n) k ω hω,
      Real.dist_eq] at this
    simp only at this
    linarith
  have hfin : c1 ≤ c1 / 2 := hlow.trans (hsub.trans hKn)
  exact absurd hfin (not_le.2 (ENNReal.half_lt_self hc1 hc1top))

/-- `q38_grad_const_mul`: the torus gradient commutes with a nonzero constant factor. -/
lemma q38_grad_const_mul {d : ℕ} (c : ℝ) (hc : c ≠ 0) (V : Torus d → ℝ) (x : Torus d) :
    Torus.grad (fun y => c * V y) x = c • Torus.grad V x := by
  have hfun : Torus.lift (fun y => c * V y) = fun z => c * Torus.lift V z := rfl
  unfold Torus.grad gradient
  rw [hfun]
  by_cases hd : DifferentiableAt ℝ (Torus.lift V) (Torus.rep x)
  · rw [fderiv_const_mul hd c, map_smul]
  · have hnd : ¬ DifferentiableAt ℝ (fun z => c * Torus.lift V z) (Torus.rep x) := fun h =>
      hd (by simpa [inv_mul_cancel_left₀ hc] using h.const_mul c⁻¹)
    rw [fderiv_zero_of_not_differentiableAt hnd, fderiv_zero_of_not_differentiableAt hd]
    simp

/-- `q38_grad_zero`: the torus gradient of the zero function vanishes. -/
lemma q38_grad_zero {d : ℕ} (x : Torus d) : Torus.grad (fun _ : Torus d => (0 : ℝ)) x = 0 := by
  have hl : Torus.lift (fun _ : Torus d => (0 : ℝ)) = fun _ => 0 := rfl
  unfold Torus.grad gradient
  rw [hl]
  simp

/-- `q38_matVec_neg_smul`: the matrix `-β I` acts as `β • (-I)`. -/
lemma q38_matVec_neg_smul {d : ℕ} (β : ℝ) (v : Euc d) :
    Torus.matVec ((-β) • (1 : Matrix (Fin d) (Fin d) ℝ)) v = β • Torus.matVec (-1) v := by
  have hM : (-β) • (1 : Matrix (Fin d) (Fin d) ℝ) = β • (-1) := by
    rw [neg_smul, smul_neg]
  unfold Torus.matVec
  rw [hM, map_smul]
  rfl

/-- `q38_hot_drift`: the rescaled drift `hotDyn` is `β` times the mean-field drift. -/
lemma q38_hot_drift {d N : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) {β : ℝ}
    (hβ : 0 < β) (X : Config d N) (i : Fin N) :
    particleDrift (hotDyn d s hs0 hsd V β) X i =
      β • particleDrift (PDE.mfData d s hs0 hsd V β hβ) X i := by
  unfold particleDrift
  simp only [hotDyn, PDE.mfData, q38_matVec_neg_smul, q38_grad_const_mul β hβ.ne' V,
    smul_sub, Finset.smul_sum, smul_comm (1 / (N : ℝ)) β]

/-- `q38_cov_scale`: change of variables `u = β s` in the drift integral. -/
lemma q38_cov_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E)
    {β τ : ℝ} (hβ : 0 < β) (hτ : 0 ≤ τ) :
    ∫ s in Set.Icc 0 τ, β • F (β * s) = ∫ u in Set.Icc 0 (β * τ), F u := by
  have h1 : ∫ s in Set.Icc 0 τ, β • F (β * s) = ∫ s in (0 : ℝ)..τ, β • F (β * s) := by
    rw [intervalIntegral.integral_of_le hτ, integral_Icc_eq_integral_Ioc]
  have h2 : ∫ u in Set.Icc 0 (β * τ), F u = ∫ u in (0 : ℝ)..(β * τ), F u := by
    rw [intervalIntegral.integral_of_le (mul_nonneg hβ.le hτ), integral_Icc_eq_integral_Ioc]
  rw [h1, h2, intervalIntegral.integral_smul,
    intervalIntegral.integral_comp_mul_left F hβ.ne', mul_zero, smul_inv_smul₀ hβ.ne']

/-- `q38_integrableOn_scale`: integrability is transported by the dilation `s ↦ β s`. -/
lemma q38_integrableOn_scale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : ℝ → E)
    {β τ : ℝ} (hβ : 0 < β) (hτ : 0 ≤ τ) (hF : IntegrableOn F (Set.Icc 0 (β * τ))) :
    IntegrableOn (fun s => F (β * s)) (Set.Icc 0 τ) := by
  have hle : 0 ≤ β * τ := mul_nonneg hβ.le hτ
  have h1 : IntervalIntegrable F volume 0 (β * τ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hle).2 hF
  have h2 := h1.comp_mul_left (c := β) enorm_ne_top enorm_ne_top
  rw [zero_div, mul_div_cancel_left₀ τ hβ.ne'] at h2
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hτ).1 h2

/-- `q38_proj_eq`: the rescaled configuration path is the original one at time `β s`. -/
lemma q38_proj_eq {d N : ℕ} {Ω : Type*} (Y : ℝ≥0 → Ω → (Fin N → Euc d)) {β : ℝ}
    (c : ℝ≥0) (hc : (c : ℝ) = β) (hβ : 0 < β) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    projectPath (fun (τ : ℝ≥0) ω i => Y (c * τ) ω i) (Real.toNNReal s) ω =
      projectPath Y (Real.toNNReal (β * s)) ω := by
  have hcs : c * Real.toNNReal s = Real.toNNReal (β * s) := by
    apply NNReal.eq
    rw [NNReal.coe_mul, hc, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (mul_nonneg hβ.le hs)]
  funext i
  simp only [projectPath, hcs]

/-- Proposition 3.46, third sentence (`M:O:prop:beta-zero`, M L3315-3322): with physical time
`t = βτ` the particle equation becomes `O:eq:hot-clock`.  Precisely: if `X` is a collision-free
strong solution on `[0,T]` of the gradient particle system at inverse temperature `β > 0`
(`PDE.mfData`, i.e. `M = -I`, `β⁻¹` noise) driven by the vector Brownian motion `W`, then
`W'_τ = β^{-1/2} W_{βτ}` is again a vector Brownian motion and `τ ↦ X_{βτ}` is a collision-free
strong solution on `[0,T/β]` of the rescaled dynamics `hotDyn` (drift
`-β(∇V + N⁻¹∑∇γ)`, noise `√2 dW'`).  (Brownian scaling, M L3327-3328.) -/
theorem hot_clock {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (V : Torus d → ℝ)
    {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (T : ℝ)
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hW : IsVectorBrownian P W)
    (hX : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) T X₀ W X) :
    IsVectorBrownian P (fun τ ω i => (Real.sqrt β)⁻¹ • W (⟨β, hβ.le⟩ * τ) ω i) ∧
      IsStrongSolution P (hotDyn d s hs0 hsd V β) (T / β) X₀
        (fun τ ω i => (Real.sqrt β)⁻¹ • W (⟨β, hβ.le⟩ * τ) ω i)
        (fun τ ω => X (⟨β, hβ.le⟩ * τ) ω) := by
  classical
  set c : ℝ≥0 := ⟨β, hβ.le⟩ with hc_def
  have hcR : (c : ℝ) = β := rfl
  have hc0 : c ≠ 0 := by
    intro h
    have h' : (c : ℝ) = 0 := by rw [h]; rfl
    linarith
  have hcτ : ∀ τ : ℝ≥0, ((c * τ : ℝ≥0) : ℝ) = β * τ := fun τ => by rw [NNReal.coe_mul, hcR]
  have hBr : IsVectorBrownian P (fun τ ω i => (Real.sqrt β)⁻¹ • W (c * τ) ω i) := by
    refine ⟨fun i j => ?_, ?_⟩
    · have h := (hW.1 i j).smul hc0
      convert h using 1
      funext τ ω
      simp [hcR, smul_eq_mul]
    · have h := hW.2.comp (fun _ => fun f : ℝ≥0 → ℝ => fun τ => (Real.sqrt β)⁻¹ * f (c * τ))
        (fun _ => Measurable.of_eval fun τ => (measurable_pi_apply (c * τ)).const_mul _)
      convert h using 1
      funext ij ω t
      simp [smul_eq_mul]
  refine ⟨hBr, ?_⟩
  obtain ⟨⟨Y, hY, hXY⟩, hinit, hcont, hadapt, hcoll⟩ := hX
  subst hXY
  refine ⟨⟨fun τ ω i => Y (c * τ) ω i, ?_, rfl⟩, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hY] with ω hω
    intro τ hτ
    have hτ' : ((c * τ : ℝ≥0) : ℝ) ≤ T := by
      rw [hcτ, mul_comm]; exact (le_div_iff₀ hβ).1 hτ
    obtain ⟨hint, heq⟩ := hω (c * τ) hτ'
    have hτ0 : (0 : ℝ) ≤ τ := NNReal.coe_nonneg τ
    have hsq : ∀ (A B : Euc d), Real.sqrt (2 * (hotDyn d s hs0 hsd V β).invβ) •
        ((Real.sqrt β)⁻¹ • A - (Real.sqrt β)⁻¹ • B) =
        Real.sqrt (2 * (PDE.mfData d s hs0 hsd V β hβ).invβ) • (A - B) := by
      intro A B
      have h1 : (hotDyn d s hs0 hsd V β).invβ = 1 := rfl
      have h2 : (PDE.mfData d s hs0 hsd V β hβ).invβ = β⁻¹ := rfl
      rw [h1, h2, ← smul_sub, mul_one, smul_smul]
      congr 1
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_inv]
    have hpt : ∀ r ∈ Set.Icc (0 : ℝ) (τ : ℝ), ∀ i : Fin N, particleDrift (hotDyn d s hs0 hsd V β)
          (projectPath (fun (τ : ℝ≥0) ω i => Y (c * τ) ω i) (Real.toNNReal r) ω) i =
          β • particleDrift (PDE.mfData d s hs0 hsd V β hβ)
            (projectPath Y (Real.toNNReal (β * r)) ω) i := by
        intro r hr i
        rw [q38_proj_eq Y c hcR hβ hr.1 ω, q38_hot_drift]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hint' : IntegrableOn (fun r => β • particleDrift (PDE.mfData d s hs0 hsd V β hβ)
          (projectPath Y (Real.toNNReal (β * r)) ω) i) (Set.Icc 0 (τ : ℝ)) := by
        have hI := hint i
        rw [hcτ] at hI
        exact Integrable.smul β (q38_integrableOn_scale
          (fun u => particleDrift (PDE.mfData d s hs0 hsd V β hβ)
            (projectPath Y (Real.toNNReal u) ω) i) hβ hτ0 hI)
      refine hint'.congr_fun ?_ measurableSet_Icc
      intro r hr
      exact (hpt r hr i).symm
    · have hI : ∫ r in Set.Icc (0 : ℝ) τ, particleDrift (hotDyn d s hs0 hsd V β)
          (projectPath (fun (τ : ℝ≥0) ω i => Y (c * τ) ω i) (Real.toNNReal r) ω) i =
          ∫ u in Set.Icc 0 (β * τ), particleDrift (PDE.mfData d s hs0 hsd V β hβ)
            (projectPath Y (Real.toNNReal u) ω) i := by
        rw [setIntegral_congr_fun measurableSet_Icc (fun r hr => hpt r hr i)]
        exact q38_cov_scale (fun u => particleDrift (PDE.mfData d s hs0 hsd V β hβ)
          (projectPath Y (Real.toNNReal u) ω) i) hβ hτ0
      have heq' := heq i
      rw [hcτ] at heq'
      simp only [mul_zero] at ⊢
      rw [hI, heq', hsq]
  · filter_upwards [hinit] with ω hω
    simpa using hω
  · filter_upwards [hcont] with ω hω i
    exact (hω i).comp (continuous_const.mul continuous_id)
  · intro τ
    exact hadapt (c * τ)
  · filter_upwards [hcoll] with ω hω t ht
    have ht' : ((c * t : ℝ≥0) : ℝ) ≤ T := by
      rw [hcτ, mul_comm]; exact (le_div_iff₀ hβ).1 ht
    exact hω (c * t) ht'

/-- Proposition 3.46, last sentence (`M:O:prop:beta-zero`, M L3322-3323): at `β = 0` the rescaled
dynamics `hotDyn` has no drift, i.e. it is the independent-diffusion endpoint
(`dx_i = √2 dB_i`, independent Brownian motions); this holds in the rescaled clock only. -/
theorem hotDyn_zero_drift {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) {N : ℕ}
    (X : Config d N) (i : Fin N) :
    particleDrift (hotDyn d s hs0 hsd V 0) X i = 0 := by
  unfold particleDrift
  simp [hotDyn, Torus.matVec, q38_grad_zero]

end HRS
