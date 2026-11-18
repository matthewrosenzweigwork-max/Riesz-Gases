import HRS.Stochastic.Bridge
import HRS.Stochastic.Ito
import HRS.PDE.Convention
import HRS.Kernel.D1
import HRS.Kernel.GradConv

/-!
# Collision-free strong well-posedness of the periodic particle system (Proposition B.1)

Package PART-01.  Source: HRS periodic main paper, Proposition B.1 `B:thm:particle-wp`
(M L11645-11656) and its proof in §B "Direct collision-free regimes" (M L11724-12000):

* Lemma `B:lem:particle-maximal` (L11731-11737): maximal strong solution up to `τ_⋆` with the
  collision alternative `B:eq:particle-collision-alternative` (L11734).
* Cluster dispersion `Q_I` (L11759-11779): `Q_I = ∑_{i∈I}|x_i - x̄_I|² = k⁻¹ ∑_{i<j∈I}|x_i - x_j|²`
  on `ℝ^d`, the enlargement identity `B:eq:cluster-enlargement` (L11770), and the smooth
  function on `(𝕋^d)^N` with `Q_I⁻¹(0) = Δ_I` equal to the Euclidean expression near `Δ_I`.
* Lemma `B:lem:cluster-ito` (L11781-11802): Itô equation `B:eq:cluster-ito` (L11784-11788),
  `𝒜_I ≥ 0` (`B:eq:cluster-internal-positive`, L11791), remainder bound
  `B:eq:cluster-remainder` (L11795) under the exterior separation
  `B:eq:larger-cluster-separated` (L11799).
* Lemma `B:lem:cluster-barrier` (L11849-11856): logarithmic barrier, descending induction.
* Proposition `B:prop:particle-no-collision-dge2` (L11912-11918).
* Lemma `B:lem:d1-pair-barrier` (L11938-11948) and Proposition
  `B:prop:particle-no-collision-d1` (L11969-11971) for `d = 1`.
* Conclusion (L11989-12000), including the random initial configuration.

## Representation decisions (see `docs/ISSUES.md` §D1 and `HRS/Stochastic/SPEC.md`)

* Everything is formulated on the covering space `E = Fin N → Euc d` through the lifted SDE of
  `HRS/Stochastic/Bridge.lean`: drift `liftedDrift D`, additive noise `liftedNoise D`, state
  space `liftedFree d N` (open).  The source's maximal solution and its `τ_⋆` are the output of
  `exists_sde_solution_maximal` on `liftedFree d N` (bundled as `IsMaximalParticleSolution`);
  the source's force-truncation construction (L11740-11756) is already inside SI-01 and is not
  repeated.
* **Cluster dispersion on the torus.**  Instead of a tubular neighbourhood of `Δ_I` we use the
  geodesic representative `geoRep z = centeredRep (mk z) ∈ (-1/2,1/2]^d` and a smooth periodic
  pair function `pairDispersion x = χ(c)|c|² + (1-χ(c))/64`, `c = centeredRep x`, with `χ` a
  smooth bump equal to `1` on `|c| ≤ 1/8` and `0` on `|c| ≥ 1/4`.  Then
  `Q_I(X) = (2k)⁻¹ ∑_{i,j∈I} pairDispersion(x_i - x_j)`; it is smooth, `Q_I⁻¹(0) = Δ_I`, and on
  `{Q_I < clusterRadius I}` (`= 1/(128 k)`) every internal pair is within geodesic distance
  `1/8`, so `Q_I` is *exactly* the Euclidean expression `k⁻¹∑_{i<j}|ỹ_i - ỹ_j|²` of the
  compatible lifts `ỹ` and the derivative identities of L11805-11810 hold verbatim.
* **Itô equation.**  The generator of the lifted SDE applied to `Q_I` is `clusterGenerator`
  (`D Q_I[b] + ½ ∑_k D² Q_I[σ_k, σ_k]`, the drift of `ito_formula_localized`).  The singular
  internal term `𝒜_I` is `clusterInternal` (`B:eq:cluster-internal-formula` with the Euclidean
  singular force `eucRieszGrad`), and `ℛ_I := clusterGenerator - 2d(k-1)/β - 𝒜_I`
  (`clusterRemainder`), exactly as the source defines it (L11785, L11839-11844).
* **Kernel inputs.**  The analytic lemmas take the interface `KernelLocal d s` (smoothness of
  `∇g` off `0` and the local form `∇g = ∇g_E + smooth` with the smooth part vanishing at `0`).
  For `d ≥ 2` it is discharged from `HRS/Kernel/Riesz.lean` and `HRS/PDE/Convention.lean` plus
  the gradient identification `periodicRieszGrad_hasGradientAt` (section `KernelInputs`,
  from `HRS/Kernel/GradSmooth.lean`); for `d = 1` the inputs are proved in
  `HRS/Kernel/D1.lean` (section `KernelD1Inputs`).
* **Temperature.**  `β_N = ∞` is `invβ = 0`; the barrier proofs are uniform in `invβ ≥ 0`
  (the diffusion contribution to `ℒ(-log Q_I)` is `(4 - 2d(k-1)) invβ / Q_I ≤ 0`, which is `0`
  at zero temperature), so no separate Grönwall argument is needed.
* **Random initial configuration.**  The barrier lemmas are stated for the random `Y₀` of the
  maximal solution directly (no moment assumption): the martingale term is killed by the
  set-integral form of optional stopping on the `ℱ_0`-measurable sets `{Q_I(Y₀) ≥ 1/m}`, which
  exhaust `Ω` since `Y₀ ∈ liftedFree`.  This replaces the source's conditioning/Fubini step
  (L11999).
* `exists_isStrongSolution_of_no_exit` of `Bridge.lean` originally quantified over stopping
  times without positivity, making its `hnoexit` premise unsatisfiable (`τ ≡ 0`, `Y ≡ Y₀`);
  it now requires `0 < τ`.  `exists_isStrongSolution_of_maximal` below is the same reduction
  phrased through `IsMaximalParticleSolution`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ### The Euclidean singular force and the kernel interface -/

open Classical in
/-- The radial coefficient `a_s(z) > 0` of the Euclidean singular force (M L11815):
`∇|z|^{-s} = -s|z|^{-s-2} z` for `s > 0`, `∇(-log|z|) = -|z|^{-2} z` for `s = 0`. -/
def rieszRadial (s : ℝ) (z : Euc d) : ℝ :=
  if s = 0 then ‖z‖ ^ (-2 : ℝ) else s * ‖z‖ ^ (-s - 2)

/-- The Euclidean singular force `∇g_E(z) = -a_s(z) z` (M L11815). -/
def eucRieszGrad (s : ℝ) (z : Euc d) : Euc d := -(rieszRadial s z) • z

theorem rieszRadial_pos {s : ℝ} (hs : 0 ≤ s) {z : Euc d} (hz : z ≠ 0) : 0 < rieszRadial s z := by
  unfold rieszRadial
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  split_ifs with h
  · exact Real.rpow_pos_of_pos hn _
  · exact mul_pos (lt_of_le_of_ne hs (Ne.symm h)) (Real.rpow_pos_of_pos hn _)

/-- The local kernel facts used by the particle analysis, for a given dimension and exponent:
`∇g` is smooth off the origin, and near the origin `∇g(mk x) = ∇g_E(x) + r(mk x)` with `r`
smooth and `r(0) = 0` (the gradient of the smooth even remainder `h` of the local decomposition
`g = g_E + h`, M L11839-11842).  Discharged by `kernelLocal_of_two_le` (`d ≥ 2`) and
`kernelLocal_d1` (`d = 1`). -/
structure KernelLocal (d : ℕ) (s : ℝ) : Prop where
  smoothOffZero : Torus.IsSmoothOffZero (periodicRieszGrad d s)
  local_sing : ∃ (r : Torus d → Euc d) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧ r 0 = 0 ∧
    ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
      periodicRieszGrad d s (Torus.mk x) = eucRieszGrad s x + r (Torus.mk x)

section KernelInputs

variable {s : ℝ}

/-- **Kernel input (`d ≥ 2`).**  `periodicRieszGrad` is the gradient of the lift of
`periodicRiesz` away from the origin.  Proved in `HRS/Kernel/GradSmooth.lean`
(`KernelGrad.periodicRieszGrad_hasGradientAt`). -/
theorem periodicRieszGrad_hasGradientAt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (x : Euc d)
    (hx : Torus.mk x ≠ 0) :
    HasGradientAt (Torus.lift (periodicRiesz d s)) (periodicRieszGrad d s (Torus.mk x)) x :=
  KernelGrad.periodicRieszGrad_hasGradientAt hd hs0 hsd hx x rfl

theorem norm_sq_rpow (y : Euc d) (t : ℝ) : (‖y‖ ^ 2) ^ t = ‖y‖ ^ (2 * t) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]; norm_num

/-- Gradient of the Euclidean Riesz singularity `|z|^{-s}`, `s > 0`. -/
theorem hasGradientAt_norm_rpow_neg (hs : 0 < s) {y : Euc d} (hy : y ≠ 0) :
    HasGradientAt (fun z : Euc d => ‖z‖ ^ (-s)) (eucRieszGrad s y) y := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hfun : (fun z : Euc d => ‖z‖ ^ (-s)) = fun z => (‖z‖ ^ 2) ^ (-s / 2) := by
    funext z; rw [norm_sq_rpow]; ring_nf
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.rpow_const (p := -s / 2)
    (Or.inl (by positivity))
  convert h using 1
  ext v
  simp only [eucRieszGrad, rieszRadial, if_neg hs.ne', InnerProductSpace.toDual_apply_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, inner_smul_left,
    nsmul_eq_mul, Nat.cast_ofNat, conj_trivial]
  rw [norm_sq_rpow]
  ring_nf

/-- Gradient of the Euclidean logarithmic singularity `-log|z|`. -/
theorem hasGradientAt_neg_log_norm {y : Euc d} (hy : y ≠ 0) :
    HasGradientAt (fun z : Euc d => -Real.log ‖z‖) (eucRieszGrad 0 y) y := by
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hfun : (fun z : Euc d => -Real.log ‖z‖) = fun z => -(1 / 2 : ℝ) * Real.log (‖z‖ ^ 2) := by
    funext z; rw [Real.log_pow]; push_cast; ring
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  have h := ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.log (by positivity)).const_mul (-(1 / 2 : ℝ))
  convert h using 1
  ext v
  simp only [eucRieszGrad, rieszRadial, InnerProductSpace.toDual_apply_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, inner_smul_left,
    nsmul_eq_mul, Nat.cast_ofNat, conj_trivial]
  simp only [ite_true]
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_two]
  field_simp

theorem mk_ne_zero_of_norm_lt_one {x : Euc d} (hx : ‖x‖ < 1) (hx0 : x ≠ 0) : Torus.mk x ≠ 0 := by
  intro h
  apply hx0
  ext i
  have hi : ((x i : ℝ) : AddCircle (1 : ℝ)) = 0 := congrFun h i
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
  have hle : |x i| ≤ ‖x‖ := by
    have := PiLp.norm_apply_le x i
    rwa [Real.norm_eq_abs] at this
  rw [← hn] at hle
  have h1 : |(n : ℝ)| < 1 := by simpa using hle.trans_lt hx
  have h2 : |n| < 1 := by exact_mod_cast h1
  have h3 : n = 0 := by rw [abs_lt] at h2; omega
  rw [← hn, h3]; simp

/-- From a local decomposition `g = sing(|x|) + r₀` with `∇ sing(|·|) = ∇g_E`, the local form of
the force. -/
theorem local_grad_of_decomp (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (sing : ℝ → ℝ)
    (r0 : Torus d → ℝ) (δ : ℝ) (hδ : 0 < δ) (hr0 : Torus.IsSmooth r0)
    (hloc : ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
      periodicRiesz d s (Torus.mk x) = sing ‖x‖ + r0 (Torus.mk x))
    (hsing : ∀ y : Euc d, y ≠ 0 → HasGradientAt (fun z : Euc d => sing ‖z‖) (eucRieszGrad s y) y) :
    ∃ (r : Torus d → Euc d) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧ r 0 = 0 ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRieszGrad d s (Torus.mk x) = eucRieszGrad s x + r (Torus.mk x) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r0) := hr0
  have hdiff : Differentiable ℝ (Torus.lift r0) := hc.differentiable (by simp)
  refine ⟨Torus.grad r0, min δ 1, lt_min hδ one_pos, KernelD1Aux.isSmooth_grad hr0, ?_, ?_⟩
  · have h1 : Torus.grad r0 0 = gradient (Torus.lift r0) 0 := by
      have := KernelD1Aux.lift_grad r0 0
      have hm : Torus.mk (0 : Euc d) = 0 := by funext i; simp [Torus.mk]
      simpa [Torus.lift, hm] using this
    rw [h1]
    apply KernelD1Aux.gradient_zero_of_even _ (hdiff 0)
    filter_upwards [Metric.ball_mem_nhds (0 : Euc d) hδ] with z hz
    have hz' : ‖z‖ < δ := by simpa using hz
    show r0 (Torus.mk (-z)) = r0 (Torus.mk z)
    by_cases hz0 : z = 0
    · simp [hz0]
    · have h2 := hloc z hz' hz0
      have h3 := hloc (-z) (by simpa using hz') (neg_ne_zero.mpr hz0)
      have hmn : Torus.mk (-z) = -Torus.mk z := by funext i; simp [Torus.mk]
      have hg : periodicRiesz d s (Torus.mk (-z)) = periodicRiesz d s (Torus.mk z) := by
        rw [hmn, periodicRiesz_neg]
      rw [norm_neg] at h3
      linarith
  · intro x hx hx0
    have hxδ : ‖x‖ < δ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx1 : ‖x‖ < 1 := lt_of_lt_of_le hx (min_le_right _ _)
    have hG := periodicRieszGrad_hasGradientAt hd hs0 hsd x
      (mk_ne_zero_of_norm_lt_one hx1 hx0)
    have hR : HasGradientAt (Torus.lift r0) (gradient (Torus.lift r0) x) x :=
      (hdiff x).hasGradientAt
    have h1 := hsing x hx0
    rw [hasGradientAt_iff_hasFDerivAt] at h1 hR
    have hS := h1.add hR
    have hopen : IsOpen {z : Euc d | ‖z‖ < δ ∧ z ≠ 0} :=
      (isOpen_lt continuous_norm continuous_const).inter isOpen_ne
    have hev : (fun z : Euc d => periodicRiesz d s (Torus.mk z)) =ᶠ[𝓝 x]
        (fun z => sing ‖z‖ + Torus.lift r0 z) := by
      filter_upwards [hopen.mem_nhds ⟨hxδ, hx0⟩] with z hz
      exact hloc z hz.1 hz.2
    have hS' : HasGradientAt (fun z : Euc d => periodicRiesz d s (Torus.mk z))
        (eucRieszGrad s x + gradient (Torus.lift r0) x) x := by
      rw [hasGradientAt_iff_hasFDerivAt, map_add]
      exact HasFDerivAt.congr_of_eventuallyEq hS hev
    rw [hG.unique hS', ← KernelD1Aux.lift_grad r0 x]
    rfl

theorem Torus.grad_mk_aux (φ : Torus d → ℝ) (y : Euc d) :
    Torus.grad φ (Torus.mk y) = gradient (Torus.lift φ) y := by
  obtain ⟨n, hn⟩ := Torus.rep_mk y
  unfold Torus.grad
  rw [hn]
  have hper : (fun x => Torus.lift φ (x + Lattice.toEuc n)) = Torus.lift φ :=
    funext fun x => Torus.lift_periodic φ x n
  unfold gradient
  rw [← fderiv_comp_add_right (Lattice.toEuc n) (f := Torus.lift φ) (x := y), hper]

theorem mk_neg_euc (x : Euc d) : Torus.mk (-x) = -Torus.mk x := by
  funext i; simp [Torus.mk]

/-- Local form of the force for `d ≥ 2` (M L11839: `g = g_E + h`, `h` smooth and even, hence
`∇h(0) = 0`).  From `periodicRiesz_local_singularity` / `periodicLog_local_singularity`
(KERN-01b), `periodicRiesz_neg`, and `periodicRieszGrad_hasGradientAt`. -/
theorem periodicRieszGrad_local_singularity (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (r : Torus d → Euc d) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧ r 0 = 0 ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRieszGrad d s (Torus.mk x) = eucRieszGrad s x + r (Torus.mk x) := by
  by_cases hs : s = 0
  · subst hs
    obtain ⟨r0, δ, hδ, hr0, hloc⟩ := periodicLog_local_singularity hd
    exact local_grad_of_decomp hd hs0 hsd (fun r => -Real.log r) r0 δ hδ hr0 hloc
      (fun y hy => hasGradientAt_neg_log_norm hy)
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    obtain ⟨r0, δ, hδ, hr0, hloc⟩ := periodicRiesz_local_singularity hd hspos hsd
    exact local_grad_of_decomp hd hs0 hsd (fun r => r ^ (-s)) r0 δ hδ hr0 hloc
      (fun y hy => hasGradientAt_norm_rpow_neg hspos hy)

/-- The kernel interface for `d ≥ 2`, from `KernelGrad.periodicRieszGrad_smoothOffZero`
(`HRS/Kernel/GradConv.lean`, stated with a textually identical local copy of
`Torus.IsSmoothOffZero`) and `periodicRieszGrad_local_singularity`. -/
theorem kernelLocal_of_two_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) : KernelLocal d s :=
  ⟨KernelGrad.periodicRieszGrad_smoothOffZero hd hs0 hsd,
    periodicRieszGrad_local_singularity hd hs0 hsd⟩

end KernelInputs

section KernelD1Inputs

/-! The one-dimensional kernel facts needed by cases (ii)-(iii) of Proposition B.1 and by
Lemma `B:lem:d1-pair-barrier` are proved in `HRS/Kernel/D1.lean`
(`periodicRiesz_local_singularity_d1`, `periodicLog_local_singularity_d1`,
`periodicRieszGrad_smoothOffZero_d1`, `periodicRieszGrad_bound_d1`,
`periodicRieszGrad_local_singularity_d1`). That file states the last one with its own copy
`KernelD1.eucRieszGrad` of the Euclidean force, which is definitionally `eucRieszGrad`. -/

variable {s : ℝ}

theorem kernelD1_eucRieszGrad_eq : (KernelD1.eucRieszGrad s : Euc 1 → Euc 1) = eucRieszGrad s :=
  rfl

/-- The kernel interface for `d = 1`, assembled from the results of `HRS/Kernel/D1.lean`. -/
theorem kernelLocal_d1 (hs0 : 0 ≤ s) (hs1 : s < 1) : KernelLocal 1 s :=
  ⟨periodicRieszGrad_smoothOffZero_d1 hs0 hs1, periodicRieszGrad_local_singularity_d1 hs0 hs1⟩

end KernelD1Inputs

/-! ### Cluster dispersion `Q_I` on the torus (M L11759-11779) -/

/-- The geodesic representative of a covering-space vector: the representative of `mk z` in
`(-1/2, 1/2]^d`.  For `‖z - n‖ < 1/4`, `n ∈ ℤ^d`, it is `z - n`. -/
def geoRep (z : Euc d) : Euc d := Torus.centeredRep (Torus.mk z)

/-- The smooth cutoff `χ` on `ℝ^d`: `1` on `|z| ≤ 1/8`, `0` on `|z| ≥ 1/4`, values in `[0,1]`. -/
def clusterBump (d : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The periodic pair dispersion `ψ(x) = χ(c)|c|² + (1 - χ(c))/64` with `c = centeredRep x`:
a smooth function on `𝕋^d`, equal to the squared geodesic distance `|c|²` for `|c| ≤ 1/8`,
`≥ 1/64` for `|c| ≥ 1/8`, vanishing exactly at `x = 0`. -/
def pairDispersion (x : Torus d) : ℝ :=
  clusterBump d (Torus.centeredRep x) * ‖Torus.centeredRep x‖ ^ 2 +
    (1 - clusterBump d (Torus.centeredRep x)) * (1 / 64)

/-- The cluster dispersion `Q_I(X) = (2k)⁻¹ ∑_{i,j∈I} ψ(x_i - x_j)` on `(𝕋^d)^N`
(`B:eq:cluster-dispersion-rd`, M L11762-11766, with `k⁻¹∑_{i<j} = (2k)⁻¹∑_{i,j}`; the smooth
torus version of M L11775-11779). -/
def clusterDispersion (I : Finset (Fin N)) (X : Config d N) : ℝ :=
  (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I, pairDispersion (X i - X j)

/-- The lift of `Q_I` to the covering space `(ℝ^d)^N`. -/
def clusterDispersionLift (I : Finset (Fin N)) (Y : Fin N → Euc d) : ℝ :=
  clusterDispersion I fun i => Torus.mk (Y i)

/-- The cluster diagonal `Δ_I = {X : x_i = x_{i'} for all i, i' ∈ I}` (M L11777). -/
def clusterDiagonal (I : Finset (Fin N)) : Set (Config d N) :=
  {X | ∀ i ∈ I, ∀ j ∈ I, X i = X j}

/-- The radius `q_I = 1/(128 k)` below which `Q_I` is the Euclidean expression of the compatible
lifts (every internal pair is within geodesic distance `1/8`). -/
def clusterRadius (I : Finset (Fin N)) : ℝ := 1 / (128 * (I.card : ℝ))

/-- `x_i - x̄_I` in the compatible lift: `k⁻¹ ∑_{j∈I} geoRep(y_i - y_j)` for `i ∈ I`, `0`
otherwise. -/
def clusterCentered (I : Finset (Fin N)) (Y : Fin N → Euc d) (i : Fin N) : Euc d :=
  if i ∈ I then (1 / (I.card : ℝ)) • ∑ j ∈ I, geoRep (Y i - Y j) else 0

/-- Coordinates of `rep` lie in `[0,1)`. -/
theorem Torus.rep_coord_mem (x : Torus d) (i : Fin d) : 0 ≤ Torus.rep x i ∧ Torus.rep x i < 1 := by
  have h := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
  simpa [Torus.rep] using h

theorem Torus.centeredRep_apply (x : Torus d) (i : Fin d) :
    Torus.centeredRep x i = if Torus.rep x i ≤ 1 / 2 then Torus.rep x i else Torus.rep x i - 1 :=
  rfl

/-- `mk` of the centered representative is the original point. -/
theorem Torus.mk_centeredRep (x : Torus d) : Torus.mk (Torus.centeredRep x) = x := by
  funext i
  have h : (((Torus.rep x) i : ℝ) : UnitAddCircle) = x i := congrFun (Torus.mk_rep x) i
  show (((Torus.centeredRep x) i : ℝ) : UnitAddCircle) = x i
  rw [Torus.centeredRep_apply]
  split_ifs with hc
  · exact h
  · rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]; exact h

/-- The coordinates of `geoRep z` lie in `(-1/2, 1/2]`. -/
theorem geoRep_coord (z : Euc d) (i : Fin d) : -(1 / 2) < geoRep z i ∧ geoRep z i ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := Torus.rep_coord_mem (Torus.mk z) i
  show -(1 / 2) < Torus.centeredRep (Torus.mk z) i ∧ Torus.centeredRep (Torus.mk z) i ≤ 1 / 2
  rw [Torus.centeredRep_apply]
  split_ifs with hc
  · constructor <;> linarith
  · constructor <;> linarith [not_le.1 hc]

/-- `geoRep z` is congruent to `z` modulo `ℤ^d`, coordinatewise. -/
theorem geoRep_int (z : Euc d) (i : Fin d) : ∃ m : ℤ, z i - geoRep z i = m := by
  have h : (((geoRep z i : ℝ)) : UnitAddCircle) = ((z i : ℝ) : UnitAddCircle) :=
    congrFun (Torus.mk_centeredRep (Torus.mk z)) i
  have h0 : (((z i - geoRep z i : ℝ)) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, sub_eq_zero]
    exact h.symm
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h0
  exact ⟨n, by simpa using hn.symm⟩

/-- Characterisation of `geoRep`: the unique vector with coordinates in `(-1/2,1/2]` that is
congruent to `z` modulo `ℤ^d`. -/
theorem eq_geoRep_of (z w : Euc d) (hw : ∀ i, -(1 / 2) < w i ∧ w i ≤ 1 / 2)
    (hint : ∀ i, ∃ m : ℤ, z i - w i = m) : geoRep z = w := by
  ext i
  obtain ⟨m1, h1⟩ := hint i
  obtain ⟨m2, h2⟩ := geoRep_int z i
  obtain ⟨a1, a2⟩ := hw i
  obtain ⟨b1, b2⟩ := geoRep_coord z i
  have h3 : ((m1 - m2 : ℤ) : ℝ) = geoRep z i - w i := by push_cast; linarith
  have h4 : ((m1 - m2 : ℤ) : ℝ) < 1 := by rw [h3]; linarith
  have h5 : (-1 : ℝ) < ((m1 - m2 : ℤ) : ℝ) := by rw [h3]; linarith
  have h6 : m1 - m2 < 1 := by exact_mod_cast h4
  have h7 : -1 < m1 - m2 := by exact_mod_cast h5
  have h8 : m1 - m2 = 0 := by omega
  rw [h8] at h3
  simp at h3
  linarith

theorem geoRep_zero : geoRep (0 : Euc d) = 0 := by
  refine eq_geoRep_of 0 0 (fun i => by simp) (fun i => ⟨0, by simp⟩)

/-- `geoRep z = z - v` when `v ∈ ℤ^d` and `z - v` has coordinates in `(-1/2,1/2]`. -/
theorem geoRep_eq_sub (z v : Euc d) (hv : ∀ i, ∃ m : ℤ, v i = m)
    (hz : ∀ i, -(1 / 2) < (z - v) i ∧ (z - v) i ≤ 1 / 2) : geoRep z = z - v := by
  refine eq_geoRep_of z (z - v) hz fun i => ?_
  obtain ⟨m, hm⟩ := hv i
  exact ⟨m, by simpa using hm⟩

/-- `geoRep z = z - n` when `‖z - n‖ < 1/4`, `n ∈ ℤ^d`. -/
theorem geoRep_eq_of_norm_lt (z : Euc d) (n : Lattice d) (h : ‖z - Lattice.toEuc n‖ < 1 / 4) :
    geoRep z = z - Lattice.toEuc n := by
  refine geoRep_eq_sub z _ (fun i => ⟨n i, by simp [Lattice.toEuc]⟩) fun i => ?_
  have := PiLp.norm_apply_le (z - Lattice.toEuc n) i
  rw [Real.norm_eq_abs] at this
  constructor <;> linarith [abs_le.1 (this.trans h.le)]

theorem coord_abs_le_norm (w : Euc d) (i : Fin d) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  rwa [Real.norm_eq_abs] at this

/-- The helper function `F(w) = χ(w)|w|² + (1-χ(w))/64`, so that `ψ(x) = F(centeredRep x)`. -/
def pairDispersionF (w : Euc d) : ℝ :=
  clusterBump d w * ‖w‖ ^ 2 + (1 - clusterBump d w) * (1 / 64)

theorem pairDispersion_eq_F (x : Torus d) :
    pairDispersion x = pairDispersionF (Torus.centeredRep x) := rfl

theorem contDiff_pairDispersionF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (pairDispersionF (d := d)) := by
  unfold pairDispersionF
  exact ((clusterBump d).contDiff.mul (contDiff_norm_sq ℝ)).add
    ((contDiff_const.sub (clusterBump d).contDiff).mul contDiff_const)

theorem pairDispersionF_eq_of_le_norm {w : Euc d} (hw : 1 / 4 ≤ ‖w‖) :
    pairDispersionF w = 1 / 64 := by
  unfold pairDispersionF
  have : clusterBump d w = 0 :=
    (clusterBump d).zero_of_le_dist (by simpa [clusterBump, dist_zero_right] using hw)
  rw [this]; ring

theorem pairDispersion_nonneg (x : Torus d) : 0 ≤ pairDispersion x := by
  rw [pairDispersion_eq_F]
  unfold pairDispersionF
  have h0 : 0 ≤ clusterBump d (Torus.centeredRep x) := (clusterBump d).nonneg
  have h1 : clusterBump d (Torus.centeredRep x) ≤ 1 := (clusterBump d).le_one
  exact add_nonneg (mul_nonneg h0 (sq_nonneg _)) (mul_nonneg (by linarith) (by norm_num))

theorem Torus.mk_zero : Torus.mk (0 : Euc d) = 0 := by
  funext i; simp [Torus.mk]

/-- `ψ` vanishes exactly at the origin. -/
theorem pairDispersion_eq_zero_iff (x : Torus d) : pairDispersion x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [pairDispersion_eq_F] at h
    unfold pairDispersionF at h
    set c := Torus.centeredRep x with hc
    have h0 : 0 ≤ clusterBump d c := (clusterBump d).nonneg
    have h1 : clusterBump d c ≤ 1 := (clusterBump d).le_one
    have ha : 0 ≤ clusterBump d c * ‖c‖ ^ 2 := mul_nonneg h0 (sq_nonneg _)
    have hb : 0 ≤ (1 - clusterBump d c) * (1 / 64) := mul_nonneg (by linarith) (by norm_num)
    have hb' : (1 - clusterBump d c) * (1 / 64) = 0 := by linarith
    have hchi : clusterBump d c = 1 := by linarith
    have ha' : clusterBump d c * ‖c‖ ^ 2 = 0 := by linarith
    rw [hchi, one_mul] at ha'
    have hc0 : c = 0 := norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 ha')
    rw [← Torus.mk_centeredRep x, ← hc, hc0, Torus.mk_zero]
  · rintro rfl
    have : Torus.centeredRep (0 : Torus d) = 0 := by
      have := geoRep_zero (d := d)
      rwa [geoRep, Torus.mk_zero] at this
    rw [pairDispersion_eq_F, this]
    unfold pairDispersionF
    have : clusterBump d (0 : Euc d) = 1 :=
      (clusterBump d).one_of_mem_closedBall (by simp [clusterBump])
    rw [this]; simp

/-- `ψ` is the squared geodesic distance on `{|c| ≤ 1/8}`. -/
theorem pairDispersion_eq_sq (x : Torus d) (hx : ‖Torus.centeredRep x‖ ≤ 1 / 8) :
    pairDispersion x = ‖Torus.centeredRep x‖ ^ 2 := by
  rw [pairDispersion_eq_F]
  unfold pairDispersionF
  have : clusterBump d (Torus.centeredRep x) = 1 :=
    (clusterBump d).one_of_mem_closedBall (by simpa [clusterBump] using hx)
  rw [this]; ring

/-- `ψ ≥ 1/64` off `{|c| < 1/8}`. -/
theorem le_pairDispersion (x : Torus d) (hx : 1 / 8 ≤ ‖Torus.centeredRep x‖) :
    1 / 64 ≤ pairDispersion x := by
  rw [pairDispersion_eq_F]
  unfold pairDispersionF
  have h0 : 0 ≤ clusterBump d (Torus.centeredRep x) := (clusterBump d).nonneg
  have h1 : clusterBump d (Torus.centeredRep x) ≤ 1 := (clusterBump d).le_one
  have h2 : 1 / 64 ≤ ‖Torus.centeredRep x‖ ^ 2 := by nlinarith
  nlinarith

/-- `ψ ∈ C^∞(𝕋^d)`. -/
theorem pairDispersion_smooth : Torus.IsSmooth (pairDispersion (d := d)) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [contDiff_iff_contDiffAt]
  intro z0
  have hlift : ∀ z, Torus.lift (pairDispersion (d := d)) z = pairDispersionF (geoRep z) :=
    fun z => rfl
  by_cases h : ∀ i, geoRep z0 i < 1 / 2
  · -- away from the cut locus: `geoRep` is locally `z - v`
    set v : Euc d := z0 - geoRep z0 with hv
    have hvint : ∀ i, ∃ m : ℤ, v i = m := fun i => by
      obtain ⟨m, hm⟩ := geoRep_int z0 i
      exact ⟨m, by simpa [hv] using hm⟩
    have hev : ∀ᶠ z in 𝓝 z0, ∀ i, -(1 / 2) < (z - v) i ∧ (z - v) i ≤ 1 / 2 := by
      refine Filter.eventually_all.2 fun i => ?_
      have hc : Continuous fun z : Euc d => (z - v) i := by
        have : Continuous fun z : Euc d => z i := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous
        exact this.sub continuous_const
      have e0 : (z0 - v) i = geoRep z0 i := by simp [hv]
      have h1 : ∀ᶠ z in 𝓝 z0, -(1 / 2) < (z - v) i :=
        continuousAt_const.eventually_lt hc.continuousAt (by rw [e0]; exact (geoRep_coord z0 i).1)
      have h2 : ∀ᶠ z in 𝓝 z0, (z - v) i < 1 / 2 :=
        hc.continuousAt.eventually_lt continuousAt_const (by rw [e0]; exact h i)
      filter_upwards [h1, h2] with z a b using ⟨a, b.le⟩
    have heq : Torus.lift (pairDispersion (d := d)) =ᶠ[𝓝 z0] fun z => pairDispersionF (z - v) := by
      filter_upwards [hev] with z hz
      rw [hlift, geoRep_eq_sub z v hvint hz]
    exact ((contDiff_pairDispersionF.comp (contDiff_id.sub contDiff_const)).contDiffAt).congr_of_eventuallyEq heq
  · -- at the cut locus: `ψ ≡ 1/64` nearby
    push Not at h
    obtain ⟨i0, hi0⟩ := h
    have hi0' : geoRep z0 i0 = 1 / 2 := le_antisymm (geoRep_coord z0 i0).2 hi0
    have heq : Torus.lift (pairDispersion (d := d)) =ᶠ[𝓝 z0] fun _ => (1 / 64 : ℝ) := by
      have hball : Metric.ball z0 (1 / 4) ∈ 𝓝 z0 := Metric.ball_mem_nhds _ (by norm_num)
      filter_upwards [hball] with z hz
      rw [hlift]
      apply pairDispersionF_eq_of_le_norm
      refine le_trans ?_ (coord_abs_le_norm (geoRep z) i0)
      by_contra hlt
      push Not at hlt
      obtain ⟨m1, h1⟩ := geoRep_int z i0
      obtain ⟨m2, h2⟩ := geoRep_int z0 i0
      have hd : |z i0 - z0 i0| < 1 / 4 := by
        have := coord_abs_le_norm (z - z0) i0
        rw [Metric.mem_ball, dist_eq_norm] at hz
        simpa using this.trans_lt hz
      have hg := abs_lt.1 hlt
      have hd' := abs_lt.1 hd
      have h3 : ((m1 - m2 : ℤ) : ℝ) = (z i0 - z0 i0) - geoRep z i0 + 1 / 2 := by
        push_cast; rw [hi0'] at h2; linarith
      have h4 : (0 : ℝ) < ((m1 - m2 : ℤ) : ℝ) := by rw [h3]; linarith
      have h5 : ((m1 - m2 : ℤ) : ℝ) < 1 := by rw [h3]; linarith
      have h6 : 0 < m1 - m2 := by exact_mod_cast h4
      have h7 : m1 - m2 < 1 := by exact_mod_cast h5
      omega
    exact (contDiffAt_const).congr_of_eventuallyEq heq

theorem clusterDispersion_nonneg (I : Finset (Fin N)) (X : Config d N) :
    0 ≤ clusterDispersion I X := by
  unfold clusterDispersion
  exact mul_nonneg (by positivity)
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => pairDispersion_nonneg _)

/-- `Q_I⁻¹(0) = Δ_I` (M L11779). -/
theorem clusterDispersion_eq_zero_iff (I : Finset (Fin N)) (X : Config d N) :
    clusterDispersion I X = 0 ↔ X ∈ clusterDiagonal I := by
  unfold clusterDispersion clusterDiagonal
  constructor
  · intro h i hi j hj
    have hk : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.2 ⟨i, hi⟩
    have hsum : ∑ i ∈ I, ∑ j ∈ I, pairDispersion (X i - X j) = 0 := by
      rcases mul_eq_zero.1 h with h1 | h1
      · exfalso; revert h1; positivity
      · exact h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ => pairDispersion_nonneg (X i - X j))).1 hsum i hi
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => pairDispersion_nonneg (X i - X j))).1 h2 j hj
    exact sub_eq_zero.1 ((pairDispersion_eq_zero_iff _).1 h3)
  · intro h
    have : ∀ i ∈ I, ∀ j ∈ I, pairDispersion (X i - X j) = 0 := fun i hi j hj => by
      rw [h i hi j hj, sub_self]; exact (pairDispersion_eq_zero_iff 0).2 rfl
    rw [Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => this i hi j hj, mul_zero]

/-- `Q_I ∈ C^∞((𝕋^d)^N)`: its lift to the covering space is `C^∞` (M L11779). -/
theorem contDiff_clusterDispersionLift (I : Finset (Fin N)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (clusterDispersionLift (d := d) I) := by
  have hfun : clusterDispersionLift (d := d) I = fun Y => (1 / (2 * (I.card : ℝ))) *
      ∑ i ∈ I, ∑ j ∈ I, Torus.lift pairDispersion (Y i - Y j) := by
    funext Y
    unfold clusterDispersionLift clusterDispersion
    congr 1
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (pairDispersion (d := d))) :=
    pairDispersion_smooth
  rw [hfun]
  refine contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_)
  exact hs.comp ((contDiff_apply ℝ _ i).sub (contDiff_apply ℝ _ j))

/-- Pairwise identity for vectors: `∑_{i,j}|a_i - a_j|² = 2k ∑|a_i|² - 2|∑ a_i|²`. -/
theorem sum_sum_norm_sub_sq {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (I : Finset ι) (a : ι → V) :
    ∑ i ∈ I, ∑ j ∈ I, ‖a i - a j‖ ^ 2 =
      2 * (I.card : ℝ) * ∑ i ∈ I, ‖a i‖ ^ 2 - 2 * ‖∑ i ∈ I, a i‖ ^ 2 := by
  have h : ∀ i j, ‖a i - a j‖ ^ 2 = ‖a i‖ ^ 2 - 2 * inner ℝ (a i) (a j) + ‖a j‖ ^ 2 :=
    fun i j => norm_sub_sq_real _ _
  have hin : ∑ i ∈ I, ∑ j ∈ I, inner ℝ (a i) (a j) = ‖∑ i ∈ I, a i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hin,
    Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- Mean identity: `∑|a_i - ā|² = ∑|a_i|² - |∑ a_i|²/k`. -/
theorem sum_norm_sub_mean_sq {ι V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (I : Finset ι) (a : ι → V) :
    ∑ i ∈ I, ‖a i - (1 / (I.card : ℝ)) • ∑ j ∈ I, a j‖ ^ 2 =
      ∑ i ∈ I, ‖a i‖ ^ 2 - ‖∑ i ∈ I, a i‖ ^ 2 / (I.card : ℝ) := by
  by_cases hk : I.card = 0
  · rw [Finset.card_eq_zero.1 hk]; simp
  have hk' : (I.card : ℝ) ≠ 0 := by exact_mod_cast hk
  set S := ∑ j ∈ I, a j with hS
  have h : ∀ i, ‖a i - (1 / (I.card : ℝ)) • S‖ ^ 2 =
      ‖a i‖ ^ 2 - 2 * (1 / (I.card : ℝ)) * inner ℝ (a i) S + (1 / (I.card : ℝ)) ^ 2 * ‖S‖ ^ 2 := by
    intro i
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  have hin : ∑ i ∈ I, inner ℝ (a i) S = ‖S‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← sum_inner]
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hin,
    Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

/-- Compatibility of geodesic representatives: if `y_p, y_q` are within `1/8` of `y_r`, then
`geoRep(y_p - y_q) = geoRep(y_p - y_r) - geoRep(y_q - y_r)`. -/
theorem geoRep_sub_compat (Y : Fin N → Euc d) (p q r : Fin N)
    (hp : ‖geoRep (Y p - Y r)‖ < 1 / 8) (hq : ‖geoRep (Y q - Y r)‖ < 1 / 8) :
    geoRep (Y p - Y q) = geoRep (Y p - Y r) - geoRep (Y q - Y r) := by
  refine eq_geoRep_of _ _ (fun i => ?_) (fun i => ?_)
  · have h1 := coord_abs_le_norm (geoRep (Y p - Y r)) i
    have h2 := coord_abs_le_norm (geoRep (Y q - Y r)) i
    have h3 := abs_le.1 (h1.trans hp.le)
    have h4 := abs_le.1 (h2.trans hq.le)
    simp only [PiLp.sub_apply]
    constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  · obtain ⟨m1, h1⟩ := geoRep_int (Y p - Y r) i
    obtain ⟨m2, h2⟩ := geoRep_int (Y q - Y r) i
    refine ⟨m1 - m2, ?_⟩
    simp only [PiLp.sub_apply] at h1 h2 ⊢
    push_cast
    linarith

/-- When all internal pairs are within geodesic distance `1/8`, `Q_I` is the Euclidean expression
of the compatible lifts. -/
theorem cluster_euclid_of_pairs (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hpairs : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < 1 / 8) :
    clusterDispersionLift I Y =
        (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 ∧
      clusterDispersionLift I Y = ∑ i ∈ I, ‖clusterCentered I Y i‖ ^ 2 := by
  have h1 : clusterDispersionLift I Y =
      (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 := by
    unfold clusterDispersionLift clusterDispersion
    congr 1
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [← mk_sub']
    exact pairDispersion_eq_sq _ (hpairs i hi j hj).le
  refine ⟨h1, ?_⟩
  by_cases hI : I = ∅
  · subst hI; simp [clusterDispersionLift, clusterDispersion]
  obtain ⟨i0, hi0⟩ := Finset.nonempty_iff_ne_empty.2 hI
  have hk : (I.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 ⟨i0, hi0⟩).ne'
  set a : Fin N → Euc d := fun i => geoRep (Y i - Y i0) with ha
  have hcomp : ∀ i ∈ I, ∀ j ∈ I, geoRep (Y i - Y j) = a i - a j := fun i hi j hj =>
    geoRep_sub_compat Y i j i0 (hpairs i hi i0 hi0) (hpairs j hj i0 hi0)
  have hcc : ∀ i ∈ I, clusterCentered I Y i = a i - (1 / (I.card : ℝ)) • ∑ j ∈ I, a j := by
    intro i hi
    unfold clusterCentered
    rw [if_pos hi, Finset.sum_congr rfl fun j hj => hcomp i hi j hj, Finset.sum_sub_distrib,
      Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hk]
  have e1 : ∑ i ∈ I, ‖clusterCentered I Y i‖ ^ 2 =
      ∑ i ∈ I, ‖a i - (1 / (I.card : ℝ)) • ∑ j ∈ I, a j‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi => by rw [hcc i hi]
  have e2 : ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 = ∑ i ∈ I, ∑ j ∈ I, ‖a i - a j‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => by rw [hcomp i hi j hj]
  rw [h1, e1, e2, sum_norm_sub_mean_sq, sum_sum_norm_sub_sq]
  field_simp

/-- Below `clusterRadius I` every internal pair is within geodesic distance `1/8` and `Q_I` is
the Euclidean expression `∑_{i∈I}|ỹ_i - ȳ_I|²` of the compatible lifts (M L11779, L11765). -/
theorem clusterDispersionLift_eq_euclid (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hq : clusterDispersionLift I Y < clusterRadius I) :
    (∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < 1 / 8) ∧
      clusterDispersionLift I Y =
        (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 ∧
      clusterDispersionLift I Y = ∑ i ∈ I, ‖clusterCentered I Y i‖ ^ 2 := by
  have hk : 0 < I.card := by
    rcases Nat.eq_zero_or_pos I.card with h | h
    · exfalso
      rw [Finset.card_eq_zero.1 h] at hq
      simp [clusterDispersionLift, clusterDispersion, clusterRadius] at hq
    · exact h
  have hk' : (0 : ℝ) < I.card := by exact_mod_cast hk
  have hpairs : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < 1 / 8 := by
    intro i hi j hj
    by_contra hnot
    push Not at hnot
    have hle := le_pairDispersion (Torus.mk (Y i) - Torus.mk (Y j))
      (by rw [← mk_sub']; exact hnot)
    have hsingle : pairDispersion (Torus.mk (Y i) - Torus.mk (Y j)) ≤
        ∑ i ∈ I, ∑ j ∈ I, pairDispersion (Torus.mk (Y i) - Torus.mk (Y j)) :=
      (Finset.single_le_sum (f := fun j => pairDispersion (Torus.mk (Y i) - Torus.mk (Y j)))
        (fun j _ => pairDispersion_nonneg _) hj).trans
        (Finset.single_le_sum (f := fun i => ∑ j ∈ I, pairDispersion (Torus.mk (Y i) - Torus.mk (Y j)))
          (fun i _ => Finset.sum_nonneg fun j _ => pairDispersion_nonneg _) hi)
    unfold clusterDispersionLift clusterDispersion clusterRadius at hq
    rw [div_mul_eq_mul_div, one_mul, div_lt_div_iff₀ (by positivity) (by positivity)] at hq
    nlinarith
  obtain ⟨h1, h2⟩ := cluster_euclid_of_pairs I Y hpairs
  exact ⟨hpairs, h1, h2⟩

/-- The enlargement identity `B:eq:cluster-enlargement` (M L11770):
`Q_{I∪{j}} = Q_I + (k/(k+1)) |x_j - x̄_I|²` for `j ∉ I`, below the radius of `I ∪ {j}`. -/
theorem clusterDispersionLift_insert (I : Finset (Fin N)) (Y : Fin N → Euc d) (j : Fin N)
    (hj : j ∉ I) (hq : clusterDispersionLift (insert j I) Y < clusterRadius (insert j I)) :
    clusterDispersionLift (insert j I) Y = clusterDispersionLift I Y +
      ((I.card : ℝ) / ((I.card : ℝ) + 1)) *
        ‖(1 / (I.card : ℝ)) • ∑ i ∈ I, geoRep (Y j - Y i)‖ ^ 2 := by
  obtain ⟨hpJ, hJ, -⟩ := clusterDispersionLift_eq_euclid (insert j I) Y hq
  have hpI : ∀ i ∈ I, ∀ l ∈ I, ‖geoRep (Y i - Y l)‖ < 1 / 8 := fun i hi l hl =>
    hpJ i (Finset.mem_insert_of_mem hi) l (Finset.mem_insert_of_mem hl)
  have hI := (cluster_euclid_of_pairs I Y hpI).1
  set a : Fin N → Euc d := fun i => geoRep (Y i - Y j) with ha
  have haj : a j = 0 := by simp [ha, geoRep_zero]
  have hcomp : ∀ i ∈ insert j I, ∀ l ∈ insert j I, geoRep (Y i - Y l) = a i - a l :=
    fun i hi l hl => geoRep_sub_compat Y i l j (hpJ i hi j (Finset.mem_insert_self _ _))
      (hpJ l hl j (Finset.mem_insert_self _ _))
  have hcompI : ∀ i ∈ I, ∀ l ∈ I, geoRep (Y i - Y l) = a i - a l := fun i hi l hl =>
    hcomp i (Finset.mem_insert_of_mem hi) l (Finset.mem_insert_of_mem hl)
  have hneg : ∀ i ∈ I, geoRep (Y j - Y i) = - a i := by
    intro i hi
    rw [hcomp j (Finset.mem_insert_self _ _) i (Finset.mem_insert_of_mem hi), haj, zero_sub]
  rw [Finset.sum_congr rfl hneg, Finset.sum_neg_distrib, smul_neg, norm_neg]
  have hcardJ : ((insert j I).card : ℝ) = I.card + 1 := by
    rw [Finset.card_insert_of_notMem hj]; push_cast; ring
  have eJ : ∑ i ∈ insert j I, ∑ l ∈ insert j I, ‖geoRep (Y i - Y l)‖ ^ 2 =
      ∑ i ∈ insert j I, ∑ l ∈ insert j I, ‖a i - a l‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => by rw [hcomp i hi l hl]
  have eI : ∑ i ∈ I, ∑ l ∈ I, ‖geoRep (Y i - Y l)‖ ^ 2 = ∑ i ∈ I, ∑ l ∈ I, ‖a i - a l‖ ^ 2 :=
    Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun l hl => by rw [hcompI i hi l hl]
  rw [hJ, hI, hcardJ, eJ, eI]
  by_cases hk : I.card = 0
  · rw [Finset.card_eq_zero.1 hk]; simp [haj]
  have hk' : (I.card : ℝ) ≠ 0 := by exact_mod_cast hk
  simp only [Finset.sum_insert hj, haj, sub_self, norm_zero, zero_sub, sub_zero, norm_neg,
    Finset.sum_add_distrib]
  rw [sum_sum_norm_sub_sq]
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp
  field_simp
  ring

/-- The Euclidean quadratic form `(2k)⁻¹ ∑_{i,j∈I} |(Y_i - n_i) - (Y_j - n_j)|²` with a fixed
integer shift `n`: the local Euclidean form of `Q_I` below the radius. -/
def clusterQuad (I : Finset (Fin N)) (n : Fin N → Euc d) (Y : Fin N → Euc d) : ℝ :=
  (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I, ‖(Y i - n i) - (Y j - n j)‖ ^ 2

theorem fderiv_clusterQuad (I : Finset (Fin N)) (n Y v : Fin N → Euc d) :
    fderiv ℝ (clusterQuad I n) Y v = (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I,
      2 * inner ℝ ((Y i - n i) - (Y j - n j)) (v i - v j) := by
  have h1 : ∀ i j, HasFDerivAt (fun Y : Fin N → Euc d => (Y i - n i) - (Y j - n j))
        ((ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d) - ContinuousLinearMap.proj j) Y :=
    fun i j => ((hasFDerivAt_apply i Y).sub_const (n i)).sub ((hasFDerivAt_apply j Y).sub_const (n j))
  have hterm := fun i j => (h1 i j).norm_sq
  have hsum := HasFDerivAt.const_mul (HasFDerivAt.fun_sum (u := I) (fun i _ =>
    HasFDerivAt.fun_sum (u := I) (fun j _ => hterm i j))) (1 / (2 * (I.card : ℝ)))
  have := hsum.fderiv
  unfold clusterQuad
  rw [this]
  simp only [smul_apply, sum_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply, sub_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]

theorem cluster_card_pos (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hq : clusterDispersionLift I Y < clusterRadius I) : 0 < I.card := by
  rcases Nat.eq_zero_or_pos I.card with h | h
  · exfalso
    rw [Finset.card_eq_zero.1 h] at hq
    simp [clusterDispersionLift, clusterDispersion, clusterRadius] at hq
  · exact h

theorem geoRep_antisymm (Y : Fin N → Euc d) (i j : Fin N) (h : ‖geoRep (Y i - Y j)‖ < 1 / 8) :
    geoRep (Y j - Y i) = - geoRep (Y i - Y j) := by
  refine eq_geoRep_of _ _ (fun k => ?_) (fun k => ?_)
  · have := abs_le.1 ((coord_abs_le_norm (geoRep (Y i - Y j)) k).trans h.le)
    simp only [PiLp.neg_apply]
    constructor <;> linarith [this.1, this.2]
  · obtain ⟨m, hm⟩ := geoRep_int (Y i - Y j) k
    refine ⟨-m, ?_⟩
    simp only [PiLp.sub_apply, PiLp.neg_apply] at hm ⊢
    push_cast
    linarith

theorem clusterDispersionLift_local (I : Finset (Fin N)) (Y0 : Fin N → Euc d)
    (hq : clusterDispersionLift I Y0 < clusterRadius I) :
    ∃ n : Fin N → Euc d,
      (∀ i ∈ I, ∀ j ∈ I, (Y0 i - n i) - (Y0 j - n j) = geoRep (Y0 i - Y0 j)) ∧
        clusterDispersionLift I =ᶠ[𝓝 Y0] clusterQuad I n := by
  obtain ⟨hpairs, -, -⟩ := clusterDispersionLift_eq_euclid I Y0 hq
  obtain ⟨i0, hi0⟩ := Finset.card_pos.1 (cluster_card_pos I Y0 hq)
  set n : Fin N → Euc d := fun i => (Y0 i - Y0 i0) - geoRep (Y0 i - Y0 i0) with hn
  have hnint : ∀ i k, ∃ m : ℤ, n i k = m := fun i k => by
    obtain ⟨m, hm⟩ := geoRep_int (Y0 i - Y0 i0) k
    exact ⟨m, by simpa [hn] using hm⟩
  have hw0 : ∀ i ∈ I, ∀ j ∈ I, (Y0 i - n i) - (Y0 j - n j) = geoRep (Y0 i - Y0 j) := by
    intro i hi j hj
    rw [geoRep_sub_compat Y0 i j i0 (hpairs i hi i0 hi0) (hpairs j hj i0 hi0)]
    simp only [hn]; abel
  refine ⟨n, hw0, ?_⟩
  have hcont : ∀ (i : Fin N) (k : Fin d), Continuous fun Y : Fin N → Euc d => Y i k := fun i k =>
    (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).continuous.comp (continuous_apply i)
  have h1 : ∀ᶠ Y in 𝓝 Y0, clusterDispersionLift I Y < clusterRadius I :=
    (contDiff_clusterDispersionLift (d := d) I).continuous.continuousAt.eventually_lt
      continuousAt_const hq
  have h2 : ∀ᶠ Y in 𝓝 Y0, ∀ i ∈ I, ∀ j ∈ I, ∀ k : Fin d,
      -(1 / 2) < ((Y i - n i) - (Y j - n j)) k ∧ ((Y i - n i) - (Y j - n j)) k ≤ 1 / 2 := by
    refine (Filter.eventually_all_finset I).2 fun i hi => (Filter.eventually_all_finset I).2
      fun j hj => Filter.eventually_all.2 fun k => ?_
    have hc : Continuous fun Y : Fin N → Euc d => ((Y i - n i) - (Y j - n j)) k := by
      have := ((hcont i k).sub (continuous_const (y := n i k))).sub ((hcont j k).sub (continuous_const (y := n j k)))
      exact this
    have hv : ((Y0 i - n i) - (Y0 j - n j)) k = geoRep (Y0 i - Y0 j) k := by rw [hw0 i hi j hj]
    have hb := abs_lt.1 ((coord_abs_le_norm (geoRep (Y0 i - Y0 j)) k).trans_lt (hpairs i hi j hj))
    have e1 : ∀ᶠ Y in 𝓝 Y0, -(1 / 2) < ((Y i - n i) - (Y j - n j)) k :=
      continuousAt_const.eventually_lt hc.continuousAt (by rw [hv]; linarith [hb.1])
    have e2 : ∀ᶠ Y in 𝓝 Y0, ((Y i - n i) - (Y j - n j)) k < 1 / 2 :=
      hc.continuousAt.eventually_lt continuousAt_const (by rw [hv]; linarith [hb.2])
    filter_upwards [e1, e2] with Y a b using ⟨a, b.le⟩
  filter_upwards [h1, h2] with Y hY hw
  obtain ⟨-, h3, -⟩ := clusterDispersionLift_eq_euclid I Y hY
  rw [h3]
  unfold clusterQuad
  congr 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [eq_geoRep_of (Y i - Y j) ((Y i - n i) - (Y j - n j)) (hw i hi j hj) (fun k => ?_)]
  obtain ⟨m1, h1⟩ := hnint i k
  obtain ⟨m2, h2⟩ := hnint j k
  refine ⟨m1 - m2, ?_⟩
  simp only [PiLp.sub_apply]
  push_cast
  linarith

/-- Regrouping of the pair sum into the single sum `∑_i ⟨2 cc_i, v_i⟩`. -/
theorem cluster_pair_regroup (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hpairs : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < 1 / 8) (hk : 0 < I.card)
    (v : Fin N → Euc d) :
    (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I,
        2 * inner ℝ (geoRep (Y i - Y j)) (v i - v j) =
      ∑ i, inner ℝ ((2 : ℝ) • clusterCentered I Y i) (v i) := by
  have hk' : (I.card : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hanti : ∀ i ∈ I, ∀ j ∈ I, geoRep (Y j - Y i) = - geoRep (Y i - Y j) :=
    fun i hi j hj => geoRep_antisymm Y i j (hpairs i hi j hj)
  have e1 : ∑ i ∈ I, ∑ j ∈ I, 2 * inner ℝ (geoRep (Y i - Y j)) (v i - v j) =
      ∑ i ∈ I, ∑ j ∈ I, 2 * inner ℝ (geoRep (Y i - Y j)) (v i) -
        ∑ i ∈ I, ∑ j ∈ I, 2 * inner ℝ (geoRep (Y i - Y j)) (v j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_sub_right]; ring
  have e2 : ∑ i ∈ I, ∑ j ∈ I, 2 * inner ℝ (geoRep (Y i - Y j)) (v j) =
      - ∑ i ∈ I, ∑ j ∈ I, 2 * inner ℝ (geoRep (Y i - Y j)) (v i) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hanti i hi j hj, inner_neg_left]; ring
  have e3 : ∀ i ∈ I, ∑ j ∈ I, 2 * inner ℝ (geoRep (Y i - Y j)) (v i) =
      inner ℝ ((2 : ℝ) • clusterCentered I Y i) (v i) * (I.card : ℝ) := by
    intro i hi
    unfold clusterCentered
    rw [if_pos hi, ← Finset.mul_sum, ← sum_inner, smul_smul, real_inner_smul_left]
    field_simp
  have e4 : ∑ i, inner ℝ ((2 : ℝ) • clusterCentered I Y i) (v i) =
      ∑ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i) (v i) :=
    (Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by
      simp [clusterCentered, hi])).symm
  rw [e1, e2, e4, Finset.sum_congr rfl e3, ← Finset.sum_mul]
  field_simp
  ring

/-- `∇_{x_i} Q_I = 2(x_i - x̄_I)` for `i ∈ I`, `0` otherwise (M L11807), below the radius. -/
theorem fderiv_clusterDispersionLift (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hq : clusterDispersionLift I Y < clusterRadius I) (v : Fin N → Euc d) :
    fderiv ℝ (clusterDispersionLift I) Y v =
      ∑ i, inner ℝ ((2 : ℝ) • clusterCentered I Y i) (v i) := by
  obtain ⟨hpairs, -, -⟩ := clusterDispersionLift_eq_euclid I Y hq
  obtain ⟨n, hn, hev⟩ := clusterDispersionLift_local I Y hq
  rw [hev.fderiv_eq, fderiv_clusterQuad,
    ← cluster_pair_regroup I Y hpairs (cluster_card_pos I Y hq) v]
  congr 1
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
  rw [hn i hi j hj]

/-- `∑_{i∈I} |∇_{x_i} Q_I|² = 4 Q_I` (M L11809), below the radius. -/
theorem sum_sq_grad_clusterDispersionLift (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hq : clusterDispersionLift I Y < clusterRadius I) :
    ∑ i, ‖(2 : ℝ) • clusterCentered I Y i‖ ^ 2 = 4 * clusterDispersionLift I Y := by
  obtain ⟨-, -, h3⟩ := clusterDispersionLift_eq_euclid I Y hq
  have e4 : ∑ i, ‖(2 : ℝ) • clusterCentered I Y i‖ ^ 2 =
      ∑ i ∈ I, ‖(2 : ℝ) • clusterCentered I Y i‖ ^ 2 :=
    (Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => by
      simp [clusterCentered, hi])).symm
  rw [e4, h3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_smul]; simp; ring

/-- Second derivative of `Q_I` below the radius. -/
theorem fderiv_fderiv_clusterDispersionLift (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hq : clusterDispersionLift I Y < clusterRadius I) (v w : Fin N → Euc d) :
    fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y w v =
      (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I, 2 * inner ℝ (w i - w j) (v i - v j) := by
  obtain ⟨n, hn, hev⟩ := clusterDispersionLift_local I Y hq
  have hQ := contDiff_clusterDispersionLift (d := d) (N := N) I
  have hdiff : DifferentiableAt ℝ (fderiv ℝ (clusterDispersionLift (d := d) I)) Y := by
    have := hQ.fderiv_right (m := 1) (by norm_cast)
    exact (this.differentiable (by norm_num)).differentiableAt
  set L : (Fin N → Euc d) → ℝ := fun Y' => (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I,
      2 * inner ℝ (v i - v j) ((Y' i - n i) - (Y' j - n j)) with hL
  have h1 : (fun Y' => fderiv ℝ (clusterDispersionLift I) Y' v) =ᶠ[𝓝 Y] L := by
    filter_upwards [Filter.EventuallyEq.fderiv (𝕜 := ℝ) hev] with Y' hY'
    rw [hY', fderiv_clusterQuad]
    simp only [hL, real_inner_comm]
  have hproj : ∀ i j, HasFDerivAt (fun Y' : Fin N → Euc d => (Y' i - n i) - (Y' j - n j))
        ((ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d) - ContinuousLinearMap.proj j) Y :=
    fun i j => ((hasFDerivAt_apply i Y).sub_const (n i)).sub ((hasFDerivAt_apply j Y).sub_const (n j))
  have hterm := fun i j => ((innerSL ℝ (v i - v j)).hasFDerivAt.comp Y (hproj i j)).const_mul 2
  have hLd := HasFDerivAt.const_mul (HasFDerivAt.fun_sum (u := I) (fun i _ =>
    HasFDerivAt.fun_sum (u := I) (fun j _ => hterm i j))) (1 / (2 * (I.card : ℝ)))
  have e1 : fderiv ℝ (fun Y' => fderiv ℝ (clusterDispersionLift I) Y' v) Y = fderiv ℝ L Y :=
    h1.fderiv_eq
  have e2 : fderiv ℝ (fun Y' => fderiv ℝ (clusterDispersionLift I) Y' v) Y =
      (fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y).flip v := by
    have := fderiv_clm_apply (c := fderiv ℝ (clusterDispersionLift (d := d) I)) (u := fun _ => v)
      (x := Y) hdiff (differentiableAt_const v)
    simpa using this
  have e3 : fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y w v =
      fderiv ℝ L Y w := by
    have := congrArg (fun f => f w) (e2.symm.trans e1)
    simpa using this
  have key := HasFDerivAt.fderiv (f := L) hLd
  rw [e3, key]
  simp only [smul_apply, sum_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm]

/-- `∑_{i∈I} Δ_{x_i} Q_I = 2d(k-1)` (M L11808), below the radius. -/
theorem laplacian_clusterDispersionLift (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hq : clusterDispersionLift I Y < clusterRadius I) :
    ∑ i : Fin N, ∑ a : Fin d,
      fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y (Pi.single i (EuclideanSpace.single a 1))
        (Pi.single i (EuclideanSpace.single a 1)) =
      2 * (d : ℝ) * ((I.card : ℝ) - 1) := by
  have hk := cluster_card_pos I Y hq
  have hk' : (I.card : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have key : ∀ (i : Fin N) (a : Fin d),
      fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y (Pi.single i (EuclideanSpace.single a 1))
        (Pi.single i (EuclideanSpace.single a 1)) = (1 / (I.card : ℝ)) * (if i ∈ I then 2 * ((I.card : ℝ) - 1) else 0) := by
    intro i a
    rw [fderiv_fderiv_clusterDispersionLift I Y hq]
    set e : Fin N → Euc d := Pi.single i (EuclideanSpace.single a 1) with he
    have h2 : ∀ i j, 2 * inner ℝ (e i - e j) (e i - e j) = 2 * ‖e i - e j‖ ^ 2 := fun i j => by
      rw [real_inner_self_eq_norm_sq]
    simp_rw [h2, ← Finset.mul_sum]
    rw [sum_sum_norm_sub_sq]
    have hT : ∑ p ∈ I, ‖e p‖ ^ 2 = if i ∈ I then 1 else 0 := by
      have : ∀ p, ‖e p‖ ^ 2 = (Pi.single i (1 : ℝ) : Fin N → ℝ) p := fun p => by
        by_cases hp : p = i
        · subst hp; simp [he]
        · simp [he, Pi.single_apply, hp]
      simp_rw [this]
      exact Finset.sum_pi_single' i 1 I
    have hS : ∑ p ∈ I, e p = if i ∈ I then EuclideanSpace.single a (1 : ℝ) else 0 := by
      exact Finset.sum_pi_single' i _ I
    rw [hT, hS]
    by_cases hi : i ∈ I <;> simp [hi] <;> field_simp
  simp_rw [key]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : Finset.filter (fun i => i ∈ I) Finset.univ = I := by ext; simp
  rw [this]
  field_simp

/-! ### The generator of `Q_I`: the internal term `𝒜_I` and the remainder `ℛ_I`
(Lemma `B:lem:cluster-ito`, M L11781-11845) -/

/-- The generator of the lifted particle SDE applied to `Q_I`:
`D Q_I(Y)[b(Y)] + ½ ∑_k D² Q_I(Y)[σ_k, σ_k]` (the Itô drift of `Q_I(Y_t)`). -/
def clusterGenerator (D : DynData d) (I : Finset (Fin N)) (Y : Fin N → Euc d) : ℝ :=
  fderiv ℝ (clusterDispersionLift I) Y (liftedDrift D Y) +
    (1 / 2) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y (liftedNoise D k) (liftedNoise D k)

/-- The singular internal term `𝒜_I = (2/N) ∑_{i<j∈I} (x_i - x_j) · M ∇g_E(x_i - x_j)`
(`B:eq:cluster-internal-formula`, M L11813, written as `N⁻¹ ∑_{i,j∈I}`), with the Euclidean
singular force at the geodesic representative of `y_i - y_j`. -/
def clusterInternal (D : DynData d) (I : Finset (Fin N)) (Y : Fin N → Euc d) : ℝ :=
  (1 / (N : ℝ)) * ∑ i ∈ I, ∑ j ∈ I,
    inner ℝ (geoRep (Y i - Y j)) (Torus.matVec D.M (eucRieszGrad D.s (geoRep (Y i - Y j))))

/-- The remainder `ℛ_I` of `B:eq:cluster-ito` (M L11785): the generator minus the constant
diffusion drift `2d(k-1)/β` and the internal term (exterior forces, the smooth part of the
kernel, and the confinement, M L11822-11844). -/
def clusterRemainder (D : DynData d) (I : Finset (Fin N)) (Y : Fin N → Euc d) : ℝ :=
  clusterGenerator D I Y - 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ - clusterInternal D I Y

/-- The constant diffusion drift: `½ ∑_k D² Q_I[σ_k, σ_k] = 2d(k-1)/β` below the radius
(M L11808, L11811). -/
theorem cluster_diffusion_term (D : DynData d) (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hq : clusterDispersionLift I Y < clusterRadius I) :
    (1 / 2) * ∑ k : Fin N × Fin d,
        fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y (liftedNoise D k) (liftedNoise D k) =
      2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ := by
  have hc : Real.sqrt (2 * D.invβ) * Real.sqrt (2 * D.invβ) = 2 * D.invβ :=
    Real.mul_self_sqrt (by linarith [D.hβ])
  have key : ∀ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y (liftedNoise D k) (liftedNoise D k) =
        2 * D.invβ * fderiv ℝ (fderiv ℝ (clusterDispersionLift I)) Y
          (Pi.single k.1 (EuclideanSpace.single k.2 1)) (Pi.single k.1 (EuclideanSpace.single k.2 1)) := by
    intro k
    simp only [liftedNoise, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, hc]
  have hl := laplacian_clusterDispersionLift I Y hq
  simp_rw [key]
  simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
  rw [hl]
  ring

/-- The quadratic variation density of the martingale term:
`∑_k (D Q_I[σ_k])² = (8/β) Q_I` (`B:eq:cluster-ito`, M L11787, from L11809). -/
theorem cluster_qv (D : DynData d) (I : Finset (Fin N)) (Y : Fin N → Euc d)
    (hq : clusterDispersionLift I Y < clusterRadius I) :
    ∑ k : Fin N × Fin d, (fderiv ℝ (clusterDispersionLift I) Y (liftedNoise D k)) ^ 2 =
      8 * D.invβ * clusterDispersionLift I Y := by
  have hc : Real.sqrt (2 * D.invβ) ^ 2 = 2 * D.invβ := Real.sq_sqrt (by linarith [D.hβ])
  have key : ∀ k : Fin N × Fin d, fderiv ℝ (clusterDispersionLift I) Y (liftedNoise D k) =
      Real.sqrt (2 * D.invβ) * (2 * clusterCentered I Y k.1 k.2) := by
    intro k
    rw [fderiv_clusterDispersionLift I Y hq, Finset.sum_eq_single k.1]
    · have hin : ∀ (x : Euc d) (a : Fin d), inner ℝ x (EuclideanSpace.single a (1 : ℝ)) = x a := by
        intro x a; simp [EuclideanSpace.inner_single_right]
      simp [liftedNoise, inner_smul_right, hin]
    · intro i _ hi
      simp [liftedNoise, Pi.single_apply, hi]
    · simp
  have hn : ∀ i, ∑ a : Fin d, (2 * clusterCentered I Y i a) ^ 2 =
      ‖(2 : ℝ) • clusterCentered I Y i‖ ^ 2 := by
    intro i
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Real.norm_eq_abs, PiLp.smul_apply, smul_eq_mul]
    rw [sq_abs]
  have key2 : ∀ k : Fin N × Fin d,
      (fderiv ℝ (clusterDispersionLift I) Y (liftedNoise D k)) ^ 2 =
        2 * D.invβ * (2 * clusterCentered I Y k.1 k.2) ^ 2 := fun k => by rw [key k, mul_pow, hc]
  simp_rw [key2]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, hn]
  rw [sum_sq_grad_clusterDispersionLift I Y hq]
  ring

open Matrix in
theorem inner_matVec_eq (M : Matrix (Fin d) (Fin d) ℝ) (z : Euc d) :
    inner ℝ z (Torus.matVec M z) = (z.ofLp) ⬝ᵥ (M *ᵥ z.ofLp) := by
  unfold Torus.matVec
  have : Matrix.toEuclideanLin M z = WithLp.toLp 2 (M *ᵥ z.ofLp) := by
    rfl
  rw [this]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

open Matrix in
theorem inner_matVec_nonpos {M : Matrix (Fin d) (Fin d) ℝ} (hM : Torus.SymNonpos M) (z : Euc d) :
    inner ℝ z (Torus.matVec M z) ≤ 0 := by
  rw [inner_matVec_eq]
  have h := hM.dotProduct_mulVec_nonneg z.ofLp
  have e : (z.ofLp) ⬝ᵥ ((Torus.symPart M) *ᵥ z.ofLp) = (z.ofLp) ⬝ᵥ (M *ᵥ z.ofLp) := by
    have h1 : (z.ofLp) ⬝ᵥ (Mᵀ *ᵥ z.ofLp) = (z.ofLp) ⬝ᵥ (M *ᵥ z.ofLp) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
    unfold Torus.symPart
    rw [smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, h1]
    simp; ring
  simp only [star_trivial, neg_mulVec, dotProduct_neg, e] at h
  linarith

/-- `𝒜_I ≥ 0` (`B:eq:cluster-internal-positive`, M L11791): `z · M ∇g_E(z) = -a_s(z) zᵀ Sym(M) z`
and `Sym M ≤ 0` (M L11815-11820); the antisymmetric part of `M` drops out. -/
theorem clusterInternal_nonneg (D : DynData d) (hM : Torus.SymNonpos D.M) (I : Finset (Fin N))
    (Y : Fin N → Euc d) : 0 ≤ clusterInternal D I Y := by
  unfold clusterInternal
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_)
  generalize geoRep (Y i - Y j) = z
  by_cases hz : z = 0
  · simp [hz]
  have ha := rieszRadial_pos D.hs0 hz
  unfold eucRieszGrad
  have e : Torus.matVec D.M (-(rieszRadial D.s z) • z) = -(rieszRadial D.s z) • Torus.matVec D.M z := by
    unfold Torus.matVec; exact map_smul _ _ _
  rw [e, real_inner_smul_right]
  have := inner_matVec_nonpos hM z
  nlinarith

/-- Coordinatewise, `|centeredRep z|_i` is the norm of `z_i` in the circle `ℝ/ℤ`. -/
theorem Torus.abs_centeredRep_apply (z : Torus d) (i : Fin d) :
    |Torus.centeredRep z i| = ‖z i‖ := by
  have hz : z i = (((Torus.rep z) i : ℝ) : UnitAddCircle) := by
    have := congrFun (Torus.mk_rep z) i
    simpa [Torus.mk] using this.symm
  have hr : (Torus.rep z) i ∈ Set.Ico (0 : ℝ) 1 := by
    have := (AddCircle.equivIco (1 : ℝ) 0 (z i)).2
    simpa [Torus.rep] using this
  have hc : Torus.centeredRep z i =
      if (Torus.rep z) i ≤ 1 / 2 then (Torus.rep z) i else (Torus.rep z) i - 1 := rfl
  rw [hc, hz]
  by_cases h : (Torus.rep z) i ≤ 1 / 2
  · simp only [h, ↓reduceIte]
    have : ‖(((Torus.rep z) i : ℝ) : UnitAddCircle)‖ = |(Torus.rep z) i| := by
      rw [AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)]
      rw [abs_of_nonneg hr.1]; norm_num; linarith
    exact this.symm
  · simp only [h, ↓reduceIte]
    have h2 : (((Torus.rep z) i : ℝ) : UnitAddCircle) =
        ((((Torus.rep z) i - 1 : ℝ)) : UnitAddCircle) := by
      have : ((1 : ℝ) : UnitAddCircle) = 0 := AddCircle.coe_period 1
      rw [AddCircle.coe_sub, this, sub_zero]
    rw [h2]
    have : ‖((((Torus.rep z) i - 1 : ℝ)) : UnitAddCircle)‖ = |(Torus.rep z) i - 1| := by
      rw [AddCircle.norm_coe_eq_abs_iff (p := (1 : ℝ)) (by norm_num)]
      rw [abs_le]; constructor <;> norm_num <;> linarith [hr.2]
    exact this.symm

theorem Torus.tdist_eq_sqrt (x y : Torus d) :
    Torus.tdist x y = Real.sqrt (∑ i, ‖x i - y i‖ ^ 2) := by
  unfold Torus.tdist
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, Torus.abs_centeredRep_apply]
  rfl

theorem Torus.continuous_tdist : Continuous fun p : Torus d × Torus d => Torus.tdist p.1 p.2 := by
  simp_rw [Torus.tdist_eq_sqrt]
  fun_prop

theorem Torus.tdist_eq_zero_iff (x y : Torus d) : Torus.tdist x y = 0 ↔ x = y := by
  rw [Torus.tdist_eq_sqrt]
  constructor
  · intro h
    have h1 : ∑ i, ‖x i - y i‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.1 h
    have h2 : ∀ i ∈ Finset.univ, ‖x i - y i‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg _).1
        (le_antisymm h1 (Finset.sum_nonneg fun i _ => sq_nonneg _))
    funext i
    have := h2 i (Finset.mem_univ i)
    exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff (two_ne_zero) |>.1 this))
  · rintro rfl
    simp

theorem Torus.tdist_pos_of_ne {x y : Torus d} (h : x ≠ y) : 0 < Torus.tdist x y :=
  lt_of_le_of_ne (norm_nonneg _) (fun h0 => h ((Torus.tdist_eq_zero_iff x y).1 h0.symm))

theorem Torus.continuous_tdist_comp {α : Type*} [TopologicalSpace α] {f g : α → Torus d}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun a => Torus.tdist (f a) (g a) := by
  have := (Torus.continuous_tdist (d := d)).comp (hf.prodMk hg)
  exact this

theorem isOpen_setOf_mk_ne_zero : IsOpen {x : Euc d | Torus.mk x ≠ 0} :=
  (isClosed_singleton (x := (0 : Torus d))).isOpen_compl.preimage Torus.continuous_mk

/-- The lifted drift in covering-space coordinates:
`b_i(Y) = N⁻¹ ∑_{j≠i} M (lift ∇g)(Y_i - Y_j) - ∇(lift V)(Y_i)`. -/
theorem liftedDrift_apply (D : DynData d) (Y : Fin N → Euc d) (i : Fin N) :
    liftedDrift D Y i = (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
      Torus.matVec D.M (Torus.lift (periodicRieszGrad d D.s) (Y i - Y j)) -
        gradient (Torus.lift D.V) (Y i) := by
  unfold liftedDrift particleDrift
  rw [Torus.grad_mk_aux D.V (Y i)]
  congr 3

theorem mk_sub_ne_zero_of_mem_liftedFree {Y : Fin N → Euc d} (hY : Y ∈ liftedFree d N)
    {i j : Fin N} (hij : i ≠ j) : Torus.mk (Y i - Y j) ≠ 0 := by
  intro h
  apply hY
  refine ⟨i, j, hij, ?_⟩
  rw [mk_sub'] at h
  exact sub_eq_zero.1 h


theorem Torus.rem_tdist_comm (x y : Torus d) : Torus.tdist x y = Torus.tdist y x := by
  rw [Torus.tdist_eq_sqrt, Torus.tdist_eq_sqrt]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [norm_sub_rev]

theorem Torus.rem_tdist_triangle (x y z : Torus d) :
    Torus.tdist x z ≤ Torus.tdist x y + Torus.tdist y z := by
  rw [Torus.tdist_eq_sqrt, Torus.tdist_eq_sqrt, Torus.tdist_eq_sqrt]
  let a : Euc d := WithLp.toLp 2 fun i => ‖x i - y i‖
  let b : Euc d := WithLp.toLp 2 fun i => ‖y i - z i‖
  have ha : ‖a‖ = Real.sqrt (∑ i, ‖x i - y i‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [a]
  have hb : ‖b‖ = Real.sqrt (∑ i, ‖y i - z i‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]; simp [b]
  rw [← ha, ← hb]
  refine le_trans ?_ (norm_add_le a b)
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h1 : ‖x i - z i‖ ≤ ‖x i - y i‖ + ‖y i - z i‖ := by
    calc ‖x i - z i‖ = ‖(x i - y i) + (y i - z i)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have h2 : ‖(a + b) i‖ = ‖x i - y i‖ + ‖y i - z i‖ := by
    simp [a, b]
    positivity
  rw [h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem Torus.rem_tdist_mk_le (a b : Euc d) : Torus.tdist (Torus.mk a) (Torus.mk b) ≤ ‖a - b‖ := by
  rw [Torus.tdist_eq_sqrt, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  have h1 : ‖(Torus.mk a i - Torus.mk b i : UnitAddCircle)‖ ≤ |a i - b i| := by
    have : (Torus.mk a i - Torus.mk b i : UnitAddCircle) = (((a i - b i : ℝ)) : UnitAddCircle) := by
      simp [Torus.mk]
    rw [this]
    have := QuotientAddGroup.norm_mk_le_norm (S := AddSubgroup.zmultiples (1 : ℝ)) (m := a i - b i)
    simpa using this
  have h2 : ‖(a - b) i‖ = |a i - b i| := by simp
  rw [h2]
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

theorem rem_mk_centeredRep_eq (w : Torus d) : Torus.mk (Torus.centeredRep w) = w := by
  funext i
  have hz : w i = (((Torus.rep w) i : ℝ) : UnitAddCircle) := by
    have := congrFun (Torus.mk_rep w) i
    simpa [Torus.mk] using this.symm
  have hc : Torus.centeredRep w i =
      if (Torus.rep w) i ≤ 1 / 2 then (Torus.rep w) i else (Torus.rep w) i - 1 := rfl
  show (((Torus.centeredRep w) i : ℝ) : UnitAddCircle) = w i
  rw [hc, hz]
  split_ifs
  · rfl
  · rw [AddCircle.coe_sub, (AddCircle.coe_period 1 : ((1 : ℝ) : UnitAddCircle) = 0), sub_zero]

theorem rem_centeredRep_eq_of_mk_eq {v : Euc d} {w : Torus d} (hv : Torus.mk v = w)
    (hlt : ∀ a, |v a| < 1 / 2) : Torus.centeredRep w = v := by
  ext a
  have hr : (Torus.rep w) a ∈ Set.Ico (0 : ℝ) 1 := by
    have := (AddCircle.equivIco (1 : ℝ) 0 (w a)).2
    simpa [Torus.rep] using this
  have hz : w a = (((Torus.rep w) a : ℝ) : UnitAddCircle) := by
    have := congrFun (Torus.mk_rep w) a
    simpa [Torus.mk] using this.symm
  have hva : (((v a : ℝ)) : UnitAddCircle) = w a := congrFun hv a
  have h1 : ((v a : ℝ) : UnitAddCircle) = (((Torus.rep w) a : ℝ) : UnitAddCircle) := hva.trans hz
  have h2 := (QuotientAddGroup.eq).mp h1
  rw [AddSubgroup.mem_zmultiples_iff] at h2
  obtain ⟨n, hn⟩ := h2
  simp only [zsmul_eq_mul, mul_one] at hn
  have hc : Torus.centeredRep w a =
      if (Torus.rep w) a ≤ 1 / 2 then (Torus.rep w) a else (Torus.rep w) a - 1 := rfl
  have hva2 := abs_lt.1 (hlt a)
  have hn1 : (-1 : ℝ) < n := by linarith [hr.1]
  have hn2 : (n : ℝ) < 2 := by linarith [hr.2]
  have hn3 : (-1 : ℤ) < n := by exact_mod_cast hn1
  have hn4 : n < 2 := by exact_mod_cast hn2
  have : n = 0 ∨ n = 1 := by omega
  show Torus.centeredRep w a = v a
  rw [hc]
  rcases this with h | h
  · subst h
    have : (Torus.rep w) a = v a := by simp at hn; linarith
    have hle : (Torus.rep w) a ≤ 1 / 2 := by rw [this]; linarith
    simp only [hle, ↓reduceIte]
    exact this
  · subst h
    have : (Torus.rep w) a = v a + 1 := by simp at hn; linarith
    have hle : ¬ (Torus.rep w) a ≤ 1 / 2 := by rw [this]; intro hh; linarith
    simp only [hle, ↓reduceIte]
    rw [this]; ring

theorem rem_mk_geoRep_eq (z : Euc d) : Torus.mk (geoRep z) = Torus.mk z := rem_mk_centeredRep_eq _

theorem rem_geoRep_eq_of_mk_eq {z v : Euc d} (hv : Torus.mk v = Torus.mk z) (hlt : ‖v‖ < 1 / 2) :
    geoRep z = v :=
  rem_centeredRep_eq_of_mk_eq hv fun a => lt_of_le_of_lt (by simpa using PiLp.norm_apply_le v a) hlt

theorem rem_geoRep_neg_of_small {z : Euc d} (h : ‖geoRep z‖ < 1 / 2) : geoRep (-z) = -geoRep z :=
  rem_geoRep_eq_of_mk_eq (by rw [mk_neg_euc, rem_mk_geoRep_eq, mk_neg_euc]) (by rwa [norm_neg])

theorem rem_geoRep_add_of_small {z w : Euc d} (hz : ‖geoRep z‖ < 1 / 4) (hw : ‖geoRep w‖ < 1 / 4) :
    geoRep (z + w) = geoRep z + geoRep w :=
  rem_geoRep_eq_of_mk_eq (by rw [Torus.mk_add, Torus.mk_add, rem_mk_geoRep_eq, rem_mk_geoRep_eq])
    ((norm_add_le _ _).trans_lt (by linarith))

theorem rem_exists_bound_periodic {E' : Type*} [NormedAddCommGroup E'] (F : Euc d → E')
    (S : Set (Euc d)) (hS : IsClosed S) (hSrep : ∀ w ∈ S, Torus.rep (Torus.mk w) ∈ S)
    (hF : ContinuousOn F S)
    (hper : ∀ (w : Euc d) (n : Lattice d), F (w + Lattice.toEuc n) = F w) :
    ∃ B : ℝ, ∀ w ∈ S, ‖F w‖ ≤ B := by
  let Box : Set (Euc d) :=
    (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
  have hBox : IsCompact Box :=
    (isCompact_univ_pi fun _ => isCompact_Icc).image (PiLp.continuous_toLp 2 _)
  obtain ⟨B, hB⟩ := (hBox.inter_right hS).exists_bound_of_continuousOn
    (hF.mono Set.inter_subset_right)
  refine ⟨B, fun w hw => ?_⟩
  obtain ⟨n, hn⟩ := Torus.rep_mk w
  have hmem : Torus.rep (Torus.mk w) ∈ Box := by
    refine ⟨fun a => Torus.rep (Torus.mk w) a, fun a _ => ?_, rfl⟩
    have := (AddCircle.equivIco (1 : ℝ) 0 (Torus.mk w a)).2
    simp only [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  have h1 := hB (Torus.rep (Torus.mk w)) ⟨hmem, hSrep w hw⟩
  rw [hn, hper] at h1
  exact h1

theorem rem_exists_norm_le_of_smooth_zero (r : Torus d → Euc d) (hr : Torus.IsSmooth r)
    (h0 : r 0 = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : Euc d, ‖x‖ ≤ 1 / 8 → ‖r (Torus.mk x)‖ ≤ L * ‖x‖ := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) := hr
  obtain ⟨L, hL⟩ := hc.contDiffOn.exists_lipschitzOnWith (s := Metric.closedBall (0 : Euc d) (1 / 8))
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  refine ⟨L, L.2, fun x hx => ?_⟩
  have h := hL.dist_le_mul x (by simpa using hx) 0 (by simp)
  have e : Torus.lift r 0 = 0 := by
    have : Torus.mk (0 : Euc d) = 0 := by funext i; simp [Torus.mk]
    simp [Torus.lift, this, h0]
  rw [e, dist_zero_right, dist_zero_right] at h
  exact h

theorem rem_exists_fderiv_bound_off_zero {κ : Torus d → Euc d} (hK : Torus.IsSmoothOffZero κ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w : Euc d, ε ≤ Torus.tdist (Torus.mk w) 0 →
      ‖fderiv ℝ (Torus.lift κ) w‖ ≤ L := by
  let S : Set (Euc d) := {w | ε ≤ Torus.tdist (Torus.mk w) 0}
  have hS : IsClosed S := by
    have : Continuous fun w : Euc d => Torus.tdist (Torus.mk w) 0 :=
      Torus.continuous_tdist_comp Torus.continuous_mk continuous_const
    exact isClosed_le continuous_const this
  have hSne : S ⊆ {x : Euc d | Torus.mk x ≠ 0} := by
    intro w hw h0
    have : Torus.tdist (Torus.mk w) 0 = 0 := (Torus.tdist_eq_zero_iff _ _).2 h0
    have hw' : ε ≤ Torus.tdist (Torus.mk w) 0 := hw
    linarith
  have hcont : ContinuousOn (fderiv ℝ (Torus.lift κ)) S :=
    (hK.continuousOn_fderiv_of_isOpen isOpen_setOf_mk_ne_zero (by simp)).mono hSne
  have hper : ∀ (w : Euc d) (n : Lattice d),
      fderiv ℝ (Torus.lift κ) (w + Lattice.toEuc n) = fderiv ℝ (Torus.lift κ) w := by
    intro w n
    have hp : (fun x => Torus.lift κ (x + Lattice.toEuc n)) = Torus.lift κ :=
      funext fun x => Torus.lift_periodic κ x n
    rw [← fderiv_comp_add_right (Lattice.toEuc n) (f := Torus.lift κ) (x := w), hp]
  obtain ⟨B, hB⟩ := rem_exists_bound_periodic _ S hS (fun w hw => by
    show ε ≤ Torus.tdist (Torus.mk (Torus.rep (Torus.mk w))) 0
    rw [Torus.mk_rep]; exact hw) hcont hper
  exact ⟨max B 0, le_max_right _ _, fun w hw => (hB w hw).trans (le_max_left _ _)⟩

theorem rem_exists_lipschitz_of_periodic {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (G : Euc d → E') (hG : ContDiff ℝ 1 G)
    (hper : ∀ (w : Euc d) (n : Lattice d), G (w + Lattice.toEuc n) = G w) :
    ∃ L : ℝ≥0, LipschitzWith L G := by
  have hFper : ∀ (w : Euc d) (n : Lattice d),
      fderiv ℝ G (w + Lattice.toEuc n) = fderiv ℝ G w := by
    intro w n
    have hp : (fun x => G (x + Lattice.toEuc n)) = G := funext fun x => hper x n
    rw [← fderiv_comp_add_right (Lattice.toEuc n) (f := G) (x := w), hp]
  obtain ⟨B, hB⟩ := rem_exists_bound_periodic (fderiv ℝ G) Set.univ isClosed_univ
    (fun _ _ => Set.mem_univ _) (hG.continuous_fderiv one_ne_zero).continuousOn hFper
  refine ⟨⟨max B 0, le_max_right _ _⟩, ?_⟩
  refine lipschitzWith_of_nnnorm_fderiv_le (hG.differentiable one_ne_zero) fun x => ?_
  have := (hB x (Set.mem_univ _)).trans (le_max_left B 0)
  exact_mod_cast this

theorem rem_kernel_lipschitz_off_zero {κ : Torus d → Euc d} (hK : Torus.IsSmoothOffZero κ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (u v y : Euc d), ε ≤ Torus.tdist (Torus.mk u) (Torus.mk y) →
      ‖v - u‖ ≤ ε / 2 →
      ‖Torus.lift κ (v - y) - Torus.lift κ (u - y)‖ ≤ L * ‖v - u‖ := by
  obtain ⟨L, hL0, hL⟩ := rem_exists_fderiv_bound_off_zero hK (half_pos hε)
  refine ⟨L, hL0, fun u v y hu hv => ?_⟩
  let f : Euc d → Euc d := fun z => Torus.lift κ (z + (-y))
  have hf : ∀ z ∈ Metric.closedBall u (ε / 2),
      ε / 2 ≤ Torus.tdist (Torus.mk (z + (-y))) 0 := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1 := Torus.rem_tdist_triangle (Torus.mk u) (Torus.mk z) (Torus.mk y)
    have h2 := Torus.rem_tdist_mk_le u z
    have h3 : Torus.tdist (Torus.mk (z + (-y))) 0 = Torus.tdist (Torus.mk z) (Torus.mk y) := by
      rw [← sub_eq_add_neg, mk_sub']
      unfold Torus.tdist
      rw [sub_zero]
    rw [h3]
    rw [norm_sub_rev] at hz
    linarith
  have hne : ∀ z ∈ Metric.closedBall u (ε / 2), Torus.mk (z + (-y)) ≠ 0 := by
    intro z hz h0
    have := hf z hz
    rw [(Torus.tdist_eq_zero_iff _ _).2 h0] at this
    linarith
  have hdA : ∀ z ∈ Metric.closedBall u (ε / 2), DifferentiableAt ℝ (Torus.lift κ) (z + (-y)) := by
    intro z hz
    exact ((hK.contDiffAt (isOpen_setOf_mk_ne_zero.mem_nhds (hne z hz))).differentiableAt
      (by simp))
  have hdiff : ∀ z ∈ Metric.closedBall u (ε / 2), DifferentiableAt ℝ f z := fun z hz =>
    DifferentiableAt.comp (g := Torus.lift κ) (f := fun z : Euc d => z + (-y)) z (hdA z hz)
      (differentiableAt_id.add_const (-y))
  have hbd : ∀ z ∈ Metric.closedBall u (ε / 2), ‖fderiv ℝ f z‖ ≤ L := by
    intro z hz
    have : fderiv ℝ f z = fderiv ℝ (Torus.lift κ) (z + (-y)) :=
      fderiv_comp_add_right (-y) (f := Torus.lift κ) (x := z)
    rw [this]
    exact hL _ (hf z hz)
  have := (convex_closedBall u (ε / 2)).norm_image_sub_le_of_norm_fderiv_le hdiff hbd
    (Metric.mem_closedBall_self (by linarith)) (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hv)
  simpa [f, sub_eq_add_neg] using this

theorem rem_exists_lipschitz_gradient (V : Torus d → ℝ) (hV : Torus.IsCk 2 V) :
    ∃ L : ℝ≥0, LipschitzWith L (gradient (Torus.lift V)) := by
  have hV' : ContDiff ℝ 2 (Torus.lift V) := hV
  have h1 : ContDiff ℝ 1 (fderiv ℝ (Torus.lift V)) := hV'.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 1 (gradient (Torus.lift V)) := by
    have : gradient (Torus.lift V) =
        (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ (Torus.lift V) := by
      funext x; rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h1
  refine rem_exists_lipschitz_of_periodic _ hg fun w n => ?_
  rw [← Torus.grad_mk_aux, ← Torus.grad_mk_aux, Torus.mk_add, Torus.mk_toEuc, add_zero]

theorem rem_abs_sum_inner_le {ι : Type*} (I : Finset ι) (c : ι → Euc d) (hc : ∑ i ∈ I, c i = 0)
    (F : ι → Euc d) (Fb : Euc d) (T : Euc d →L[ℝ] Euc d) (L : ℝ)
    (hF : ∀ i ∈ I, ‖F i - Fb‖ ≤ L * ‖c i‖) :
    |∑ i ∈ I, inner ℝ ((2 : ℝ) • c i) (T (F i))| ≤ 2 * ‖T‖ * L * ∑ i ∈ I, ‖c i‖ ^ 2 := by
  have h1 : ∑ i ∈ I, inner ℝ ((2 : ℝ) • c i) (T (F i)) =
      ∑ i ∈ I, inner ℝ ((2 : ℝ) • c i) (T (F i - Fb)) := by
    have h2 : ∑ i ∈ I, inner ℝ ((2 : ℝ) • c i) (T Fb) = 0 := by
      rw [← sum_inner, ← Finset.smul_sum, hc]
      simp
    have h3 : ∀ i ∈ I, inner ℝ ((2 : ℝ) • c i) (T (F i)) =
        inner ℝ ((2 : ℝ) • c i) (T (F i - Fb)) + inner ℝ ((2 : ℝ) • c i) (T Fb) := by
      intro i _
      rw [← inner_add_right, ← map_add, sub_add_cancel]
    rw [Finset.sum_congr rfl h3, Finset.sum_add_distrib, h2, add_zero]
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_smul, Real.norm_two]
  have h4 : ‖T (F i - Fb)‖ ≤ ‖T‖ * (L * ‖c i‖) :=
    (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hF i hi) (norm_nonneg _))
  calc 2 * ‖c i‖ * ‖T (F i - Fb)‖ ≤ 2 * ‖c i‖ * (‖T‖ * (L * ‖c i‖)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = 2 * ‖T‖ * L * ‖c i‖ ^ 2 := by ring

theorem rem_cluster_compat {I : Finset (Fin N)} {Y : Fin N → Euc d}
    (hsmall : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < 1 / 8) :
    (∀ i ∈ I, ∀ j ∈ I, geoRep (Y j - Y i) = -geoRep (Y i - Y j)) ∧
    (∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I,
      geoRep (Y i - Y l) = geoRep (Y i - Y j) + geoRep (Y j - Y l)) := by
  refine ⟨fun i hi j hj => ?_, fun i hi j hj l hl => ?_⟩
  · have : Y j - Y i = -(Y i - Y j) := by abel
    rw [this]
    exact rem_geoRep_neg_of_small ((hsmall i hi j hj).trans (by norm_num))
  · have : Y i - Y l = (Y i - Y j) + (Y j - Y l) := by abel
    rw [this]
    exact rem_geoRep_add_of_small ((hsmall i hi j hj).trans (by norm_num))
      ((hsmall j hj l hl).trans (by norm_num))

theorem rem_clusterCentered_of_mem {I : Finset (Fin N)} {Y : Fin N → Euc d} {i : Fin N} (hi : i ∈ I) :
    clusterCentered I Y i = (1 / (I.card : ℝ)) • ∑ j ∈ I, geoRep (Y i - Y j) := by
  simp [clusterCentered, hi]

theorem rem_clusterCentered_sub {I : Finset (Fin N)} {Y : Fin N → Euc d} (hI : I.Nonempty)
    (hc : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I,
      geoRep (Y i - Y l) = geoRep (Y i - Y j) + geoRep (Y j - Y l))
    {i j : Fin N} (hi : i ∈ I) (hj : j ∈ I) :
    clusterCentered I Y i - clusterCentered I Y j = geoRep (Y i - Y j) := by
  rw [rem_clusterCentered_of_mem hi, rem_clusterCentered_of_mem hj, ← smul_sub, ← Finset.sum_sub_distrib]
  have : ∀ l ∈ I, geoRep (Y i - Y l) - geoRep (Y j - Y l) = geoRep (Y i - Y j) := by
    intro l hl
    have := hc i hi j hj l hl
    rw [this]; abel
  rw [Finset.sum_congr rfl this, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have hk : (I.card : ℝ) ≠ 0 := by exact_mod_cast hI.card_pos.ne'
  rw [one_div, inv_mul_cancel₀ hk, one_smul]

theorem rem_clusterCentered_sum {I : Finset (Fin N)} {Y : Fin N → Euc d}
    (hneg : ∀ i ∈ I, ∀ j ∈ I, geoRep (Y j - Y i) = -geoRep (Y i - Y j)) :
    ∑ i ∈ I, clusterCentered I Y i = 0 := by
  have h1 : ∑ i ∈ I, clusterCentered I Y i =
      (1 / (I.card : ℝ)) • ∑ i ∈ I, ∑ j ∈ I, geoRep (Y i - Y j) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i hi => rem_clusterCentered_of_mem hi
  have h2 : ∑ i ∈ I, ∑ j ∈ I, geoRep (Y i - Y j) = 0 := by
    have h3 : ∑ i ∈ I, ∑ j ∈ I, geoRep (Y i - Y j) = -∑ i ∈ I, ∑ j ∈ I, geoRep (Y i - Y j) := by
      conv_lhs => rw [Finset.sum_comm]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i hi => (hneg i hi j hj).symm ▸ by simp
    set S := ∑ i ∈ I, ∑ j ∈ I, geoRep (Y i - Y j) with hSdef
    have h4 : (2 : ℝ) • S = 0 := by
      rw [two_smul]; nth_rewrite 1 [h3]; exact neg_add_cancel _
    exact (smul_eq_zero.1 h4).resolve_left two_ne_zero
  rw [h1, h2, smul_zero]

theorem rem_internal_identity {I : Finset (Fin N)} {Y : Fin N → Euc d} (hI : I.Nonempty)
    (hneg : ∀ i ∈ I, ∀ j ∈ I, geoRep (Y j - Y i) = -geoRep (Y i - Y j))
    (hc : ∀ i ∈ I, ∀ j ∈ I, ∀ l ∈ I,
      geoRep (Y i - Y l) = geoRep (Y i - Y j) + geoRep (Y j - Y l))
    (E : Euc d → Euc d) (hE : ∀ z, E (-z) = -E z) (T : Euc d →L[ℝ] Euc d) :
    ∑ i ∈ I, ∑ j ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i) (T (E (geoRep (Y i - Y j)))) =
      ∑ i ∈ I, ∑ j ∈ I, inner ℝ (geoRep (Y i - Y j)) (T (E (geoRep (Y i - Y j)))) := by
  set c := clusterCentered I Y with hcdef
  set x : Fin N → Fin N → Euc d := fun i j => geoRep (Y i - Y j) with hx
  have hS : ∑ i ∈ I, ∑ j ∈ I, inner ℝ (c j) (T (E (x i j))) =
      -∑ i ∈ I, ∑ j ∈ I, inner ℝ (c i) (T (E (x i j))) := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : x j i = -x i j := hneg i hi j hj
    rw [this, hE, map_neg, inner_neg_right]
  have hsub : ∑ i ∈ I, ∑ j ∈ I, (inner ℝ (c i) (T (E (x i j))) - inner ℝ (c j) (T (E (x i j)))) =
      ∑ i ∈ I, ∑ j ∈ I, inner ℝ (x i j) (T (E (x i j))) := by
    refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    rw [← inner_sub_left, rem_clusterCentered_sub hI hc hi hj]
  rw [← hsub]
  simp only [Finset.sum_sub_distrib, hS]
  simp only [real_inner_smul_left, ← Finset.mul_sum]
  ring

theorem rem_exterior_separation {I : Finset (Fin N)} (hI : I.Nonempty) {Y : Fin N → Euc d}
    {j : Fin N} (hj : j ∉ I) {ε δ : ℝ} (hδ0 : 0 < δ) (hε1 : ε ≤ 1 / 16)
    (hεδ : 4 * ε ^ 2 ≤ δ / 4)
    (hsmall : ∀ a ∈ I, ∀ b ∈ I, ‖geoRep (Y a - Y b)‖ < ε)
    (hQ : clusterDispersionLift I Y < δ / 4)
    (hδ : δ ≤ clusterDispersionLift (insert j I) Y) :
    ∀ a ∈ I, ε ≤ Torus.tdist (Torus.mk (Y a)) (Torus.mk (Y j)) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, ha, hta⟩ := hcon
  set t : Fin N → ℝ := fun b => Torus.tdist (Torus.mk (Y b)) (Torus.mk (Y j)) with ht
  have ht2 : ∀ b ∈ I, t b < 2 * ε := by
    intro b hb
    have h1 := Torus.rem_tdist_triangle (Torus.mk (Y b)) (Torus.mk (Y a)) (Torus.mk (Y j))
    have h2 : Torus.tdist (Torus.mk (Y b)) (Torus.mk (Y a)) = ‖geoRep (Y b - Y a)‖ := by
      unfold Torus.tdist geoRep
      rw [mk_sub']
    have h3 := hsmall b hb a ha
    show Torus.tdist (Torus.mk (Y b)) (Torus.mk (Y j)) < 2 * ε
    linarith
  have ht0 : ∀ b, 0 ≤ t b := fun b => norm_nonneg _
  have hε0 : 0 < ε := by
    have := ht0 a
    linarith
  set k : ℝ := (I.card : ℝ) with hk
  have hk1 : 1 ≤ k := by
    have : (1 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hI.card_pos
    exact this
  -- the double sum over `insert j I`
  set ψ : Fin N → Fin N → ℝ := fun a b => pairDispersion (Torus.mk (Y a) - Torus.mk (Y b)) with hψ
  have hQI : ∑ a ∈ I, ∑ b ∈ I, ψ a b = 2 * k * clusterDispersionLift I Y := by
    have h : clusterDispersionLift I Y = (1 / (2 * k)) * ∑ a ∈ I, ∑ b ∈ I, ψ a b := rfl
    have : (2 * k) ≠ 0 := by positivity
    rw [h]
    field_simp
  have hQ' : clusterDispersionLift (insert j I) Y * (2 * (k + 1)) =
      ψ j j + ∑ b ∈ I, ψ j b + (∑ a ∈ I, ψ a j + ∑ a ∈ I, ∑ b ∈ I, ψ a b) := by
    have h : clusterDispersionLift (insert j I) Y =
        (1 / (2 * (k + 1))) * ∑ a ∈ insert j I, ∑ b ∈ insert j I, ψ a b := by
      unfold clusterDispersionLift clusterDispersion
      rw [Finset.card_insert_of_notMem hj]
      push_cast
      rfl
    rw [h, Finset.sum_insert hj]
    simp only [Finset.sum_insert hj, Finset.sum_add_distrib]
    have : (2 * (k + 1)) ≠ 0 := by positivity
    field_simp
  have hψjj : ψ j j = 0 := by
    have h0 : ‖Torus.centeredRep (Torus.mk (Y j) - Torus.mk (Y j))‖ = 0 := by
      have := (Torus.tdist_eq_zero_iff (Torus.mk (Y j)) (Torus.mk (Y j))).2 rfl
      exact this
    show pairDispersion (Torus.mk (Y j) - Torus.mk (Y j)) = 0
    rw [pairDispersion_eq_sq _ (by rw [h0]; norm_num), h0]; norm_num
  have hψja : ∀ b ∈ I, ψ b j = t b ^ 2 := by
    intro b hb
    have h0 : ‖Torus.centeredRep (Torus.mk (Y b) - Torus.mk (Y j))‖ = t b := rfl
    show pairDispersion (Torus.mk (Y b) - Torus.mk (Y j)) = t b ^ 2
    rw [pairDispersion_eq_sq _ (by rw [h0]; linarith [ht2 b hb]), h0]
  have hψjb : ∀ b ∈ I, ψ j b = t b ^ 2 := by
    intro b hb
    have h0 : ‖Torus.centeredRep (Torus.mk (Y j) - Torus.mk (Y b))‖ = t b := by
      show Torus.tdist (Torus.mk (Y j)) (Torus.mk (Y b)) = _
      exact Torus.rem_tdist_comm _ _
    show pairDispersion (Torus.mk (Y j) - Torus.mk (Y b)) = t b ^ 2
    rw [pairDispersion_eq_sq _ (by rw [h0]; linarith [ht2 b hb]), h0]
  have hsum1 : ∑ b ∈ I, ψ j b ≤ k * (4 * ε ^ 2) := by
    calc ∑ b ∈ I, ψ j b = ∑ b ∈ I, t b ^ 2 := Finset.sum_congr rfl hψjb
      _ ≤ ∑ b ∈ I, 4 * ε ^ 2 := Finset.sum_le_sum fun b hb => by
          have := ht2 b hb
          nlinarith [ht0 b]
      _ = k * (4 * ε ^ 2) := by simp [hk]
  have hsum2 : ∑ b ∈ I, ψ b j ≤ k * (4 * ε ^ 2) := by
    calc ∑ b ∈ I, ψ b j = ∑ b ∈ I, t b ^ 2 := Finset.sum_congr rfl hψja
      _ ≤ ∑ b ∈ I, 4 * ε ^ 2 := Finset.sum_le_sum fun b hb => by
          have := ht2 b hb
          nlinarith [ht0 b]
      _ = k * (4 * ε ^ 2) := by simp [hk]
  have hQ0 : 0 ≤ clusterDispersionLift I Y := clusterDispersion_nonneg I _
  have hmain : clusterDispersionLift (insert j I) Y * (2 * (k + 1)) ≤
      2 * k * (4 * ε ^ 2) + 2 * k * clusterDispersionLift I Y := by
    rw [hQ', hψjj, hQI]; linarith
  have : δ * (2 * (k + 1)) ≤ 2 * k * (4 * ε ^ 2) + 2 * k * clusterDispersionLift I Y :=
    le_trans (mul_le_mul_of_nonneg_right hδ (by positivity)) hmain
  nlinarith

theorem rem_decomp (D : DynData d) {I : Finset (Fin N)} (hI : I.Nonempty)
    {Y : Fin N → Euc d} (hq : clusterDispersionLift I Y < clusterRadius I)
    (r : Torus d → Euc d)
    (hsmall : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < 1 / 8)
    (hloc : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      periodicRieszGrad d D.s (Torus.mk (Y i - Y j)) =
        eucRieszGrad D.s (geoRep (Y i - Y j)) + r (Torus.mk (Y i - Y j))) :
    clusterRemainder D I Y =
      (1 / (N : ℝ)) * ∑ i ∈ I, ∑ j ∈ I.erase i,
        inner ℝ ((2 : ℝ) • clusterCentered I Y i) (Torus.matVec D.M (r (Torus.mk (Y i - Y j)))) +
      (1 / (N : ℝ)) * ∑ i ∈ I, ∑ j ∈ Finset.univ \ I,
        inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j)))) -
      ∑ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i) (gradient (Torus.lift D.V) (Y i)) := by
  obtain ⟨hneg, hcomp⟩ := rem_cluster_compat hsmall
  unfold clusterRemainder clusterGenerator
  rw [cluster_diffusion_term D I Y hq, fderiv_clusterDispersionLift I Y hq (liftedDrift D Y)]
  -- restrict the sum to `I`
  have hzero : ∀ i, i ∉ I → inner ℝ ((2 : ℝ) • clusterCentered I Y i) (liftedDrift D Y i) = 0 := by
    intro i hi
    simp [clusterCentered, hi]
  rw [← Finset.sum_subset (Finset.subset_univ I) (fun i _ hi => hzero i hi)]
  -- the drift of each `i ∈ I`
  have hdrift : ∀ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i) (liftedDrift D Y i) =
      (1 / (N : ℝ)) * (∑ j ∈ I.erase i,
        inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (eucRieszGrad D.s (geoRep (Y i - Y j)))) +
        ∑ j ∈ I.erase i, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (r (Torus.mk (Y i - Y j)))) +
        ∑ j ∈ Finset.univ \ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j))))) -
        inner ℝ ((2 : ℝ) • clusterCentered I Y i) (gradient (Torus.lift D.V) (Y i)) := by
    intro i hi
    rw [liftedDrift_apply, inner_sub_right, inner_smul_right, inner_sum]
    have hset : Finset.univ.erase i = I.erase i ∪ (Finset.univ \ I) := by
      ext j
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, Finset.mem_sdiff,
        true_and]
      constructor
      · intro hj
        by_cases hjI : j ∈ I
        · exact Or.inl ⟨hj, hjI⟩
        · exact Or.inr hjI
      · rintro (⟨hj, _⟩ | hjI)
        · exact hj
        · rintro rfl; exact hjI hi
    have hdisj : Disjoint (I.erase i) (Finset.univ \ I) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      exact (Finset.mem_sdiff.1 hj').2 (Finset.mem_of_mem_erase hj)
    rw [hset, Finset.sum_union hdisj]
    have hsplit : ∀ j ∈ I.erase i,
        inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (Torus.lift (periodicRieszGrad d D.s) (Y i - Y j))) =
        inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (eucRieszGrad D.s (geoRep (Y i - Y j)))) +
        inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (r (Torus.mk (Y i - Y j)))) := by
      intro j hj
      have hji := Finset.mem_erase.1 hj
      show inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j)))) = _
      rw [hloc i hi j hji.2 (Ne.symm hji.1)]
      unfold Torus.matVec
      rw [map_add, inner_add_right]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    rfl
  rw [Finset.sum_congr rfl hdrift]
  have hA : ∑ i ∈ I, ∑ j ∈ I.erase i, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (Torus.matVec D.M (eucRieszGrad D.s (geoRep (Y i - Y j)))) =
      ∑ i ∈ I, ∑ j ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (Torus.matVec D.M (eucRieszGrad D.s (geoRep (Y i - Y j)))) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← Finset.add_sum_erase I _ hi]
    have hx0 : geoRep (Y i - Y i) = 0 := by
      have h := hneg i hi i hi
      have h2 : (2 : ℝ) • geoRep (Y i - Y i) = 0 := by
        rw [two_smul]; nth_rewrite 1 [h]; exact neg_add_cancel _
      exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
    rw [hx0]
    simp [eucRieszGrad, Torus.matVec]
  have hE : ∀ z : Euc d, eucRieszGrad D.s (-z) = -eucRieszGrad D.s z := by
    intro z
    simp [eucRieszGrad, rieszRadial]
  have hint := rem_internal_identity hI hneg hcomp (eucRieszGrad D.s) hE
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M))
  have hinternal : clusterInternal D I Y = (1 / (N : ℝ)) * ∑ i ∈ I, ∑ j ∈ I.erase i,
      inner ℝ ((2 : ℝ) • clusterCentered I Y i)
        (Torus.matVec D.M (eucRieszGrad D.s (geoRep (Y i - Y j)))) := by
    rw [hA]
    unfold clusterInternal
    congr 1
    exact hint.symm
  rw [hinternal]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  ring

theorem rem_bound_internal_remainder (D : DynData d) {I : Finset (Fin N)} {Y : Fin N → Euc d}
    (r : Torus d → Euc d) {Lr : ℝ} (hLr0 : 0 ≤ Lr)
    (hLr : ∀ x : Euc d, ‖x‖ ≤ 1 / 8 → ‖r (Torus.mk x)‖ ≤ Lr * ‖x‖)
    (hsmall : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < 1 / 8)
    (hQ1 : clusterDispersionLift I Y =
      (1 / (2 * (I.card : ℝ))) * ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2)
    (hQ2 : clusterDispersionLift I Y = ∑ i ∈ I, ‖clusterCentered I Y i‖ ^ 2) (hI : I.Nonempty) :
    |∑ i ∈ I, ∑ j ∈ I.erase i, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
        (Torus.matVec D.M (r (Torus.mk (Y i - Y j))))| ≤
      3 * (I.card : ℝ) * ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M)‖ * Lr *
        clusterDispersionLift I Y := by
  set cm := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M) with hcm
  set c := clusterCentered I Y with hc
  set x : Fin N → Fin N → Euc d := fun i j => geoRep (Y i - Y j) with hx
  set k : ℝ := (I.card : ℝ) with hk
  have hk0 : 0 < k := by
    have : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hI.card_pos
    exact this
  have hterm : ∀ i ∈ I, ∀ j ∈ I.erase i,
      |inner ℝ ((2 : ℝ) • c i) (Torus.matVec D.M (r (Torus.mk (Y i - Y j))))| ≤
        ‖cm‖ * Lr * (‖c i‖ ^ 2 + ‖x i j‖ ^ 2) := by
    intro i hi j hj
    have hjI := Finset.mem_of_mem_erase hj
    have hr : ‖r (Torus.mk (Y i - Y j))‖ ≤ Lr * ‖x i j‖ := by
      have := hLr (x i j) (hsmall i hi j hjI).le
      rwa [show Torus.mk (x i j) = Torus.mk (Y i - Y j) from rem_mk_geoRep_eq _] at this
    have h1 : ‖Torus.matVec D.M (r (Torus.mk (Y i - Y j)))‖ ≤ ‖cm‖ * (Lr * ‖x i j‖) :=
      (cm.le_opNorm _).trans (mul_le_mul_of_nonneg_left hr (norm_nonneg _))
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_smul, Real.norm_two]
    calc 2 * ‖c i‖ * ‖Torus.matVec D.M (r (Torus.mk (Y i - Y j)))‖
        ≤ 2 * ‖c i‖ * (‖cm‖ * (Lr * ‖x i j‖)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖cm‖ * Lr * (2 * ‖c i‖ * ‖x i j‖) := by ring
      _ ≤ ‖cm‖ * Lr * (‖c i‖ ^ 2 + ‖x i j‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          nlinarith [sq_nonneg (‖c i‖ - ‖x i j‖)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h2 : ∀ i ∈ I, |∑ j ∈ I.erase i, inner ℝ ((2 : ℝ) • c i)
      (Torus.matVec D.M (r (Torus.mk (Y i - Y j))))| ≤
      ∑ j ∈ I, ‖cm‖ * Lr * (‖c i‖ ^ 2 + ‖x i j‖ ^ 2) := by
    intro i hi
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum (hterm i hi)).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
      (fun j _ _ => by positivity)
  refine (Finset.sum_le_sum h2).trans ?_
  have h3 : ∑ i ∈ I, ∑ j ∈ I, ‖cm‖ * Lr * (‖c i‖ ^ 2 + ‖x i j‖ ^ 2) =
      ‖cm‖ * Lr * (k * ∑ i ∈ I, ‖c i‖ ^ 2 + ∑ i ∈ I, ∑ j ∈ I, ‖x i j‖ ^ 2) := by
    simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hk]
  rw [h3, ← hQ2]
  have h4 : ∑ i ∈ I, ∑ j ∈ I, ‖x i j‖ ^ 2 = 2 * k * clusterDispersionLift I Y := by
    rw [hQ1]; field_simp; rfl
  rw [h4]
  nlinarith [mul_nonneg (norm_nonneg cm) hLr0]


/-- The remainder bound `B:eq:cluster-remainder` (M L11793-11801): for every `δ > 0` there are
`q_{I,δ} ∈ (0, q_I)` and `C_{I,δ}` with `ℛ_I ≥ -C_{I,δ} Q_I` whenever `Q_I < q_{I,δ}`, the
configuration is collision-free, and `Q_{I∪{j}} ≥ δ` for every `j ∉ I`
(`B:eq:larger-cluster-separated`).  For `I = univ` the separation condition is vacuous
(`clusterRemainder_bound_univ`). -/
theorem clusterRemainder_bound (D : DynData d) (hK : KernelLocal d D.s) (hV : Torus.IsCk 2 D.V)
    (I : Finset (Fin N)) (hI : 2 ≤ I.card) (δ : ℝ) (hδ : 0 < δ) :
    ∃ q C : ℝ, 0 < q ∧ q < clusterRadius I ∧ 0 ≤ C ∧
      ∀ Y : Fin N → Euc d, Y ∈ liftedFree d N → clusterDispersionLift I Y < q →
        (∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Y) →
        -C * clusterDispersionLift I Y ≤ clusterRemainder D I Y := by
  have hIne : I.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨r, δK, hδK, hrs, hr0, hloc⟩ := hK.local_sing
  obtain ⟨Lr, hLr0, hLr⟩ := rem_exists_norm_le_of_smooth_zero r hrs hr0
  set k : ℝ := (I.card : ℝ) with hk
  have hk2 : (2 : ℝ) ≤ k := by
    have : (2 : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hI
    exact this
  have hkpos : 0 < k := by linarith
  set ε₀ : ℝ := min (1 / 16) (Real.sqrt δ / 4) with hε₀
  have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  have hε₀pos : 0 < ε₀ := lt_min (by norm_num) (by positivity)
  have hε₀1 : ε₀ ≤ 1 / 16 := min_le_left _ _
  have hε₀δ : 4 * ε₀ ^ 2 ≤ δ / 4 := by
    have h1 : ε₀ ≤ Real.sqrt δ / 4 := min_le_right _ _
    have h2 : ε₀ ^ 2 ≤ (Real.sqrt δ / 4) ^ 2 := pow_le_pow_left₀ hε₀pos.le h1 2
    have h3 : (Real.sqrt δ) ^ 2 = δ := Real.sq_sqrt hδ.le
    have h4 : (Real.sqrt δ / 4) ^ 2 = δ / 16 := by rw [div_pow, h3]; norm_num
    linarith
  obtain ⟨Lg, hLg0, hLg⟩ := rem_kernel_lipschitz_off_zero hK.smoothOffZero hε₀pos
  obtain ⟨LV, hLV⟩ := rem_exists_lipschitz_gradient D.V hV
  set cm := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M) with hcm
  have hradpos : 0 < clusterRadius I := by unfold clusterRadius; positivity
  set q : ℝ := min (min (clusterRadius I / 2) (δK ^ 2 / (2 * k))) (min (ε₀ ^ 2 / (2 * k)) (δ / 4))
    with hq
  have hqpos : 0 < q :=
    lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))
  have hq1 : q ≤ clusterRadius I / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hq2 : q ≤ δK ^ 2 / (2 * k) := (min_le_left _ _).trans (min_le_right _ _)
  have hq3 : q ≤ ε₀ ^ 2 / (2 * k) := (min_le_right _ _).trans (min_le_left _ _)
  have hq4 : q ≤ δ / 4 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨q, (3 * k * ‖cm‖ * Lr) / N + 2 * ‖cm‖ * Lg + 2 * (LV : ℝ), hqpos, by linarith, ?_, ?_⟩
  · positivity
  intro Y hY hQ hsep
  set Q := clusterDispersionLift I Y with hQdef
  have hQrad : Q < clusterRadius I := by linarith
  obtain ⟨hsmall, hQ1', hQ2'⟩ := clusterDispersionLift_eq_euclid I Y hQrad
  have hQ1 : Q = (1 / (2 * k)) * ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 := hQ1'
  have hQ2 : Q = ∑ i ∈ I, ‖clusterCentered I Y i‖ ^ 2 := hQ2'
  have hQnn : 0 ≤ Q := clusterDispersion_nonneg I (fun i => Torus.mk (Y i))
  have h2k : 0 < 2 * k := by positivity
  have hS : ∑ i ∈ I, ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 = 2 * k * Q := by
    rw [hQ1]; field_simp
  have hxsq : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2 ≤ 2 * k * Q := by
    intro i hi j hj
    rw [← hS]
    refine le_trans (Finset.single_le_sum (f := fun j => ‖geoRep (Y i - Y j)‖ ^ 2)
      (fun j _ => by positivity) hj) ?_
    exact Finset.single_le_sum (f := fun i => ∑ j ∈ I, ‖geoRep (Y i - Y j)‖ ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => by positivity) hi
  have hcsq : ∀ i ∈ I, ‖clusterCentered I Y i‖ ^ 2 ≤ Q := by
    intro i hi
    rw [hQ2]
    exact Finset.single_le_sum (f := fun i => ‖clusterCentered I Y i‖ ^ 2)
      (fun i _ => by positivity) hi
  have e1 : 2 * k * q ≤ δK ^ 2 := by
    have := (le_div_iff₀ h2k).1 hq2; linarith
  have e2 : 2 * k * q ≤ ε₀ ^ 2 := by
    have := (le_div_iff₀ h2k).1 hq3; linarith
  have hxlt : ∀ i ∈ I, ∀ j ∈ I, ‖geoRep (Y i - Y j)‖ < δK ∧ ‖geoRep (Y i - Y j)‖ < ε₀ := by
    intro i hi j hj
    have h := hxsq i hi j hj
    have h3 : 2 * k * Q < 2 * k * q := mul_lt_mul_of_pos_left hQ h2k
    constructor
    · by_contra hc
      push Not at hc
      linarith [pow_le_pow_left₀ hδK.le hc 2]
    · by_contra hc
      push Not at hc
      linarith [pow_le_pow_left₀ hε₀pos.le hc 2]
  have hclt : ∀ i ∈ I, ‖clusterCentered I Y i‖ ≤ ε₀ / 2 := by
    intro i hi
    have h := hcsq i hi
    by_contra hc
    push Not at hc
    have h4 : q ≤ ε₀ ^ 2 / 4 := by
      refine hq3.trans ?_
      rw [div_le_div_iff₀ h2k (by norm_num)]
      exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg ε₀)
    linarith [pow_le_pow_left₀ (by positivity : 0 ≤ ε₀ / 2) hc.le 2]
  have hIne' : I.Nonempty := hIne
  obtain ⟨hneg, hcomp⟩ := rem_cluster_compat hsmall
  have hsumc := rem_clusterCentered_sum (I := I) (Y := Y) hneg
  have hlocI : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      periodicRieszGrad d D.s (Torus.mk (Y i - Y j)) =
        eucRieszGrad D.s (geoRep (Y i - Y j)) + r (Torus.mk (Y i - Y j)) := by
    intro i hi j hj hij
    have hne : geoRep (Y i - Y j) ≠ 0 := by
      intro h0
      apply mk_sub_ne_zero_of_mem_liftedFree hY hij
      rw [← rem_mk_geoRep_eq, h0]
      funext a; simp [Torus.mk]
    have := hloc _ (hxlt i hi j hj).1 hne
    rwa [rem_mk_geoRep_eq] at this
  have hdec := rem_decomp D hIne' hQrad r hsmall hlocI
  rw [hdec]
  -- compatible lifts
  obtain ⟨i₀, hi₀⟩ := hIne
  set ytil : Fin N → Euc d := fun i => Y i₀ - geoRep (Y i₀ - Y i) with hytil
  have hytil_mk : ∀ i, Torus.mk (ytil i) = Torus.mk (Y i) := by
    intro i
    simp only [hytil]
    rw [mk_sub', rem_mk_geoRep_eq, mk_sub']
    abel
  have hytil_sub : ∀ i ∈ I, ∀ l ∈ I, ytil i - ytil l = geoRep (Y i - Y l) := by
    intro i hi l hl
    have := hcomp i₀ hi₀ i hi l hl
    simp only [hytil]
    rw [this]
    abel
  set ybar : Euc d := (1 / k) • ∑ l ∈ I, ytil l with hybar
  have hyc : ∀ i ∈ I, ytil i - ybar = clusterCentered I Y i := by
    intro i hi
    rw [rem_clusterCentered_of_mem hi]
    have h1 : ∑ l ∈ I, geoRep (Y i - Y l) = ∑ l ∈ I, (ytil i - ytil l) :=
      Finset.sum_congr rfl fun l hl => (hytil_sub i hi l hl).symm
    rw [h1, Finset.sum_sub_distrib, Finset.sum_const, hybar, smul_sub, ← Nat.cast_smul_eq_nsmul ℝ,
      smul_smul, one_div, inv_mul_cancel₀ hkpos.ne', one_smul]
  have hc_norm : ∀ i ∈ I, ‖ybar - ytil i‖ = ‖clusterCentered I Y i‖ := by
    intro i hi; rw [norm_sub_rev, hyc i hi]
  have hNk : k ≤ (N : ℝ) := by
    have h : I.card ≤ N := by simpa using Finset.card_le_univ I
    have h' : (I.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    exact h'
  have hNpos : 0 < (N : ℝ) := by linarith
  -- (1) the smooth part of the internal force
  have hAr := rem_bound_internal_remainder D r hLr0 hLr hsmall hQ1' hQ2' hIne'
  -- (2) the exterior forces
  have hB : ∀ j ∈ Finset.univ \ I, |∑ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j))))| ≤
      2 * ‖cm‖ * Lg * Q := by
    intro j hj
    have hjI : j ∉ I := (Finset.mem_sdiff.1 hj).2
    have hsepj := rem_exterior_separation hIne' hjI hδ hε₀1 hε₀δ
      (fun a ha b hb => (hxlt a ha b hb).2) (by linarith) (hsep j hjI)
    have hF : ∀ i ∈ I, ‖Torus.lift (periodicRieszGrad d D.s) (ytil i - Y j) -
        Torus.lift (periodicRieszGrad d D.s) (ybar - Y j)‖ ≤ Lg * ‖clusterCentered I Y i‖ := by
      intro i hi
      have hu : ε₀ ≤ Torus.tdist (Torus.mk (ytil i)) (Torus.mk (Y j)) := by
        rw [hytil_mk]; exact hsepj i hi
      have hv : ‖ybar - ytil i‖ ≤ ε₀ / 2 := by rw [hc_norm i hi]; exact hclt i hi
      have := hLg (ytil i) ybar (Y j) hu hv
      rw [norm_sub_rev, hc_norm i hi] at this
      exact this
    have key := rem_abs_sum_inner_le I (clusterCentered I Y) hsumc
      (fun i => Torus.lift (periodicRieszGrad d D.s) (ytil i - Y j))
      (Torus.lift (periodicRieszGrad d D.s) (ybar - Y j)) cm Lg hF
    have hF_eq : ∀ i, Torus.lift (periodicRieszGrad d D.s) (ytil i - Y j) =
        periodicRieszGrad d D.s (Torus.mk (Y i - Y j)) := by
      intro i
      show periodicRieszGrad d D.s (Torus.mk (ytil i - Y j)) = _
      rw [mk_sub', hytil_mk, ← mk_sub']
    simp only [hF_eq] at key
    rw [← hQ2] at key
    exact key
  have hBtot : |(1 / (N : ℝ)) * ∑ i ∈ I, ∑ j ∈ Finset.univ \ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j))))| ≤
      2 * ‖cm‖ * Lg * Q := by
    rw [Finset.sum_comm, abs_mul, abs_of_pos (by positivity : 0 < 1 / (N : ℝ))]
    have h1 := (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hB)
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    have hcard : ((Finset.univ \ I).card : ℝ) ≤ N := by
      have : (Finset.univ \ I).card ≤ N := by simpa using Finset.card_le_univ (Finset.univ \ I)
      exact_mod_cast this
    have h2 : 0 ≤ 2 * ‖cm‖ * Lg * Q := by positivity
    calc 1 / (N : ℝ) * |∑ j ∈ Finset.univ \ I, ∑ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
          (Torus.matVec D.M (periodicRieszGrad d D.s (Torus.mk (Y i - Y j))))|
        ≤ 1 / (N : ℝ) * (((Finset.univ \ I).card : ℝ) * (2 * ‖cm‖ * Lg * Q)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 1 / (N : ℝ) * ((N : ℝ) * (2 * ‖cm‖ * Lg * Q)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard h2) (by positivity)
      _ = 2 * ‖cm‖ * Lg * Q := by
          rw [← mul_assoc, one_div, inv_mul_cancel₀ hNpos.ne', one_mul]
  -- (3) the confinement
  have hVF : ∀ i ∈ I, ‖gradient (Torus.lift D.V) (ytil i) - gradient (Torus.lift D.V) ybar‖ ≤
      (LV : ℝ) * ‖clusterCentered I Y i‖ := by
    intro i hi
    have := hLV.dist_le_mul (ytil i) ybar
    rw [dist_eq_norm, dist_eq_norm, hyc i hi] at this
    exact this
  have hVkey := rem_abs_sum_inner_le I (clusterCentered I Y) hsumc
    (fun i => gradient (Torus.lift D.V) (ytil i)) (gradient (Torus.lift D.V) ybar)
    (ContinuousLinearMap.id ℝ (Euc d)) (LV : ℝ) hVF
  have hVeq : ∀ i, gradient (Torus.lift D.V) (ytil i) = gradient (Torus.lift D.V) (Y i) := by
    intro i
    rw [← Torus.grad_mk_aux, hytil_mk, Torus.grad_mk_aux]
  simp only [hVeq, ContinuousLinearMap.id_apply] at hVkey
  rw [← hQ2] at hVkey
  have hidn : ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hVkey' : |∑ i ∈ I, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (gradient (Torus.lift D.V) (Y i))| ≤ 2 * (LV : ℝ) * Q := by
    refine hVkey.trans ?_
    have h0 : 0 ≤ 2 * (LV : ℝ) * Q := by positivity
    have e : 2 * ‖ContinuousLinearMap.id ℝ (Euc d)‖ * (LV : ℝ) * Q =
        ‖ContinuousLinearMap.id ℝ (Euc d)‖ * (2 * (LV : ℝ) * Q) := by ring
    rw [e]
    calc _ ≤ 1 * (2 * (LV : ℝ) * Q) := mul_le_mul_of_nonneg_right hidn h0
      _ = _ := one_mul _
  -- assemble
  have hArN : |(1 / (N : ℝ)) * ∑ i ∈ I, ∑ j ∈ I.erase i, inner ℝ ((2 : ℝ) • clusterCentered I Y i)
      (Torus.matVec D.M (r (Torus.mk (Y i - Y j))))| ≤ (3 * k * ‖cm‖ * Lr) / N * Q := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / (N : ℝ))]
    calc 1 / (N : ℝ) * _ ≤ 1 / (N : ℝ) * (3 * k * ‖cm‖ * Lr * Q) :=
          mul_le_mul_of_nonneg_left hAr (by positivity)
      _ = (3 * k * ‖cm‖ * Lr) / N * Q := by ring
  have h1 := abs_le.1 hArN
  have h2 := abs_le.1 hBtot
  have h3 := abs_le.1 hVkey'
  have e : -((3 * k * ‖cm‖ * Lr) / N + 2 * ‖cm‖ * Lg + 2 * (LV : ℝ)) * Q =
      -((3 * k * ‖cm‖ * Lr) / N * Q) - 2 * ‖cm‖ * Lg * Q - 2 * (LV : ℝ) * Q := by ring
  rw [e]
  linarith [h1.1, h2.1, h3.2]

/-- The remainder bound for the full cluster `I = univ` (M L11801: the condition
`B:eq:larger-cluster-separated` is empty and the constant is independent of `δ`). -/
theorem clusterRemainder_bound_univ (D : DynData d) (hK : KernelLocal d D.s)
    (hV : Torus.IsCk 2 D.V) (hN : 2 ≤ N) :
    ∃ q C : ℝ, 0 < q ∧ q < clusterRadius (Finset.univ : Finset (Fin N)) ∧ 0 ≤ C ∧
      ∀ Y : Fin N → Euc d, Y ∈ liftedFree d N →
        clusterDispersionLift Finset.univ Y < q →
        -C * clusterDispersionLift Finset.univ Y ≤ clusterRemainder D Finset.univ Y := by
  obtain ⟨q, C, hq, hqr, hC, h⟩ := clusterRemainder_bound D hK hV (Finset.univ : Finset (Fin N))
    (by simpa using hN) 1 one_pos
  refine ⟨q, C, hq, hqr, hC, fun Y hY hQ => h Y hY hQ ?_⟩
  intro j hj
  exact absurd (Finset.mem_univ j) hj

/-! ### Regularity of the lifted drift -/

/-- `Torus.grad φ (mk y) = gradient (lift φ) y`: the gradient of the lift is `ℤ^d`-periodic. -/
theorem Torus.grad_mk (φ : Torus d → ℝ) (hφ : Torus.IsCk 1 φ) (y : Euc d) :
    Torus.grad φ (Torus.mk y) = gradient (Torus.lift φ) y :=
  Torus.grad_mk_aux φ y

/-- The lifted drift is `C¹` on the (open) collision-free region. -/
theorem contDiffOn_liftedDrift (D : DynData d)
    (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s)) (hV : Torus.IsCk 2 D.V) :
    ContDiffOn ℝ 1 (liftedDrift (N := N) D) (liftedFree d N) := by
  have hK1 : ContDiffOn ℝ 1 (Torus.lift (periodicRieszGrad d D.s)) {x : Euc d | Torus.mk x ≠ 0} :=
    hK.of_le (by exact_mod_cast le_top)
  have hMv : ContDiff ℝ 1 (Torus.matVec D.M) :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin D.M)).contDiff
  have hV1 : ContDiff ℝ 1 (gradient (Torus.lift D.V)) := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ (Torus.lift D.V)) := hV.fderiv_right (by norm_num)
    have : gradient (Torus.lift D.V) =
        (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ (Torus.lift D.V) := by
      funext x; rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp h1
  refine contDiffOn_pi.2 fun i => ?_
  have e : (fun Y : Fin N → Euc d => liftedDrift D Y i) = fun Y =>
      (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        Torus.matVec D.M (Torus.lift (periodicRieszGrad d D.s) (Y i - Y j)) -
          gradient (Torus.lift D.V) (Y i) := funext fun Y => liftedDrift_apply D Y i
  show ContDiffOn ℝ 1 (fun Y : Fin N → Euc d => liftedDrift D Y i) (liftedFree d N)
  rw [e]
  refine ContDiffOn.sub (ContDiffOn.const_smul _ (ContDiffOn.sum fun j hj => ?_)) ?_
  · have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    refine hMv.comp_contDiffOn (hK1.comp (f := fun Y : Fin N → Euc d => Y i - Y j) ?_ ?_)
    · exact ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffOn
    · intro Y hY
      exact mk_sub_ne_zero_of_mem_liftedFree hY hij
  · exact (hV1.comp (contDiff_apply ℝ (Euc d) i)).contDiffOn

/-- The lifted drift is continuous and locally Lipschitz on the collision-free region, from the
smoothness of `∇g` off the origin and `V ∈ C²` (M L11750: "the original, locally Lipschitz
drift on `(ℝ^d)^N ∖ 𝔇_N`"; L11997).  This is the analytic input of
`pathwiseUnique_of_locLipschitz` and `exists_sde_solution_maximal`. -/
theorem liftedDrift_locLipschitz (D : DynData d)
    (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s)) (hV : Torus.IsCk 2 D.V) :
    IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) := by
  have hC := contDiffOn_liftedDrift (N := N) D hK hV
  refine ⟨?_, fun K hKc hKU T => ?_⟩
  · exact hC.continuousOn.comp continuousOn_snd (fun p hp => hp.2)
  · have hloc : LocallyLipschitzOn K (liftedDrift (N := N) D) := by
      intro x hx
      obtain ⟨L, t, ht, hL⟩ := ((hC x (hKU hx)).contDiffAt
        ((isOpen_liftedFree d N).mem_nhds (hKU hx))).exists_lipschitzOnWith
      exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
    obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hKc
    exact ⟨L, fun _ _ => hL⟩

/-! ### The maximal solution and the collision alternative (Lemma `B:lem:particle-maximal`) -/

section Probabilistic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The output of `exists_sde_solution_maximal` for the lifted particle SDE on `liftedFree d N`:
a stopping time `τ > 0`, a strong solution on `[0, τ)` with values in the collision-free region,
leaving every compact subset of the region as `t ↑ τ` on `{τ < ∞}`.  This is the source's
maximal solution `(X_N, τ_⋆)` of Lemma `B:lem:particle-maximal` (M L11731-11737), lifted. -/
structure IsMaximalParticleSolution (P : Measure Ω) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (D : DynData d) (Y₀ : Ω → (Fin N → Euc d))
    (τ : Ω → WithTop ℝ) (Y : ℝ → Ω → (Fin N → Euc d)) : Prop where
  init_meas : ∀ t : ℝ, Measurable[ℱ t] Y₀
  stopping : IsStoppingTime ℱ τ
  pos : ∀ ω, 0 < τ ω
  sol : IsAdditiveSDESolution P ℱ W' (fun _ Z => liftedDrift D Z) (liftedNoise D) Y₀ τ Y
  mem : ∀ ω, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ ω → Y t ω ∈ liftedFree d N
  exit : ∀ ω, τ ω < ⊤ → ∀ K : Set (Fin N → Euc d), IsCompact K → K ⊆ liftedFree d N →
    ∀ t₀ : ℝ, (t₀ : WithTop ℝ) < τ ω →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ω ∧ Y t ω ∉ K

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

/-- Lemma `B:lem:particle-maximal` (M L11731-11737), existence and uniqueness part: for every
Brownian filtration and every adapted collision-free initial lift there is a maximal strong
solution, which dominates and extends every other collision-free strong solution.  Reduces to
`exists_sde_solution_maximal` and `sde_pathwise_unique` on `liftedFree d N` with
`liftedDrift_locLipschitz`; the source's truncation route (L11740-11756) is not needed. -/
theorem particle_maximal [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W') (Y₀ : Ω → (Fin N → Euc d))
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) (hY₀U : ∀ ω, Y₀ ω ∈ liftedFree d N) :
    ∃ (τ : Ω → WithTop ℝ) (Y : ℝ → Ω → (Fin N → Euc d)),
      IsMaximalParticleSolution P ℱ W' D Y₀ τ Y ∧
      ∀ (τ' : Ω → WithTop ℝ) (Y' : ℝ → Ω → (Fin N → Euc d)),
        IsAdditiveSDESolution P ℱ W' (fun _ Z => liftedDrift D Z) (liftedNoise D) Y₀ τ' Y' →
        (∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ' ω → Y' t ω ∈ liftedFree d N) →
        ∀ᵐ ω ∂P, τ' ω ≤ τ ω ∧ ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ' ω → Y' t ω = Y t ω := by
  have hb := liftedDrift_locLipschitz (N := N) D hK.smoothOffZero hV
  obtain ⟨τ, Y, hstop, hpos, hsol, hmem, hexit, hmax⟩ := exists_sde_solution_maximal hW'
    (liftedFree d N) (isOpen_liftedFree d N) (fun _ Z => liftedDrift D Z) hb (liftedNoise D) Y₀
    hY₀ hY₀U
  refine ⟨τ, Y, ⟨hY₀, hstop, hpos, hsol, hmem, hexit⟩, fun τ' Y' hsol' hmem' => ?_⟩
  have hle := hmax τ' Y' hsol' hmem'
  have huniq := sde_pathwise_unique hW' (liftedFree d N) (isOpen_liftedFree d N)
    (fun _ Z => liftedDrift D Z) hb (liftedNoise D) Y₀ hsol hsol'
    (Eventually.of_forall hmem) hmem'
  filter_upwards [hle, huniq] with ω h1 h2
  exact ⟨h1, fun t ht htlt => (h2 t ht (lt_min (lt_of_lt_of_le htlt h1) htlt)).symm⟩

/-- A configuration whose pair distances are all `≥ ε > 0` is collision-free. -/
theorem mem_liftedFree_of_sep {ε : ℝ} (hε : 0 < ε) {Z : Fin N → Euc d}
    (hZ : ∀ i j : Fin N, i ≠ j → ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))) :
    Z ∈ liftedFree d N := by
  rintro ⟨i, j, hij, h⟩
  have := hZ i j hij
  have h' : Torus.mk (Z i) = Torus.mk (Z j) := h
  rw [h', (Torus.tdist_eq_zero_iff _ _).2 rfl] at this
  linarith

theorem isClosed_sepSet (d N : ℕ) (ε : ℝ) :
    IsClosed {Z : Fin N → Euc d | ∀ i j : Fin N, i ≠ j →
      ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))} := by
  have e : {Z : Fin N → Euc d | ∀ i j : Fin N, i ≠ j →
      ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))} = ⋂ i, ⋂ j, ⋂ (_ : i ≠ j),
      {Z : Fin N → Euc d | ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))} := by
    ext Z; simp only [Set.mem_iInter, Set.mem_ofPred_eq]
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
  have h1 : Continuous fun Z : Fin N → Euc d => Torus.mk (Z i) :=
    Torus.continuous_mk.comp (continuous_apply i)
  have h2 : Continuous fun Z : Fin N → Euc d => Torus.mk (Z j) :=
    Torus.continuous_mk.comp (continuous_apply j)
  exact isClosed_le continuous_const (Torus.continuous_tdist_comp h1 h2)

/-- The lifted drift is bounded on `ε`-separated configurations (periodicity reduces to a
compact fundamental box). -/
theorem liftedDrift_bounded_of_sep (D : DynData d)
    (hK : Torus.IsSmoothOffZero (periodicRieszGrad d D.s)) (hV : Torus.IsCk 2 D.V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : ℝ, ∀ Z : Fin N → Euc d,
      (∀ i j : Fin N, i ≠ j → ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))) →
        ‖liftedDrift D Z‖ ≤ B := by
  let Box : Set (Fin N → Euc d) :=
    Set.pi Set.univ fun _ => (WithLp.toLp 2) '' (Set.pi Set.univ fun _ : Fin d => Set.Icc (0 : ℝ) 1)
  have hBox : IsCompact Box :=
    isCompact_univ_pi fun _ => (isCompact_univ_pi fun _ => isCompact_Icc).image
      (PiLp.continuous_toLp 2 _)
  have hF : IsCompact (Box ∩ {Z : Fin N → Euc d | ∀ i j : Fin N, i ≠ j →
      ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))}) :=
    hBox.inter_right (isClosed_sepSet d N ε)
  have hcont : ContinuousOn (liftedDrift (N := N) D) (Box ∩ {Z : Fin N → Euc d | ∀ i j : Fin N,
      i ≠ j → ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))}) :=
    (contDiffOn_liftedDrift D hK hV).continuousOn.mono fun Z hZ => mem_liftedFree_of_sep hε hZ.2
  obtain ⟨B, hB⟩ := hF.exists_bound_of_continuousOn hcont
  refine ⟨B, fun Z hZ => ?_⟩
  let Z' : Fin N → Euc d := fun i => Torus.rep (Torus.mk (Z i))
  have hmk : (fun i => Torus.mk (Z' i)) = fun i => Torus.mk (Z i) :=
    funext fun i => Torus.mk_rep _
  have hdr : liftedDrift D Z = liftedDrift D Z' := by
    unfold liftedDrift
    rw [hmk]
  rw [hdr]
  refine hB Z' ⟨?_, ?_⟩
  · intro i _
    refine ⟨fun a => Torus.rep (Torus.mk (Z i)) a, fun a _ => ?_, rfl⟩
    have := (AddCircle.equivIco (1 : ℝ) 0 (Torus.mk (Z i) a)).2
    simp only [zero_add] at this
    exact ⟨this.1, this.2.le⟩
  · intro i j hij
    have := hZ i j hij
    have e : Torus.mk (Z' i) = Torus.mk (Z i) := congrFun hmk i
    have e' : Torus.mk (Z' j) = Torus.mk (Z j) := congrFun hmk j
    rw [e, e']
    exact this

/-- The collision alternative `B:eq:particle-collision-alternative` (M L11734): on `{τ < ∞}`,
`liminf_{t↑τ} min_{i<j} dist(x_i^t, x_j^t) = 0`.  From the exit property: if the pair distances
stayed `≥ ε` on `[t₀, τ)`, the drift would be bounded there and the path would stay in a compact
subset of `liftedFree d N` (bounded in the covering space by the integrated equation and the
continuity of the noise), contradicting `exit`. -/
theorem IsMaximalParticleSolution.collision_alternative [IsProbabilityMeasure P] (D : DynData d)
    (hK : KernelLocal d D.s) (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) :
    ∀ᵐ ω ∂P, τ ω < ⊤ → ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℝ, 0 ≤ t₀ → (t₀ : WithTop ℝ) < τ ω →
      ∃ t : ℝ, t₀ < t ∧ (t : WithTop ℝ) < τ ω ∧
        ∃ i j : Fin N, i ≠ j ∧ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < ε := by
  filter_upwards [hsol.sol.eq] with ω hω hτ ε hε t₀ ht₀ ht₀τ
  by_contra hcon
  have hsep : ∀ t : ℝ, t₀ < t → (t : WithTop ℝ) < τ ω → ∀ i j : Fin N, i ≠ j →
      ε ≤ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) := by
    intro t ht htτ i j hij
    by_contra h
    exact hcon ⟨t, ht, htτ, i, j, hij, not_le.1 h⟩
  obtain ⟨T₁, hT₁⟩ := WithTop.ne_top_iff_exists.1 hτ.ne
  have hlt : ∀ t : ℝ, (t : WithTop ℝ) < τ ω → t < T₁ := fun t ht => by
    rw [← hT₁] at ht
    exact_mod_cast ht
  have ht₀T : t₀ < T₁ := hlt t₀ ht₀τ
  obtain ⟨B, hB⟩ := liftedDrift_bounded_of_sep (N := N) D hK.smoothOffZero hV hε
  -- bound on `[0, t₀]`
  obtain ⟨R₁, hR₁⟩ := (isCompact_Icc.image_of_continuousOn
    (hsol.sol.cont ω t₀ ht₀ ht₀τ)).isBounded.exists_norm_le
  have hY₁ : ‖Y t₀ ω‖ ≤ R₁ := hR₁ _ ⟨t₀, ⟨ht₀, le_rfl⟩, rfl⟩
  -- bound on the noise
  have hNc : Continuous (addNoise (liftedNoise (N := N) D) fun s => W' s ω) :=
    continuous_addNoise _ (hW'.cont ω)
  obtain ⟨R₂, hR₂⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T₁)).exists_bound_of_continuousOn
    hNc.continuousOn
  -- the path stays in a ball
  have hbound : ∀ t : ℝ, t₀ < t → (t : WithTop ℝ) < τ ω →
      ‖Y t ω‖ ≤ R₁ + |B| * |T₁| + 2 * R₂ := by
    intro t ht htτ
    have htT := hlt t htτ
    have ht0 : 0 ≤ t := ht₀.trans ht.le
    obtain ⟨hi₀, he₀⟩ := hω t₀ ht₀ ht₀τ
    obtain ⟨hi, he⟩ := hω t ht0 htτ
    have hii₀ : IntervalIntegrable (fun s => liftedDrift D (Y s ω)) volume 0 t₀ :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht₀).2 hi₀
    have hii : IntervalIntegrable (fun s => liftedDrift D (Y s ω)) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht0).2 hi
    have hI : ∀ u : ℝ, 0 ≤ u → ∫ s in Set.Icc 0 u, liftedDrift D (Y s ω) =
        ∫ s in (0 : ℝ)..u, liftedDrift D (Y s ω) := fun u hu => by
      rw [intervalIntegral.integral_of_le hu, integral_Icc_eq_integral_Ioc]
    have hdiff : ∫ s in t₀..t, liftedDrift D (Y s ω) =
        (∫ s in Set.Icc 0 t, liftedDrift D (Y s ω)) -
          ∫ s in Set.Icc 0 t₀, liftedDrift D (Y s ω) := by
      rw [hI t ht0, hI t₀ ht₀, intervalIntegral.integral_interval_sub_left hii hii₀]
    have hint : ‖∫ s in t₀..t, liftedDrift D (Y s ω)‖ ≤ B * |t - t₀| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
      rw [Set.uIoc_of_le ht.le] at hs
      exact hB _ (hsep s hs.1 (by
        rw [← hT₁]; exact_mod_cast lt_of_le_of_lt hs.2 htT))
    have hnt := hR₂ t ⟨ht0, htT.le⟩
    have hnt₀ := hR₂ t₀ ⟨ht₀, ht₀T.le⟩
    have hNN : ∀ u : ℝ, ∑ k, ofNNRealTime W' u ω k • liftedNoise (N := N) D k =
        addNoise (liftedNoise (N := N) D) (fun s => W' s ω) u := fun u => rfl
    rw [hNN] at he he₀
    have hYt : Y t ω = Y t₀ ω + (∫ s in t₀..t, liftedDrift D (Y s ω)) +
        (addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t -
          addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t₀) := by
      rw [hdiff, he, he₀]
      abel
    have habs : |t - t₀| ≤ |T₁| := by
      rw [abs_of_nonneg (by linarith)]
      exact (by linarith : t - t₀ ≤ T₁).trans (le_abs_self T₁)
    have hBt : B * |t - t₀| ≤ |B| * |T₁| :=
      (mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left habs (abs_nonneg _))
    rw [hYt]
    have h1 := norm_add_le (Y t₀ ω + ∫ s in t₀..t, liftedDrift D (Y s ω))
      (addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t -
        addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t₀)
    have h2 := norm_add_le (Y t₀ ω) (∫ s in t₀..t, liftedDrift D (Y s ω))
    have h3 := norm_sub_le (addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t)
      (addNoise (liftedNoise (N := N) D) (fun s => W' s ω) t₀)
    linarith
  -- the compact set
  set R := R₁ + |B| * |T₁| + 2 * R₂ with hR
  let K : Set (Fin N → Euc d) := Metric.closedBall 0 R ∩ {Z : Fin N → Euc d | ∀ i j : Fin N,
    i ≠ j → ε ≤ Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j))}
  have hKc : IsCompact K := (isCompact_closedBall _ _).inter_right (isClosed_sepSet d N ε)
  have hKU : K ⊆ liftedFree d N := fun Z hZ => mem_liftedFree_of_sep hε hZ.2
  obtain ⟨t, ht, htτ, hnot⟩ := hsol.exit ω hτ K hKc hKU t₀ ht₀τ
  refine hnot ⟨?_, hsep t ht htτ⟩
  rw [mem_closedBall_zero_iff]
  exact hbound t ht htτ

/-! ### The Itô equation for `Q_I` along the maximal solution (Lemma `B:lem:cluster-ito`) -/

/-- The martingale integrand `k ↦ D Q_I(Y_s)[σ_k]` of `B:eq:cluster-ito`. -/
def clusterNoiseIntegrand (D : DynData d) (I : Finset (Fin N)) (Y : ℝ → Ω → (Fin N → Euc d)) :
    ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun s ω k => fderiv ℝ (clusterDispersionLift I) (Y s ω) (liftedNoise D k)

/-! ### The logarithmic barrier (Lemma `B:lem:cluster-barrier`, M L11849-11910) -/

/-- The event `inf_{0 ≤ t < T ∧ τ} Q_I(X_t) = 0` of `B:eq:larger-cluster-induction-hypothesis`
(M L11852), written without a junk infimum: `Q_I(Y_t)` takes values below every `ε > 0` at some
time `t ∈ [0, T)` before `τ`. -/
def ClusterCollapse (I : Finset (Fin N)) (T : ℝ) (τ : Ω → WithTop ℝ)
    (Y : ℝ → Ω → (Fin N → Euc d)) (ω : Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ t : ℝ, 0 ≤ t ∧ t < T ∧ (t : WithTop ℝ) < τ ω ∧
    clusterDispersionLift I (Y t ω) < ε

/-- The event `{σ_{I,a} ≤ T ∧ η_{I,δ} ∧ τ}` of M L11875-11890: `Q_I` reaches the level `a` at
some time `t ≤ T` before `τ` and before any one-point enlargement `Q_{I∪{j}}` reaches `δ`. -/
def ClusterReach (I : Finset (Fin N)) (a δ T : ℝ) (τ : Ω → WithTop ℝ)
    (Y : ℝ → Ω → (Fin N → Euc d)) (ω : Ω) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ (t : WithTop ℝ) < τ ω ∧ clusterDispersionLift I (Y t ω) ≤ a ∧
    ∀ s : ℝ, 0 ≤ s → s ≤ t → ∀ j, j ∉ I → δ < clusterDispersionLift (insert j I) (Y s ω)

namespace ClusterBarrier


/-- The smooth step used for the logarithmic barrier: `0` on `x ≤ q/4`, `1` on `x ≥ q/2`. -/
def barrierStep (q x : ℝ) : ℝ := Real.smoothTransition ((x - q / 4) / (q / 4))

/-- The logarithmic barrier: `-log x` for `x ≤ q/4`, constant `-log (q/2)` for `x ≥ q/2`. -/
def barrierPhi (q x : ℝ) : ℝ :=
  -Real.log x + barrierStep q x * (Real.log x - Real.log (q / 2))

section Barrier

variable {q : ℝ}

theorem barrierStep_contDiff (hq : 0 < q) : ContDiff ℝ 2 (barrierStep q) := by
  unfold barrierStep
  exact (Real.smoothTransition.contDiff (n := 2)).comp ((contDiff_id.sub contDiff_const).div_const _)

theorem barrierStep_of_le (hq : 0 < q) {x : ℝ} (hx : x ≤ q / 4) : barrierStep q x = 0 := by
  unfold barrierStep
  apply Real.smoothTransition.zero_of_nonpos
  have : 0 < q / 4 := by positivity
  rw [div_nonpos_iff]; right; exact ⟨by linarith, this.le⟩

theorem barrierStep_of_ge (hq : 0 < q) {x : ℝ} (hx : q / 2 ≤ x) : barrierStep q x = 1 := by
  unfold barrierStep
  apply Real.smoothTransition.one_of_one_le
  have : 0 < q / 4 := by positivity
  rw [le_div_iff₀ this]; linarith

theorem barrierPhi_of_le (hq : 0 < q) {x : ℝ} (hx : x ≤ q / 4) : barrierPhi q x = -Real.log x := by
  unfold barrierPhi; rw [barrierStep_of_le hq hx]; ring

theorem barrierPhi_of_ge (hq : 0 < q) {x : ℝ} (hx : q / 2 ≤ x) :
    barrierPhi q x = -Real.log (q / 2) := by
  unfold barrierPhi; rw [barrierStep_of_ge hq hx]; ring

theorem barrierPhi_contDiffOn (hq : 0 < q) : ContDiffOn ℝ 2 (barrierPhi q) (Set.Ioi 0) := by
  unfold barrierPhi
  have h1 : ContDiffOn ℝ 2 Real.log (Set.Ioi 0) := fun x hx =>
    (Real.contDiffAt_log.2 (ne_of_gt hx)).contDiffWithinAt
  have h2 : ContDiff ℝ 2 (barrierStep q) := barrierStep_contDiff hq
  exact h1.neg.add (h2.contDiffOn.mul (h1.sub contDiffOn_const))

theorem barrierStep_monotone (hq : 0 < q) : Monotone (barrierStep q) := by
  intro x y hxy
  unfold barrierStep
  apply Real.smoothTransition.monotone
  have : 0 < q / 4 := by positivity
  exact div_le_div_of_nonneg_right (by linarith) this.le

theorem barrierStep_le_one (q x : ℝ) : barrierStep q x ≤ 1 := Real.smoothTransition.le_one _

theorem barrierStep_nonneg (q x : ℝ) : 0 ≤ barrierStep q x := Real.smoothTransition.nonneg _

theorem barrierPhi_hasDerivAt (hq : 0 < q) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (barrierPhi q)
      (-(1 / x) + (deriv (barrierStep q) x * (Real.log x - Real.log (q / 2)) +
        barrierStep q x * (1 / x))) x := by
  have hs : DifferentiableAt ℝ (barrierStep q) x :=
    ((barrierStep_contDiff hq).differentiable (by norm_num)) x
  have hl : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  unfold barrierPhi
  exact hl.neg.add (hs.hasDerivAt.mul (hl.sub_const _))

theorem deriv_barrierPhi_nonpos (hq : 0 < q) {x : ℝ} (hx : 0 < x) : deriv (barrierPhi q) x ≤ 0 := by
  rw [(barrierPhi_hasDerivAt hq hx).deriv]
  have hs' : 0 ≤ deriv (barrierStep q) x := (barrierStep_monotone hq).deriv_nonneg
  have h1 := barrierStep_le_one q x
  have h0 := barrierStep_nonneg q x
  rcases le_or_gt x (q / 2) with hxq | hxq
  · have hlog : Real.log x - Real.log (q / 2) ≤ 0 := by
      have := Real.log_le_log hx hxq
      linarith
    have h2 : deriv (barrierStep q) x * (Real.log x - Real.log (q / 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hs' hlog
    have h3 : -(1 / x) + barrierStep q x * (1 / x) ≤ 0 := by
      have : 0 < 1 / x := by positivity
      nlinarith
    linarith
  · have hconst : barrierStep q =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hxq] with y hy
      exact barrierStep_of_ge hq (le_of_lt hy)
    have hd : deriv (barrierStep q) x = 0 := by
      rw [hconst.deriv_eq]; simp
    rw [hd, barrierStep_of_ge hq hxq.le]
    simp

theorem barrierPhi_antitoneOn (hq : 0 < q) : AntitoneOn (barrierPhi q) (Set.Ioi 0) := by
  have hd : DifferentiableOn ℝ (barrierPhi q) (Set.Ioi 0) :=
    (barrierPhi_contDiffOn hq).differentiableOn (by norm_num)
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0) hd.continuousOn
    (by simpa using hd) (fun x hx => ?_)
  rw [interior_Ioi] at hx
  exact deriv_barrierPhi_nonpos hq hx

theorem barrierPhi_ge (hq : 0 < q) {x : ℝ} (hx : 0 < x) : -Real.log (q / 2) ≤ barrierPhi q x := by
  rcases le_or_gt x (q / 2) with h | h
  · have := barrierPhi_antitoneOn hq hx (show (0:ℝ) < q / 2 by positivity) h
    rwa [barrierPhi_of_ge hq le_rfl] at this
  · rw [barrierPhi_of_ge hq h.le]

theorem barrierPhi_eventuallyEq_const (hq : 0 < q) {x : ℝ} (hx : q / 2 < x) :
    barrierPhi q =ᶠ[𝓝 x] fun _ => -Real.log (q / 2) := by
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact barrierPhi_of_ge hq hy.le

theorem deriv_barrierPhi_of_gt (hq : 0 < q) {x : ℝ} (hx : q / 2 < x) : deriv (barrierPhi q) x = 0 := by
  rw [(barrierPhi_eventuallyEq_const hq hx).deriv_eq]; simp

theorem deriv2_barrierPhi_of_gt (hq : 0 < q) {x : ℝ} (hx : q / 2 < x) :
    deriv (deriv (barrierPhi q)) x = 0 := by
  have : deriv (barrierPhi q) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact deriv_barrierPhi_of_gt hq hy
  rw [this.deriv_eq]; simp

theorem deriv_barrierPhi_of_le (hq : 0 < q) {x : ℝ} (hx0 : 0 < x) (hx : x < q / 4) :
    deriv (barrierPhi q) x = -(1 / x) := by
  have : barrierPhi q =ᶠ[𝓝 x] fun y => -Real.log y := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact barrierPhi_of_le hq hy.le
  rw [this.deriv_eq, deriv.fun_neg, Real.deriv_log]; simp

theorem deriv2_barrierPhi_of_le (hq : 0 < q) {x : ℝ} (hx0 : 0 < x) (hx : x < q / 4) :
    deriv (deriv (barrierPhi q)) x = 1 / x ^ 2 := by
  have : deriv (barrierPhi q) =ᶠ[𝓝 x] fun y => -(1 / y) := by
    filter_upwards [Iio_mem_nhds hx, Ioi_mem_nhds hx0] with y hy hy0
    exact deriv_barrierPhi_of_le hq hy0 hy
  rw [this.deriv_eq]
  simp [deriv.fun_neg, deriv_inv]

end Barrier

section ChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- First-derivative chain rule for `Φ ∘ Q` at a point where `Q > 0` and `Φ` is `C²` on `(0,∞)`. -/
theorem fderiv_comp_pos {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 2 Φ (Set.Ioi 0)) {Q : E → ℝ}
    (hQ : ContDiff ℝ 2 Q) {Y : E} (hY : 0 < Q Y) :
    ∀ᶠ Y' in 𝓝 Y, fderiv ℝ (Φ ∘ Q) Y' = deriv Φ (Q Y') • fderiv ℝ Q Y' := by
  have hopen : ∀ᶠ Y' in 𝓝 Y, 0 < Q Y' := hQ.continuous.continuousAt.eventually (lt_mem_nhds hY)
  filter_upwards [hopen] with Y' hY'
  have hΦd : DifferentiableAt ℝ Φ (Q Y') :=
    ((hΦ.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hY'))
  have hQd : DifferentiableAt ℝ Q Y' := (hQ.differentiable (by norm_num)) Y'
  have := hΦd.hasDerivAt.comp_hasFDerivAt Y' hQd.hasFDerivAt
  rw [this.fderiv]

theorem fderiv_comp_pos_apply {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 2 Φ (Set.Ioi 0)) {Q : E → ℝ}
    (hQ : ContDiff ℝ 2 Q) {Y : E} (hY : 0 < Q Y) (v : E) :
    fderiv ℝ (Φ ∘ Q) Y v = deriv Φ (Q Y) * fderiv ℝ Q Y v := by
  rw [(fderiv_comp_pos hΦ hQ hY).self_of_nhds]; simp

theorem fderiv_fderiv_comp_pos_apply {Φ : ℝ → ℝ} (hΦ : ContDiffOn ℝ 2 Φ (Set.Ioi 0)) {Q : E → ℝ}
    (hQ : ContDiff ℝ 2 Q) {Y : E} (hY : 0 < Q Y) (v w : E) :
    fderiv ℝ (fderiv ℝ (Φ ∘ Q)) Y v w =
      deriv (deriv Φ) (Q Y) * (fderiv ℝ Q Y v * fderiv ℝ Q Y w) +
        deriv Φ (Q Y) * fderiv ℝ (fderiv ℝ Q) Y v w := by
  have hnhds : Set.Ioi (0 : ℝ) ∈ 𝓝 (Q Y) := Ioi_mem_nhds hY
  have hΦ2 : DifferentiableAt ℝ (deriv Φ) (Q Y) := by
    have h1 : ContDiffOn ℝ 1 (deriv Φ) (Set.Ioi 0) := by
      have := hΦ.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
      exact this
    exact (h1.differentiableOn (by norm_num)).differentiableAt hnhds
  have hQd : DifferentiableAt ℝ Q Y := (hQ.differentiable (by norm_num)) Y
  have hF : HasFDerivAt (fun Y' => deriv Φ (Q Y'))
      (deriv (deriv Φ) (Q Y) • fderiv ℝ Q Y) Y := by
    exact hΦ2.hasDerivAt.comp_hasFDerivAt Y hQd.hasFDerivAt
  have hf : HasFDerivAt (fderiv ℝ Q) (fderiv ℝ (fderiv ℝ Q) Y) Y := by
    have h1 : ContDiff ℝ 1 (fderiv ℝ Q) := hQ.fderiv_right (m := 1) (by norm_num)
    exact ((h1.differentiable (by norm_num)) Y).hasFDerivAt
  have hprod : HasFDerivAt (fun Y' => deriv Φ (Q Y') • fderiv ℝ Q Y')
      (deriv Φ (Q Y) • fderiv ℝ (fderiv ℝ Q) Y +
        (deriv (deriv Φ) (Q Y) • fderiv ℝ Q Y).smulRight (fderiv ℝ Q Y)) Y := hF.smul hf
  have heq : fderiv ℝ (Φ ∘ Q) =ᶠ[𝓝 Y] fun Y' => deriv Φ (Q Y') • fderiv ℝ Q Y' :=
    fderiv_comp_pos hΦ hQ hY
  rw [heq.fderiv_eq, hprod.fderiv]
  simp [smul_eq_mul]
  ring

end ChainRule

section Generator

variable {d N : ℕ}

theorem clusterDispersionLift_pos {I : Finset (Fin N)} (hI : 2 ≤ I.card) {Y : Fin N → Euc d}
    (hY : Y ∈ liftedFree d N) : 0 < clusterDispersionLift I Y := by
  rcases (clusterDispersion_nonneg I (fun i => Torus.mk (Y i))).lt_or_eq with h | h
  · exact h
  · exfalso
    have := (clusterDispersion_eq_zero_iff I _).1 h.symm
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.1 (by omega : 1 < I.card)
    exact hY ⟨i, j, hij, this i hi j hj⟩

theorem contDiff_two_clusterDispersionLift (I : Finset (Fin N)) :
    ContDiff ℝ 2 (clusterDispersionLift (d := d) I) :=
  (contDiff_clusterDispersionLift I).of_le (WithTop.coe_le_coe.2 le_top)

/-- The generator `D g[b] + ½ ∑_k D² g[σ_k, σ_k]` of the lifted particle SDE applied to `g`
(the time-independent Itô drift). -/
def diffGen (D : DynData d) (g : (Fin N → Euc d) → ℝ) (Y : Fin N → Euc d) : ℝ :=
  fderiv ℝ g Y (liftedDrift D Y) + (1 / 2) * ∑ k : Fin N × Fin d,
    fderiv ℝ (fderiv ℝ g) Y (liftedNoise D k) (liftedNoise D k)

theorem clusterGenerator_eq_diffGen (D : DynData d) (I : Finset (Fin N)) :
    clusterGenerator D I = diffGen D (clusterDispersionLift I) := rfl

theorem diffGen_barrier (D : DynData d) (I : Finset (Fin N)) {q : ℝ} (hq : 0 < q)
    {Y : Fin N → Euc d} (hY : 0 < clusterDispersionLift I Y) :
    diffGen D (barrierPhi q ∘ clusterDispersionLift I) Y =
      deriv (barrierPhi q) (clusterDispersionLift I Y) * clusterGenerator D I Y +
        (1 / 2) * deriv (deriv (barrierPhi q)) (clusterDispersionLift I Y) *
          ∑ k : Fin N × Fin d, (fderiv ℝ (clusterDispersionLift I) Y (liftedNoise D k)) ^ 2 := by
  have hQ := contDiff_two_clusterDispersionLift (d := d) (N := N) I
  have hΦ := barrierPhi_contDiffOn hq
  unfold diffGen clusterGenerator
  rw [fderiv_comp_pos_apply hΦ hQ hY]
  simp_rw [fderiv_fderiv_comp_pos_apply hΦ hQ hY]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, sq]
  ring

/-- The pointwise generator bound for the barrier `Φ ∘ Q_I`: on the part `S` of the
collision-free region where the remainder bound holds, `ℒ(Φ ∘ Q_I) ≤ C'`. -/
theorem barrier_generator_bound (D : DynData d) (hM : Torus.SymNonpos D.M) (I : Finset (Fin N))
    (hdk : D.invβ = 0 ∨ 2 ≤ d * (I.card - 1)) (hI : 2 ≤ I.card) {q C₀ : ℝ} (hq : 0 < q)
    (hqr : q < clusterRadius I) (hC₀ : 0 ≤ C₀) (S : Set (Fin N → Euc d))
    (hrem : ∀ Y ∈ S, Y ∈ liftedFree d N → clusterDispersionLift I Y < q →
      -C₀ * clusterDispersionLift I Y ≤ clusterRemainder D I Y) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ Y ∈ S, Y ∈ liftedFree d N →
      diffGen D (barrierPhi q ∘ clusterDispersionLift I) Y ≤ C' := by
  have hΦ := barrierPhi_contDiffOn hq
  have hd1 : ContDiffOn ℝ 1 (deriv (barrierPhi q)) (Set.Ioi 0) :=
    hΦ.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
  have hc1 : ContinuousOn (deriv (barrierPhi q)) (Set.Ioi 0) := hd1.continuousOn
  have hc2 : ContinuousOn (deriv (deriv (barrierPhi q))) (Set.Ioi 0) :=
    hd1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  set f : ℝ → ℝ := fun x => |deriv (barrierPhi q) x| * C₀ * x +
    4 * D.invβ * x * |deriv (deriv (barrierPhi q)) x| with hf
  have hsub : Set.Icc (q / 4) (3 * q / 4) ⊆ Set.Ioi 0 := fun x hx => by
    simp only [Set.mem_Icc, Set.mem_Ioi] at hx ⊢; linarith [hx.1]
  have hfc : ContinuousOn f (Set.Icc (q / 4) (3 * q / 4)) := by
    have a1 := (hc1.mono hsub).abs
    have a2 := (hc2.mono hsub).abs
    exact ((a1.mul continuousOn_const).mul continuousOn_id).add
      (((continuousOn_const.mul continuousOn_id)).mul a2)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  have hc₁ : 4 * D.invβ ≤ 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ := by
    rcases hdk with h | h
    · rw [h]; simp
    · have h' : (2 : ℝ) ≤ (d : ℝ) * ((I.card : ℝ) - 1) := by
        have : ((2 : ℕ) : ℝ) ≤ ((d * (I.card - 1) : ℕ) : ℝ) := by exact_mod_cast h
        rw [Nat.cast_mul, Nat.cast_sub (by omega)] at this
        simpa using this
      nlinarith [D.hβ]
  have hc₁0 : 0 ≤ 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ := by
    have : (1 : ℝ) ≤ I.card := by exact_mod_cast (by omega : 1 ≤ I.card)
    have := D.hβ
    positivity
  refine ⟨C₀ + |B|, by positivity, fun Y hYS hYf => ?_⟩
  have hQpos := clusterDispersionLift_pos hI hYf
  set a := clusterDispersionLift I Y with ha
  rw [diffGen_barrier D I hq hQpos]
  rcases le_or_gt (3 * q / 4) a with h34 | h34
  · have h1 : deriv (barrierPhi q) a = 0 := deriv_barrierPhi_of_gt hq (by linarith)
    have h2 : deriv (deriv (barrierPhi q)) a = 0 := deriv2_barrierPhi_of_gt hq (by linarith)
    rw [h1, h2]; simp; positivity
  · have hQr : a < clusterRadius I := by linarith
    have hqv := cluster_qv D I Y hQr
    rw [hqv]
    have hG : clusterGenerator D I Y = 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ +
        clusterInternal D I Y + clusterRemainder D I Y := by
      unfold clusterRemainder; ring
    have hA := clusterInternal_nonneg D hM I Y
    have hR := hrem Y hYS hYf (by linarith)
    have hs := deriv_barrierPhi_nonpos hq hQpos
    set s := deriv (barrierPhi q) a with hsdef
    set c₁ := 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ with hc₁def
    have hGlow : c₁ - C₀ * a ≤ clusterGenerator D I Y := by rw [hG]; linarith
    have h3 : s * clusterGenerator D I Y ≤ s * (c₁ - C₀ * a) :=
      mul_le_mul_of_nonpos_left hGlow hs
    rcases lt_or_ge a (q / 4) with h4 | h4
    · have e1 : s = -(1 / a) := deriv_barrierPhi_of_le hq hQpos h4
      have e2 : deriv (deriv (barrierPhi q)) a = 1 / a ^ 2 := deriv2_barrierPhi_of_le hq hQpos h4
      rw [e2]
      have : s * (c₁ - C₀ * a) + 1 / 2 * (1 / a ^ 2) * (8 * D.invβ * a) =
          (-(c₁) + 4 * D.invβ) / a + C₀ := by
        rw [e1]; field_simp; ring
      have h5 : (-(c₁) + 4 * D.invβ) / a ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hQpos.le
      have h6 : 1 / 2 * (1 / a ^ 2) * (8 * D.invβ * a) ≥ 0 := by
        have := D.hβ; positivity
      nlinarith [abs_nonneg B]
    · have hmem : a ∈ Set.Icc (q / 4) (3 * q / 4) := ⟨h4, h34.le⟩
      have hfa := hB a hmem
      rw [Real.norm_eq_abs] at hfa
      have hfa' : f a ≤ |B| := ((le_abs_self (f a)).trans hfa).trans (le_abs_self B)
      have habs : |s| = -s := abs_of_nonpos hs
      have e3 : s * (c₁ - C₀ * a) ≤ |s| * C₀ * a := by
        rw [habs]; nlinarith [mul_nonneg (neg_nonneg.2 hs) hc₁0]
      have e4 : 1 / 2 * deriv (deriv (barrierPhi q)) a * (8 * D.invβ * a) ≤
          4 * D.invβ * a * |deriv (deriv (barrierPhi q)) a| := by
        have := D.hβ
        have h0 : 0 ≤ 4 * D.invβ * a := by positivity
        calc 1 / 2 * deriv (deriv (barrierPhi q)) a * (8 * D.invβ * a)
            = 4 * D.invβ * a * deriv (deriv (barrierPhi q)) a := by ring
          _ ≤ 4 * D.invβ * a * |deriv (deriv (barrierPhi q)) a| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) h0
      have : f a = |s| * C₀ * a + 4 * D.invβ * a * |deriv (deriv (barrierPhi q)) a| := rfl
      nlinarith [abs_nonneg B]
  
end Generator

section ProgressiveStopped

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]

/-- The dyadic time grid below `s`: `max(⌊2^m s⌋, 0) / 2^m ∈ [0, max s 0]`. -/
def gridFloor (m : ℕ) (s : ℝ) : ℝ := ((max (⌊(2 : ℝ) ^ m * s⌋) 0 : ℤ) : ℝ) / 2 ^ m

theorem gridFloor_nonneg (m : ℕ) (s : ℝ) : 0 ≤ gridFloor m s := by
  unfold gridFloor
  have : (0 : ℝ) ≤ ((max (⌊(2 : ℝ) ^ m * s⌋) 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
  positivity

theorem gridFloor_le (m : ℕ) (s : ℝ) : gridFloor m s ≤ max s 0 := by
  unfold gridFloor
  have hpos : (0 : ℝ) < 2 ^ m := by positivity
  rw [div_le_iff₀ hpos]
  rcases le_total (⌊(2 : ℝ) ^ m * s⌋) 0 with h | h
  · rw [max_eq_right h]
    simp only [Int.cast_zero]
    positivity
  · rw [max_eq_left h]
    calc ((⌊(2 : ℝ) ^ m * s⌋ : ℤ) : ℝ) ≤ 2 ^ m * s := Int.floor_le _
      _ ≤ 2 ^ m * max s 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hpos.le
      _ = max s 0 * 2 ^ m := mul_comm _ _

theorem gridFloor_eq_zero_of_nonpos (m : ℕ) {s : ℝ} (hs : s ≤ 0) : gridFloor m s = 0 := by
  unfold gridFloor
  have : ⌊(2 : ℝ) ^ m * s⌋ ≤ 0 := by
    rw [Int.floor_le_iff]
    simp only [Int.cast_zero, zero_add]
    have : (2 : ℝ) ^ m * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hs
    linarith
  rw [max_eq_right this]; simp

theorem tendsto_gridFloor (s : ℝ) : Tendsto (fun m : ℕ => gridFloor m s) atTop (𝓝 (max s 0)) := by
  rcases le_or_gt s 0 with hs | hs
  · simp only [gridFloor_eq_zero_of_nonpos _ hs, max_eq_right hs]
    exact tendsto_const_nhds
  · rw [max_eq_left hs.le]
    have hlow : ∀ m : ℕ, s - (1 / 2) ^ m ≤ gridFloor m s := by
      intro m
      unfold gridFloor
      have hpos : (0 : ℝ) < 2 ^ m := by positivity
      rw [le_div_iff₀ hpos]
      have h1 : (2 : ℝ) ^ m * s < ⌊(2 : ℝ) ^ m * s⌋ + 1 := Int.lt_floor_add_one _
      have h2 : (0 : ℝ) ≤ ((max (⌊(2 : ℝ) ^ m * s⌋) 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
      have h3 : ((⌊(2 : ℝ) ^ m * s⌋ : ℤ) : ℝ) ≤ ((max (⌊(2 : ℝ) ^ m * s⌋) 0 : ℤ) : ℝ) := by
        exact_mod_cast le_max_left _ _
      have e : (s - (1 / 2) ^ m) * 2 ^ m = 2 ^ m * s - 1 := by
        rw [sub_mul, one_div, inv_pow, inv_mul_cancel₀ hpos.ne']; ring
      rw [e]; linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow
      (fun m => (gridFloor_le m s).trans (le_of_eq (max_eq_left hs.le)))
    have : Tendsto (fun m : ℕ => s - (1 / 2 : ℝ) ^ m) atTop (𝓝 (s - 0)) :=
      tendsto_const_nhds.sub (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    simpa using this

/-- A function of `(s, ω)` that depends on `s` only through an integer-valued measurable
function of `s` is jointly measurable as soon as each section is measurable. -/
theorem measurable_comp_int_prod {α Ω β : Type*} [MeasurableSpace α] {m : MeasurableSpace Ω}
    [MeasurableSpace β] (n : α → ℤ) (hn : Measurable n) (G : ℤ → Ω → β)
    (hG : ∀ k, Measurable[m] (G k)) :
    @Measurable (α × Ω) β (@Prod.instMeasurableSpace α Ω _ m) _ (fun p => G (n p.1) p.2) := by
  letI : MeasurableSpace Ω := m
  have h1 : Measurable fun q : ℤ × Ω => G q.1 q.2 :=
    measurable_from_prod_countable_right (fun k => hG k)
  exact h1.comp ((hn.comp measurable_fst).prodMk measurable_snd)

/-- The set `{(s, ω) : s ≤ ρ ω}` is progressively measurable for a stopping time `ρ`. -/
theorem measurableSet_le_stoppingTime (ℱ : Filtration ℝ mΩ) {ρ : Ω → WithTop ℝ}
    (hρ : IsStoppingTime ℱ ρ) (t : ℝ) :
    MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ t)]
      {p : Set.Iic t × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2} := by
  have h := isProgressive_indicator_le_stoppingTime ℱ hρ t
  have : {p : Set.Iic t × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2} =
      (fun p : Set.Iic t × Ω => Set.indicator {ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ ω}
        (fun _ => (1 : ℝ)) p.2) ⁻¹' {1} := by
    ext p
    by_cases hp : ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2
    · simp [hp]
    · simp [hp]
  rw [this]
  exact h (measurableSet_singleton 1)

/-- **Progressive measurability of a solution stopped before its blow-up time**: if `Y` is adapted,
`Y 0` is measurable at every time, and the paths are continuous on `[0, t]` for every
`t ≤ ρ` (`ρ` a stopping time), then `1_{s ≤ ρ} Y_{s ∨ 0}` is progressively measurable. -/
theorem isProgressive_stoppedPath (ℱ : Filtration ℝ mΩ) (Y : ℝ → Ω → E) (hY : Adapted ℱ Y)
    (hY0 : ∀ t : ℝ, Measurable[ℱ t] (Y 0)) {ρ : Ω → WithTop ℝ} (hρ : IsStoppingTime ℱ ρ)
    (hcont : ∀ ω (t : ℝ), 0 ≤ t → (t : WithTop ℝ) ≤ ρ ω → ContinuousOn (fun s => Y s ω) (Set.Icc 0 t)) :
    IsProgressive ℱ (fun s ω => Set.indicator {ω | (s : WithTop ℝ) ≤ ρ ω}
      (fun ω => Y (max s 0) ω) ω) := by
  intro t
  let M : MeasurableSpace (Set.Iic t × Ω) := Subtype.instMeasurableSpace.prod (ℱ t)
  have hS : MeasurableSet[M] {p : Set.Iic t × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2} :=
    measurableSet_le_stoppingTime ℱ hρ t
  -- approximants
  let Yc : ℕ → ℤ × Ω → E := fun m p =>
    Y (min (((max p.1 0 : ℤ) : ℝ) / 2 ^ m) (max t 0)) p.2
  have hYc : ∀ m : ℕ, ∀ k : ℤ, Measurable[ℱ t] (fun ω => Y (min (((max k 0 : ℤ) : ℝ) / 2 ^ m) (max t 0)) ω) := by
    intro m k
    have h0 : 0 ≤ min (((max k 0 : ℤ) : ℝ) / 2 ^ m) (max t 0) := by
      refine le_min ?_ (le_max_right _ _)
      have : (0 : ℝ) ≤ ((max k 0 : ℤ) : ℝ) := by exact_mod_cast le_max_right _ _
      positivity
    rcases le_or_gt 0 t with ht | ht
    · rw [max_eq_left ht] at *
      exact (hY _).mono (ℱ.mono (min_le_right _ _)) le_rfl
    · have : min (((max k 0 : ℤ) : ℝ) / 2 ^ m) (max t 0) = 0 := by
        rw [max_eq_right ht.le] at h0 ⊢; exact le_antisymm (min_le_right _ _) h0
      rw [this]; exact hY0 t
  have happ : ∀ m : ℕ, Measurable[M] (fun p : Set.Iic t × Ω =>
      Set.indicator {ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ ω}
        (fun ω => Y (gridFloor m p.1) ω) p.2) := by
    intro m
    have hn : Measurable (fun s : Set.Iic t => ⌊(2 : ℝ) ^ m * (s : ℝ)⌋) :=
      (Int.measurable_floor).comp ((measurable_const.mul measurable_subtype_coe))
    have hG := measurable_comp_int_prod (m := ℱ t) (β := E) _ hn
      (fun k ω => Y (min (((max k 0 : ℤ) : ℝ) / 2 ^ m) (max t 0)) ω) (hYc m)
    have heq : (fun p : Set.Iic t × Ω => Y (gridFloor m p.1) p.2) =
        fun p => Y (min (((max ⌊(2 : ℝ) ^ m * (p.1 : ℝ)⌋ 0 : ℤ) : ℝ) / 2 ^ m) (max t 0)) p.2 := by
      funext p
      congr 1
      have h1 : gridFloor m (p.1 : ℝ) ≤ max t 0 :=
        (gridFloor_le m _).trans (max_le_max p.1.2 le_rfl)
      exact (min_eq_left h1).symm
    have hfun : (fun p : Set.Iic t × Ω => Set.indicator {ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ ω}
        (fun ω => Y (gridFloor m p.1) ω) p.2) =
        Set.indicator {p : Set.Iic t × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2}
          (fun p => Y (gridFloor m p.1) p.2) := by
      funext p; simp [Set.indicator]
    rw [hfun]
    refine Measurable.indicator ?_ hS
    rw [heq]
    exact hG
  have hlim : Tendsto (fun m : ℕ => fun p : Set.Iic t × Ω =>
      Set.indicator {ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ ω} (fun ω => Y (gridFloor m p.1) ω) p.2)
      atTop (𝓝 (fun p : Set.Iic t × Ω => Set.indicator {ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ ω}
        (fun ω => Y (max (p.1 : ℝ) 0) ω) p.2)) := by
    rw [tendsto_pi_nhds]
    intro p
    by_cases hp : ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2
    · simp only [Set.indicator, Set.mem_ofPred_eq, hp, if_true]
      rcases le_or_gt (p.1 : ℝ) 0 with hs | hs
      · simp only [gridFloor_eq_zero_of_nonpos _ hs, max_eq_right hs]
        exact tendsto_const_nhds
      · have hc := hcont p.2 (p.1 : ℝ) hs.le hp
        rw [max_eq_left hs.le]
        have h1 : Tendsto (fun m : ℕ => gridFloor m (p.1 : ℝ)) atTop (𝓝[Set.Icc 0 (p.1 : ℝ)] (p.1 : ℝ)) := by
          refine tendsto_nhdsWithin_iff.2 ⟨by simpa [max_eq_left hs.le] using tendsto_gridFloor (p.1 : ℝ),
            Eventually.of_forall fun m => ⟨gridFloor_nonneg m _, ?_⟩⟩
          simpa [max_eq_left hs.le] using gridFloor_le m (p.1 : ℝ)
        exact (hc (p.1 : ℝ) ⟨hs.le, le_rfl⟩).tendsto.comp h1
    · simp only [Set.indicator, Set.mem_ofPred_eq, hp, if_false]
      exact tendsto_const_nhds
  exact @measurable_of_tendsto_metrizable _ _ M _ _ _ _ _ _ happ hlim

end ProgressiveStopped

section HittingTime

/-- Hitting a closed set by a path that is continuous only on `[0,t]`: the rational criterion. -/
theorem exists_mem_Icc_iff_infDist {E : Type*} [PseudoMetricSpace E] {f : ℝ → E} {G : Set E}
    (hG : IsClosed G) (hne : G.Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (hf : ContinuousOn f (Set.Icc 0 t)) :
    (∃ r, 0 ≤ r ∧ r ≤ t ∧ f r ∈ G) ↔
      ∀ k : ℕ, ∃ q : ℚ, Metric.infDist (f (max 0 (min t (q : ℝ)))) G < 1 / ((k : ℝ) + 1) := by
  have hc_mem : ∀ x : ℝ, max 0 (min t x) ∈ Set.Icc 0 t := fun x =>
    ⟨le_max_left _ _, max_le ht (min_le_left _ _)⟩
  have hc_cont : Continuous fun x : ℝ => max 0 (min t x) :=
    continuous_const.max (continuous_const.min continuous_id)
  have hfc : Continuous fun x : ℝ => f (max 0 (min t x)) :=
    hf.comp_continuous hc_cont hc_mem
  have hg : Continuous fun x : ℝ => Metric.infDist (f (max 0 (min t x))) G :=
    (Metric.continuous_infDist_pt G).comp hfc
  constructor
  · rintro ⟨r, hr0, hrt, hr⟩ k
    have hr0' : Metric.infDist (f r) G = 0 := (hG.mem_iff_infDist_zero hne).1 hr
    have hcr : max 0 (min t r) = r := by
      rw [min_eq_right hrt, max_eq_right hr0]
    have hev : ∀ᶠ x in 𝓝 r, Metric.infDist (f (max 0 (min t x))) G < 1 / ((k : ℝ) + 1) := by
      apply hg.continuousAt.eventually_lt continuousAt_const
      simp only [hcr, hr0']
      positivity
    obtain ⟨U, hUsub, hUopen, hrU⟩ := eventually_nhds_iff.1 hev
    obtain ⟨q, hq⟩ := Rat.denseRange_cast.exists_mem_open hUopen ⟨r, hrU⟩
    exact ⟨q, hUsub _ hq⟩
  · intro h
    have hfi : ContinuousOn (fun r => Metric.infDist (f r) G) (Set.Icc 0 t) :=
      (Metric.continuous_infDist_pt G).comp_continuousOn hf
    obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 ht) hfi
    refine ⟨r₀, hr₀.1, hr₀.2, ?_⟩
    rw [hG.mem_iff_infDist_zero hne]
    refine le_antisymm ?_ Metric.infDist_nonneg
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
    obtain ⟨q, hq⟩ := h k
    have := hmin (hc_mem q)
    simp only [Set.mem_ofPred_eq] at this
    linarith

open Classical in
/-- First time `≥ 0` before `τ` at which the path `y` is in `G` (`⊤` if there is none). -/
def pathHit {E : Type*} (τ : WithTop ℝ) (y : ℝ → E) (G : Set E) : WithTop ℝ :=
  if h : ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G then
    ((sInf {r : ℝ | 0 ≤ r ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G} : ℝ) : WithTop ℝ)
  else ⊤

theorem pathHit_eq_top {E : Type*} {τ : WithTop ℝ} {y : ℝ → E} {G : Set E}
    (h : ¬ ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G) : pathHit τ y G = ⊤ := by
  unfold pathHit; rw [dif_neg h]

/-- If the path hits `G` before `τ`, the hitting time is attained and is the first one. -/
theorem pathHit_spec {E : Type*} [TopologicalSpace E] {τ : WithTop ℝ} {y : ℝ → E} {G : Set E}
    (hG : IsClosed G) (hcont : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → ContinuousOn y (Set.Icc 0 t))
    (h : ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G) :
    ∃ r₀ : ℝ, pathHit τ y G = (r₀ : WithTop ℝ) ∧ 0 ≤ r₀ ∧ (r₀ : WithTop ℝ) < τ ∧ y r₀ ∈ G ∧
      ∀ r : ℝ, 0 ≤ r → (r : WithTop ℝ) < τ → y r ∈ G → r₀ ≤ r := by
  set S : Set ℝ := {r : ℝ | 0 ≤ r ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G} with hS
  obtain ⟨r₁, hr₁0, hr₁τ, hr₁G⟩ := h
  have hr₁S : r₁ ∈ S := ⟨hr₁0, hr₁τ, hr₁G⟩
  have hbdd : BddBelow S := ⟨0, fun r hr => hr.1⟩
  set S₁ : Set ℝ := Set.Icc 0 r₁ ∩ y ⁻¹' G with hS₁
  have hS₁closed : IsClosed S₁ :=
    (hcont r₁ hr₁0 hr₁τ).preimage_isClosed_of_isClosed isClosed_Icc hG
  have hr₁S₁ : r₁ ∈ S₁ := ⟨⟨hr₁0, le_rfl⟩, hr₁G⟩
  have hS₁bdd : BddBelow S₁ := ⟨0, fun r hr => hr.1.1⟩
  have hr₀mem : sInf S₁ ∈ S₁ := hS₁closed.csInf_mem ⟨r₁, hr₁S₁⟩ hS₁bdd
  have hr₀le : sInf S₁ ≤ r₁ := csInf_le hS₁bdd hr₁S₁
  have hr₀S : sInf S₁ ∈ S := ⟨hr₀mem.1.1, lt_of_le_of_lt (by exact_mod_cast hr₀le) hr₁τ, hr₀mem.2⟩
  have hlow : ∀ r ∈ S, sInf S₁ ≤ r := by
    intro r hr
    by_cases hrr : r ≤ r₁
    · exact csInf_le hS₁bdd ⟨⟨hr.1, hrr⟩, hr.2.2⟩
    · exact hr₀le.trans (not_le.1 hrr).le
  have hsInf : sInf S = sInf S₁ :=
    le_antisymm (csInf_le hbdd hr₀S) (le_csInf ⟨r₁, hr₁S⟩ hlow)
  refine ⟨sInf S₁, ?_, hr₀S.1, hr₀S.2.1, hr₀S.2.2, fun r hr0 hrτ hrG => hlow r ⟨hr0, hrτ, hrG⟩⟩
  unfold pathHit
  rw [dif_pos ⟨r₁, hr₁0, hr₁τ, hr₁G⟩]
  rw [hsInf]

theorem pathHit_le_iff {E : Type*} [TopologicalSpace E] {τ : WithTop ℝ} {y : ℝ → E} {G : Set E}
    (hG : IsClosed G) (hcont : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → ContinuousOn y (Set.Icc 0 t))
    (t : ℝ) :
    pathHit τ y G ≤ (t : WithTop ℝ) ↔
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ t ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G := by
  constructor
  · intro h
    by_cases hex : ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G
    · obtain ⟨r₀, h0, hr0, hr0τ, hr0G, -⟩ := pathHit_spec hG hcont hex
      rw [h0] at h
      exact ⟨r₀, hr0, by exact_mod_cast h, hr0τ, hr0G⟩
    · rw [pathHit_eq_top hex] at h
      exact absurd h (by simp)
  · rintro ⟨r, hr0, hrt, hrτ, hrG⟩
    obtain ⟨r₀, h0, -, -, -, hmin⟩ := pathHit_spec hG hcont ⟨r, hr0, hrτ, hrG⟩
    rw [h0]
    exact_mod_cast (hmin r hr0 hrτ hrG).trans hrt

/-- Before (and at) the hitting time of `G`, a path starting in the closed set `K ⊇ Gᶜ` stays in `K`. -/
theorem pathHit_mem_of_le {E : Type*} [TopologicalSpace E] {τ : WithTop ℝ} {y : ℝ → E}
    {G K : Set E} (hG : IsClosed G) (hK : IsClosed K) (hGK : Gᶜ ⊆ K)
    (hcont : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → ContinuousOn y (Set.Icc 0 t))
    (h0 : y 0 ∈ K) {t : ℝ} (ht0 : 0 ≤ t) (htτ : (t : WithTop ℝ) < τ)
    (ht : (t : WithTop ℝ) ≤ pathHit τ y G) : y t ∈ K := by
  rcases ht.lt_or_eq with hlt | heq
  · by_contra hyK
    have hyG : y t ∈ G := by
      by_contra hyG
      exact hyK (hGK hyG)
    have := (pathHit_le_iff hG hcont t).2 ⟨t, ht0, le_rfl, htτ, hyG⟩
    exact absurd hlt (not_lt.2 this)
  · have hex : ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G := by
      by_contra hne
      rw [pathHit_eq_top hne] at heq
      exact absurd heq (by simp)
    obtain ⟨r₀, h0', -, -, -, hmin⟩ := pathHit_spec hG hcont hex
    rw [h0'] at heq
    have htr : t = r₀ := by exact_mod_cast heq
    rcases eq_or_lt_of_le ht0 with h00 | hpos
    · rw [← h00]; exact h0
    · have hsub : ∀ s ∈ Set.Ico 0 t, y s ∈ K := by
        intro s hs
        by_contra hsK
        have hsG : y s ∈ G := by
          by_contra hsG
          exact hsK (hGK hsG)
        have hsτ : (s : WithTop ℝ) < τ := lt_of_le_of_lt (by exact_mod_cast hs.2.le) htτ
        have := hmin s hs.1 hsτ hsG
        linarith [hs.2]
      have hcl : t ∈ closure (Set.Ico 0 t) := by
        rw [closure_Ico hpos.ne]; exact ⟨ht0, le_rfl⟩
      have hcw : ContinuousWithinAt y (Set.Ico 0 t) t :=
        ((hcont t ht0 htτ) t ⟨ht0, le_rfl⟩).mono Set.Ico_subset_Icc_self
      have := hcw.mem_closure_image hcl
      have hsub' : y '' Set.Ico 0 t ⊆ K := by
        rintro _ ⟨s, hs, rfl⟩; exact hsub s hs
      exact (closure_minimal hsub' hK) this

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The first hitting time of a closed set `G` by the pre-blow-up path of a solution. -/
def solHit (τ : Ω → WithTop ℝ) (Y : ℝ → Ω → E) (G : Set E) (ω : Ω) : WithTop ℝ :=
  pathHit (τ ω) (fun t => Y t ω) G

/-- The first hitting time of a closed set by an adapted process that is continuous before the
stopping time `τ`, and which is forced to hit the set before `τ` when `τ < ∞`, is a stopping time. -/
theorem isStoppingTime_solHit (ℱ : Filtration ℝ mΩ) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    {Y : ℝ → Ω → E} (hY : Adapted ℱ Y)
    (hcont : ∀ ω (t : ℝ), 0 ≤ t → (t : WithTop ℝ) < τ ω → ContinuousOn (fun s => Y s ω) (Set.Icc 0 t))
    {G : Set E} (hG : IsClosed G)
    (hexit : ∀ ω, τ ω < ⊤ → ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ω ∧ Y r ω ∈ G) :
    IsStoppingTime ℱ (solHit τ Y G) := by
  intro t
  rcases G.eq_empty_or_nonempty with rfl | hne
  · have : {ω | solHit τ Y (∅ : Set E) ω ≤ (t : WithTop ℝ)} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      rw [solHit, pathHit_eq_top (by simp)] at h
      exact absurd h (by simp)
    rw [this]; exact @MeasurableSet.empty _ (ℱ t)
  have hset : {ω | solHit τ Y G ω ≤ (t : WithTop ℝ)} =
      {ω | ∃ r : ℝ, 0 ≤ r ∧ r ≤ t ∧ (r : WithTop ℝ) < τ ω ∧ Y r ω ∈ G} := by
    ext ω
    exact pathHit_le_iff hG (hcont ω) t
  rw [hset]
  by_cases ht : 0 ≤ t
  · have hkey : {ω | ∃ r : ℝ, 0 ≤ r ∧ r ≤ t ∧ (r : WithTop ℝ) < τ ω ∧ Y r ω ∈ G} =
        {ω | τ ω ≤ (t : WithTop ℝ)} ∪ ({ω | τ ω ≤ (t : WithTop ℝ)}ᶜ ∩
          ⋂ k : ℕ, ⋃ q : ℚ, {ω | Metric.infDist (Y (max 0 (min t (q : ℝ))) ω) G < 1 / ((k : ℝ) + 1)}) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
        Set.mem_iInter, Set.mem_iUnion]
      by_cases hτt : τ ω ≤ (t : WithTop ℝ)
      · have hlt : τ ω < ⊤ := lt_of_le_of_lt hτt (WithTop.coe_lt_top t)
        obtain ⟨r, hr0, hrτ, hrG⟩ := hexit ω hlt
        have : r ≤ t := by
          have := hrτ.le.trans hτt
          exact_mod_cast this
        simp only [hτt, true_or, iff_true]
        exact ⟨r, hr0, this, hrτ, hrG⟩
      · have htτ : (t : WithTop ℝ) < τ ω := not_le.1 hτt
        have hc := hcont ω t ht htτ
        simp only [hτt, false_or, not_false_eq_true, true_and]
        rw [← exists_mem_Icc_iff_infDist hG hne ht hc]
        constructor
        · rintro ⟨r, h0, h1, -, h3⟩; exact ⟨r, h0, h1, h3⟩
        · rintro ⟨r, h0, h1, h3⟩
          exact ⟨r, h0, h1, lt_of_le_of_lt (by exact_mod_cast h1) htτ, h3⟩
    rw [hkey]
    refine MeasurableSet.union (hτ t) (MeasurableSet.inter (hτ t).compl ?_)
    refine MeasurableSet.iInter fun k => MeasurableSet.iUnion fun q => ?_
    have hmem : max 0 (min t (q : ℝ)) ≤ t := max_le ht (min_le_left _ _)
    have hm : Measurable[ℱ t] (fun ω => Metric.infDist (Y (max 0 (min t (q : ℝ))) ω) G) :=
      (Metric.continuous_infDist_pt G).measurable.comp
        ((hY _).mono (ℱ.mono hmem) le_rfl)
    exact hm measurableSet_Iio
  · have : {ω | ∃ r : ℝ, 0 ≤ r ∧ r ≤ t ∧ (r : WithTop ℝ) < τ ω ∧ Y r ω ∈ G} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨r, h0, h1, -⟩
      exact ht (h0.trans h1)
    rw [this]; exact @MeasurableSet.empty _ (ℱ t)

end HittingTime

section Ito

/-- A time-independent function which is `C²` on an open set is `C^{1,2}` there. -/
theorem isC12On_of_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    {U : Set E} (hU : IsOpen U) {g : E → ℝ} (hg : ContDiffOn ℝ 2 g U) :
    IsC12On T U (fun _ x => g x) := by
  have hg1 : ContDiffOn ℝ 1 (fderiv ℝ g) U := hg.fderiv_of_isOpen hU (m := 1) (by norm_num)
  have hca : ∀ x ∈ U, ContDiffAt ℝ 2 g x := fun x hx => hg.contDiffAt (hU.mem_nhds hx)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hg.continuousOn.comp continuousOn_snd (fun p hp => hp.2)
  · intro t _ x hx
    exact ((hca x hx).differentiableAt (by norm_num)).hasFDerivAt
  · intro t _ x hx
    have : ContDiffAt ℝ 1 (fderiv ℝ g) x := (hca x hx).fderiv_right (m := 1) (by norm_num)
    exact (this.differentiableAt (by norm_num)).hasFDerivAt
  · exact (hg.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp continuousOn_snd
      (fun p hp => hp.2)
  · exact (hg1.continuousOn_fderiv_of_isOpen hU le_rfl).comp continuousOn_snd (fun p hp => hp.2)
  · intro x _ t _
    have h0 : HasDerivWithinAt (fun _ : ℝ => g x) 0 (Set.Icc 0 T) t := hasDerivWithinAt_const t _ _
    have : derivWithin (fun _ : ℝ => g x) (Set.Icc 0 T) t = 0 := by simp
    rw [this]; exact h0
  · have : (fun p : ℝ × E => derivWithin (fun r => (fun (_ : ℝ) (x : E) => g x) r p.2)
        (Set.Icc 0 T) p.1) = fun _ => 0 := by
      funext p; simp
    rw [this]
    exact continuousOn_const

end Ito

section BarrierSets

variable {d N : ℕ}

/-- The pair separation `ψ(x_i - x_j)` on the covering space. -/
def pairSep (Z : Fin N → Euc d) (i j : Fin N) : ℝ := Torus.lift (pairDispersion (d := d)) (Z i - Z j)

theorem continuous_pairSep (i j : Fin N) : Continuous fun Z : Fin N → Euc d => pairSep Z i j := by
  have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (pairDispersion (d := d))) := by
    have := pairDispersion_smooth (d := d)
    unfold Torus.IsSmooth Torus.IsCk at this
    exact this
  exact h.continuous.comp ((continuous_apply i).sub (continuous_apply j))

theorem pairSep_pos {Z : Fin N → Euc d} (hZ : Z ∈ liftedFree d N) {i j : Fin N} (hij : i ≠ j) :
    0 < pairSep Z i j := by
  rcases (pairDispersion_nonneg (Torus.mk (Z i - Z j))).lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 := (pairDispersion_eq_zero_iff _).1 h.symm
    rw [mk_sub', sub_eq_zero] at h0
    exact hZ ⟨i, j, hij, h0⟩

theorem exists_pairSep_gt {Z : Fin N → Euc d} (hZ : Z ∈ liftedFree d N) :
    ∃ n : ℕ, ∀ i j, i ≠ j → 1 / ((n : ℝ) + 1) < pairSep Z i j := by
  have : ∃ c : ℝ, 0 < c ∧ ∀ i j, i ≠ j → c ≤ pairSep Z i j := by
    classical
    by_cases hN : (Finset.univ.filter fun p : Fin N × Fin N => p.1 ≠ p.2).Nonempty
    · obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ (fun p : Fin N × Fin N => pairSep Z p.1 p.2) hN
      refine ⟨pairSep Z p.1 p.2, pairSep_pos hZ (Finset.mem_filter.1 hp).2, fun i j hij => ?_⟩
      exact hmin (i, j) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩)
    · refine ⟨1, one_pos, fun i j hij => ?_⟩
      exact absurd ⟨(i, j), Finset.mem_filter.2 ⟨Finset.mem_univ _, hij⟩⟩ hN
  obtain ⟨c, hc, hcle⟩ := this
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hc
  exact ⟨n, fun i j hij => lt_of_lt_of_le hn (hcle i j hij)⟩

/-- The compact set `K_n` on which the barrier argument is localised. -/
def barrierK (I : Finset (Fin N)) (a δ : ℝ) (n : ℕ) : Set (Fin N → Euc d) :=
  Metric.closedBall 0 ((n : ℝ) + 1) ∩ {Z | ∀ i j, i ≠ j → 1 / ((n : ℝ) + 1) ≤ pairSep Z i j} ∩
    {Z | a ≤ clusterDispersionLift I Z} ∩
    {Z | ∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z}

/-- The closed set whose first hitting time stops the barrier argument. -/
def barrierG (I : Finset (Fin N)) (a δ : ℝ) (n : ℕ) : Set (Fin N → Euc d) :=
  {Z | clusterDispersionLift I Z ≤ a} ∪ {Z | ∃ j, j ∉ I ∧ clusterDispersionLift (insert j I) Z ≤ δ} ∪
    {Z | (n : ℝ) + 1 ≤ ‖Z‖} ∪ {Z | ∃ i j, i ≠ j ∧ pairSep Z i j ≤ 1 / ((n : ℝ) + 1)}

theorem continuous_clusterDispersionLift (I : Finset (Fin N)) :
    Continuous (clusterDispersionLift (d := d) I) :=
  (contDiff_two_clusterDispersionLift I).continuous

theorem isClosed_barrierK (I : Finset (Fin N)) (a δ : ℝ) (n : ℕ) :
    IsClosed (barrierK (d := d) I a δ n) := by
  unfold barrierK
  refine ((Metric.isClosed_closedBall.inter ?_).inter (isClosed_le continuous_const
    (continuous_clusterDispersionLift I))).inter ?_
  swap
  · have : {Z : Fin N → Euc d | ∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z} =
        ⋂ j, ⋂ (_ : j ∉ I), {Z | δ ≤ clusterDispersionLift (insert j I) Z} := by
      ext Z; simp
    rw [this]
    exact isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (continuous_clusterDispersionLift _)
  have : {Z : Fin N → Euc d | ∀ i j, i ≠ j → 1 / ((n : ℝ) + 1) ≤ pairSep Z i j} =
      ⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {Z | 1 / ((n : ℝ) + 1) ≤ pairSep Z i j} := by
    ext Z; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_le continuous_const (continuous_pairSep i j)

theorem isCompact_barrierK (I : Finset (Fin N)) (a δ : ℝ) (n : ℕ) :
    IsCompact (barrierK (d := d) I a δ n) :=
  (isCompact_closedBall (0 : Fin N → Euc d) ((n : ℝ) + 1)).of_isClosed_subset
    (isClosed_barrierK I a δ n)
    (Set.inter_subset_left.trans (Set.inter_subset_left.trans Set.inter_subset_left))

theorem isClosed_barrierG (I : Finset (Fin N)) (a δ : ℝ) (n : ℕ) :
    IsClosed (barrierG (d := d) I a δ n) := by
  unfold barrierG
  refine ((( isClosed_le (continuous_clusterDispersionLift I) continuous_const).union ?_).union
    (isClosed_le continuous_const continuous_norm)).union ?_
  · have : {Z : Fin N → Euc d | ∃ j, j ∉ I ∧ clusterDispersionLift (insert j I) Z ≤ δ} =
        ⋃ j, ⋃ (_ : j ∉ I), {Z | clusterDispersionLift (insert j I) Z ≤ δ} := by
      ext Z; simp
    rw [this]
    exact isClosed_iUnion_of_finite fun j => isClosed_iUnion_of_finite fun _ =>
      isClosed_le (continuous_clusterDispersionLift _) continuous_const
  · have : {Z : Fin N → Euc d | ∃ i j, i ≠ j ∧ pairSep Z i j ≤ 1 / ((n : ℝ) + 1)} =
        ⋃ i, ⋃ j, ⋃ (_ : i ≠ j), {Z | pairSep Z i j ≤ 1 / ((n : ℝ) + 1)} := by
      ext Z; simp
    rw [this]
    exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
      isClosed_iUnion_of_finite fun _ => isClosed_le (continuous_pairSep i j) continuous_const

theorem barrierG_compl_subset (I : Finset (Fin N)) (a δ : ℝ) (n : ℕ) :
    (barrierG (d := d) I a δ n)ᶜ ⊆ barrierK I a δ n := by
  intro Z hZ
  simp only [barrierG, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq, not_or,
    not_exists, not_le, not_and] at hZ
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hZ
  refine ⟨⟨⟨?_, fun i j hij => (h4 i j hij).le⟩, h1.le⟩, fun j hj => (h2 j hj).le⟩
  rw [mem_closedBall_zero_iff]; exact h3.le

theorem barrierK_subset_free (I : Finset (Fin N)) (a δ : ℝ) (n : ℕ) :
    barrierK (d := d) I a δ n ⊆ liftedFree d N := by
  intro Z hZ hcoll
  obtain ⟨i, j, hij, h⟩ := hcoll
  have h1 := hZ.1.1.2 i j hij
  have h2 : pairSep Z i j = 0 := by
    unfold pairSep Torus.lift
    simp only [Function.comp, mk_sub', h, sub_self]
    exact (pairDispersion_eq_zero_iff 0).2 rfl
  rw [h2] at h1
  have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

theorem barrierK_subset_pos (I : Finset (Fin N)) {a : ℝ} (ha : 0 < a) (δ : ℝ) (n : ℕ) :
    barrierK (d := d) I a δ n ⊆ {Z | 0 < clusterDispersionLift I Z} :=
  fun Z hZ => lt_of_lt_of_le ha hZ.1.2

end BarrierSets

section ProgSections

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem progressive_measurable_min {β : Type*} [MeasurableSpace β] {ℱ : Filtration ℝ mΩ}
    {u : ℝ → Ω → β} (hu : IsProgressive ℱ u) (T : ℝ) :
    Measurable fun x : ℝ × Ω => u (min x.1 T) x.2 := by
  have hq : Measurable[Prod.instMeasurableSpace, Subtype.instMeasurableSpace.prod (ℱ T)]
      fun x : ℝ × Ω => ((⟨min x.1 T, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic T), x.2) :=
    Measurable.prodMk (Measurable.subtype_mk (measurable_fst.min measurable_const))
      (measurable_snd.mono le_rfl (ℱ.le T))
  exact (hu T).comp hq

/-- Sections of a progressively measurable process are a.e. strongly measurable on `[0, T]`. -/
theorem progressive_aestronglyMeasurable_Icc {β : Type*} [MeasurableSpace β]
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β] [SecondCountableTopology β]
    {ℱ : Filtration ℝ mΩ} {u : ℝ → Ω → β} (hu : IsProgressive ℱ u) (T : ℝ) (ω : Ω) :
    AEStronglyMeasurable (fun s => u s ω) (volume.restrict (Set.Icc 0 T)) := by
  have h1 : Measurable fun s : ℝ => u (min s T) ω :=
    (progressive_measurable_min hu T).comp (measurable_id.prodMk measurable_const)
  refine h1.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  simp [min_eq_left hs.2]

end ProgSections

section ItoAlong

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

/-- The drift of the lifted SDE, cut off outside a compact subset of the collision-free region
and stopped at `ρ` and `T`: the progressive drift process used in Itô's formula. -/
def stoppedDrift (D : DynData d) (K : Set (Fin N → Euc d)) (T : ℝ) (ρ : Ω → WithTop ℝ)
    (Y : ℝ → Ω → (Fin N → Euc d)) : ℝ → Ω → (Fin N → Euc d) :=
  fun s ω => open Classical in
    if (0 ≤ s ∧ s ≤ T ∧ (s : WithTop ℝ) ≤ ρ ω) then
      K.piecewise (liftedDrift D) (fun _ => 0)
        (Set.indicator {ω | (s : WithTop ℝ) ≤ ρ ω} (fun ω => Y (max s 0) ω) ω)
    else 0

theorem ito_along_solution [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {T : ℝ} (hT : 0 ≤ T)
    (ρ : Ω → WithTop ℝ) (hρ : IsStoppingTime ℱ ρ) (hρτ : ∀ ω, ρ ω < τ ω)
    {U : Set (Fin N → Euc d)} (hU : IsOpen U) (Kc : Set (Fin N → Euc d)) (hKc : IsCompact Kc)
    (hKU : Kc ⊆ U) (hKfree : Kc ⊆ liftedFree d N) {g : (Fin N → Euc d) → ℝ}
    (hg : ContDiffOn ℝ 2 g U)
    (hYK : ∀ ω, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ ρ ω → Y t ω ∈ Kc) :
    ∃ Ψ : ℝ → Ω → (Fin N × Fin d) → ℝ, IsProgressiveL2 P ℱ Ψ ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → s ≤ T → (s : WithTop ℝ) ≤ ρ ω → ∀ k,
        Ψ s ω k = fderiv ℝ g (Y s ω) (liftedNoise D k)) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ ρ ω →
        IntegrableOn (fun s => diffGen D g (Y s ω)) (Set.Icc 0 t) ∧
        g (Y t ω) = g (Y₀ ω) + (∫ s in Set.Icc 0 t, diffGen D g (Y s ω)) +
          localItoIntegral P ℱ W' (stopIntegrand Ψ ρ) t ω := by
  classical
  have hY0 : ∀ t : ℝ, Measurable[ℱ t] (Y 0) := by
    have : Y 0 = Y₀ := funext hsol.sol.init
    rw [this]; exact hsol.init_meas
  have hcont : ∀ ω (t : ℝ), 0 ≤ t → (t : WithTop ℝ) ≤ ρ ω →
      ContinuousOn (fun s => Y s ω) (Set.Icc 0 t) := fun ω t ht h =>
    hsol.sol.cont ω t ht (lt_of_le_of_lt h (hρτ ω))
  have hVprog := isProgressive_stoppedPath ℱ Y hsol.sol.adapted hY0 hρ hcont
  have hlip := liftedDrift_locLipschitz (N := N) D hK.smoothOffZero hV
  have hFc : ContinuousOn (liftedDrift D) (liftedFree d N) := by
    have h1 : ContinuousOn (Function.uncurry fun (_ : ℝ) (Z : Fin N → Euc d) => liftedDrift D Z)
        (Set.Ici 0 ×ˢ liftedFree d N) := hlip.cont
    have h2 : ContinuousOn (fun z : Fin N → Euc d => ((0 : ℝ), z)) (liftedFree d N) :=
      (continuousOn_const.prodMk continuousOn_id)
    have h3 : Set.MapsTo (fun z : Fin N → Euc d => ((0 : ℝ), z)) (liftedFree d N)
        (Set.Ici 0 ×ˢ liftedFree d N) := fun z hz => ⟨Set.mem_Ici.2 le_rfl, hz⟩
    have h4 := ContinuousOn.comp h1 h2 h3
    exact h4
  have hFKm : Measurable (Kc.piecewise (liftedDrift D) (fun _ => (0 : Fin N → Euc d))) :=
    ContinuousOn.measurable_piecewise (hFc.mono hKfree) continuousOn_const
      hKc.isClosed.measurableSet
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn (hFc.mono hKfree)
  set b := stoppedDrift D Kc T ρ Y with hbdef
  have hb_apply : ∀ ω s, 0 ≤ s → s ≤ T → (s : WithTop ℝ) ≤ ρ ω →
      b s ω = liftedDrift D (Y s ω) := by
    intro ω s hs0 hsT hsρ
    have hmem : Y s ω ∈ Kc := hYK ω s ⟨hs0, hsT⟩ hsρ
    simp only [hbdef, stoppedDrift, hs0, hsT, hsρ, and_self, ite_true]
    rw [Set.indicator_of_mem (show ω ∈ {ω | (s : WithTop ℝ) ≤ ρ ω} from hsρ), max_eq_left hs0,
      Set.piecewise_eq_of_mem _ _ _ hmem]
  have hb_bound : ∀ ω s, ‖b s ω‖ ≤ max B 0 := by
    intro ω s
    simp only [hbdef, stoppedDrift]
    split_ifs with hc
    · by_cases hmem : Set.indicator {ω | (s : WithTop ℝ) ≤ ρ ω} (fun ω => Y (max s 0) ω) ω ∈ Kc
      · rw [Set.piecewise_eq_of_mem _ _ _ hmem]
        exact (hB _ hmem).trans (le_max_left _ _)
      · rw [Set.piecewise_eq_of_notMem _ _ _ hmem]
        simp
    · simp
  have hb_prog : IsProgressive ℱ b := by
    intro i
    let M : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    have hS : MeasurableSet[M] {p : Set.Iic i × Ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2} :=
      measurableSet_le_stoppingTime ℱ hρ i
    have hc : MeasurableSet[M] {p : Set.Iic i × Ω |
        0 ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ T ∧ ((p.1 : ℝ) : WithTop ℝ) ≤ ρ p.2} := by
      have h1 : MeasurableSet[M] {p : Set.Iic i × Ω | 0 ≤ (p.1 : ℝ)} :=
        measurableSet_le measurable_const (measurable_subtype_coe.comp measurable_fst)
      have h2 : MeasurableSet[M] {p : Set.Iic i × Ω | (p.1 : ℝ) ≤ T} :=
        measurableSet_le (measurable_subtype_coe.comp measurable_fst) measurable_const
      exact h1.inter (h2.inter hS)
    have hm : Measurable[M] (fun p : Set.Iic i × Ω =>
        Kc.piecewise (liftedDrift D) (fun _ => (0 : Fin N → Euc d))
          (Set.indicator {ω | ((p.1 : ℝ) : WithTop ℝ) ≤ ρ ω} (fun ω => Y (max (p.1 : ℝ) 0) ω) p.2)) :=
      hFKm.comp (hVprog i)
    exact Measurable.ite hc hm measurable_const
  have hb_L1 : IsProgressiveLocL1 P ℱ b := by
    refine ⟨hb_prog, fun T' => Eventually.of_forall fun ω => ?_⟩
    exact Integrable.of_bound (C := max B 0) (progressive_aestronglyMeasurable_Icc hb_prog T' ω)
      (Eventually.of_forall fun s => hb_bound ω s)
  -- the constant noise integrand
  have hΦ : IsProgressiveLocL2E P ℱ (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) := by
    refine ⟨isProgressive_const ℱ (liftedNoise (N := N) D), fun T' => Eventually.of_forall fun ω => ?_⟩
    simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    refine ENNReal.mul_lt_top ?_ (by simp)
    exact ENNReal.sum_lt_top.2 fun k _ => ENNReal.pow_lt_top (enorm_lt_top)
  set X := itoProcess P ℱ W' Y₀ b (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) with hXdef
  have hXY : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, (t : WithTop ℝ) ≤ ρ ω → X t ω = Y t ω := by
    filter_upwards [localItoIntegralE_const hW' (liftedNoise (N := N) D), hsol.sol.eq] with ω h1 h2 t ht htρ
    have htτ : (t : WithTop ℝ) < τ ω := lt_of_le_of_lt htρ (hρτ ω)
    have h3 := (h2 t ht.1 htτ).2
    have h4 : (∫ s in Set.Icc (0 : ℝ) t, b s ω) = ∫ s in Set.Icc (0 : ℝ) t, liftedDrift D (Y s ω) :=
      setIntegral_congr_fun measurableSet_Icc fun s hs =>
        hb_apply ω s hs.1 (hs.2.trans ht.2) (le_trans (by exact_mod_cast hs.2) htρ)
    simp only [hXdef, itoProcess]
    rw [h1 t, h4, h3]
  have hXK : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, (t : WithTop ℝ) ≤ ρ ω → X t ω ∈ Kc := by
    filter_upwards [hXY] with ω h t ht htρ
    rw [h t ht htρ]; exact hYK ω t ht htρ
  have hf := isC12On_of_contDiffOn T hU hg
  have hmain := ito_formula_localized hW' hT U hU Kc hKc hKU (fun _ x => g x) hf Y₀
    hsol.init_meas b hb_L1 (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) hΦ ρ hρ hXK
  have hXad : Adapted ℱ X := adapted_itoProcess Y₀ hsol.init_meas b hb_prog _
  have hXc : ∀ᵐ ω ∂P, Continuous fun t => X t ω := continuous_itoProcess Y₀ b hb_L1 _
  have hprogLoc := isProgressiveLocL2_itoIntegrand Kc hKc.isClosed U hKU
    (fun _ x => g x) hf X (isProgressive_itoProcess Y₀ hsol.init_meas b hb_prog _) hXc _ hΦ
  -- boundedness of the martingale integrand
  have hdg : ContinuousOn (fderiv ℝ g) Kc :=
    (hg.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn hdg
  set C₂ : ℝ := ∑ k, ‖liftedNoise (N := N) D k‖ with hC₂
  have hΨbdd : ∀ s ω k, |itoIntegrand T Kc (fun _ x => g x) X (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) s ω k|
      ≤ max C₁ 0 * C₂ := by
    intro s ω k
    simp only [itoIntegrand, Set.indicator]
    split_ifs with h1 h2
    · rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ g (X s ω) (liftedNoise D k)‖
          ≤ ‖fderiv ℝ g (X s ω)‖ * ‖liftedNoise D k‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ max C₁ 0 * C₂ := by
          apply mul_le_mul ((hC₁ _ h2).trans (le_max_left _ _))
            (Finset.single_le_sum (f := fun k => ‖liftedNoise (N := N) D k‖) (fun _ _ => norm_nonneg _)
              (Finset.mem_univ k)) (norm_nonneg _) (le_max_right _ _)
    · simp [hC₂]; positivity
    · simp [hC₂]; positivity
  have hΨ2 : IsProgressiveL2 P ℱ
      (itoIntegrand T Kc (fun _ x => g x) X (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D)) :=
    IsProgressiveL2.of_bounded P hprogLoc.prog _ hΨbdd
  refine ⟨_, hΨ2, ?_, ?_⟩
  · filter_upwards [hXY] with ω h s hs0 hsT hsρ k
    have hXs := h s ⟨hs0, hsT⟩ hsρ
    simp only [itoIntegrand, Set.indicator, Set.mem_Icc, Set.mem_ofPred_eq, hs0, hsT, and_self,
      ite_true, hXs, hYK ω s ⟨hs0, hsT⟩ hsρ]
  · filter_upwards [hmain, hXY] with ω h1 h2 t ht htρ
    obtain ⟨hint, heq⟩ := h1 t ht htρ
    have hdrift : ∀ s ∈ Set.Icc (0 : ℝ) t,
        itoDrift T (fun _ x => g x) X b (fun (_ : ℝ) (_ : Ω) => liftedNoise (N := N) D) s ω =
          diffGen D g (Y s ω) := by
      intro s hs
      have hsT : s ≤ T := hs.2.trans ht.2
      have hsρ : (s : WithTop ℝ) ≤ ρ ω := le_trans (by exact_mod_cast hs.2) htρ
      have hXs := h2 s ⟨hs.1, hsT⟩ hsρ
      simp only [itoDrift, diffGen, hXs, hb_apply ω s hs.1 hsT hsρ]
      simp
    refine ⟨hint.congr_fun hdrift measurableSet_Icc, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Icc hdrift] at heq
    have hX0 : X 0 ω = Y₀ ω := by
      simp [hXdef, itoProcess_zero]
    rw [← h2 t ht htρ]
    simpa [hX0] using heq

end ItoAlong


section StoppedEstimate

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

theorem pathHit_nonneg {E : Type*} [TopologicalSpace E] {τ : WithTop ℝ} {y : ℝ → E} {G : Set E}
    (hG : IsClosed G)
    (hcont : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → ContinuousOn y (Set.Icc 0 t)) :
    (0 : WithTop ℝ) ≤ pathHit τ y G := by
  by_cases hex : ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ∧ y r ∈ G
  · obtain ⟨r₀, h0, hr0, -⟩ := pathHit_spec hG hcont hex
    rw [h0]; exact_mod_cast hr0
  · rw [pathHit_eq_top hex]; exact le_top



theorem untopA_coe' (r : ℝ) : (r : WithTop ℝ).untopA = r := by
  rw [WithTop.untopA_eq_untop WithTop.coe_ne_top]; simp

theorem stopped_estimate [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {T : ℝ} (hT : 0 ≤ T)
    {U : Set (Fin N → Euc d)} (hU : IsOpen U) (Kc : Set (Fin N → Euc d)) (hKc : IsCompact Kc)
    (hKU : Kc ⊆ U) (hKfree : Kc ⊆ liftedFree d N) {g : (Fin N → Euc d) → ℝ}
    (hg : ContDiffOn ℝ 2 g U) {G : Set (Fin N → Euc d)} (hG : IsClosed G) (hGK : Gᶜ ⊆ Kc)
    {C' : ℝ} (hC' : 0 ≤ C') (hgen : ∀ Z ∈ Kc, diffGen D g Z ≤ C')
    {A : Set Ω} (hA : ∀ t : ℝ, MeasurableSet[ℱ t] A) (hAK : ∀ ω ∈ A, Y₀ ω ∈ Kc) :
    ∃ Z : Ω → (Fin N → Euc d), Measurable Z ∧ (∀ ω ∈ A, Z ω ∈ Kc) ∧
      (∀ ω ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ T → solHit τ Y G ω = (t : WithTop ℝ) → Z ω = Y t ω) ∧
      IntegrableOn (fun ω => g (Z ω)) A P ∧ IntegrableOn (fun ω => g (Y₀ ω)) A P ∧
      ∫ ω in A, g (Z ω) ∂P ≤ ∫ ω in A, g (Y₀ ω) ∂P + C' * T * (P A).toReal := by
  classical
  have hY0 : ∀ t : ℝ, Measurable[ℱ t] (Y 0) := by
    have : Y 0 = Y₀ := funext hsol.sol.init
    rw [this]; exact hsol.init_meas
  have hcontY := hsol.sol.cont
  have hexit : ∀ ω, τ ω < ⊤ → ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ω ∧ Y r ω ∈ G := by
    intro ω hω
    obtain ⟨t, ht0, htτ, htK⟩ := hsol.exit ω hω Kc hKc hKfree 0 (by simpa using hsol.pos ω)
    exact ⟨t, ht0.le, htτ, by_contra fun h => htK (hGK h)⟩
  have hρ₀ : IsStoppingTime ℱ (solHit τ Y G) :=
    isStoppingTime_solHit ℱ hsol.stopping hsol.sol.adapted hcontY hG hexit
  have hcontP : ∀ ω (t : ℝ), 0 ≤ t → (t : WithTop ℝ) < τ ω →
      ContinuousOn (fun s => Y s ω) (Set.Icc 0 t) := hcontY
  have hρ₀nn : ∀ ω, (0 : WithTop ℝ) ≤ solHit τ Y G ω := fun ω =>
    pathHit_nonneg hG (hcontP ω)
  -- the stopping time
  set ρ' : Ω → WithTop ℝ := fun ω =>
    if ω ∈ A then min (solHit τ Y G ω) (T : WithTop ℝ) else (((-1 : ℝ)) : WithTop ℝ) with hρ'def
  have hρ'A : ∀ ω ∈ A, ρ' ω = min (solHit τ Y G ω) (T : WithTop ℝ) := fun ω hω => by
    simp [hρ'def, hω]
  have hρ'nA : ∀ ω, ω ∉ A → ρ' ω = (((-1 : ℝ)) : WithTop ℝ) := fun ω hω => by
    simp [hρ'def, hω]
  have hρ' : IsStoppingTime ℱ ρ' := by
    intro t
    have : {ω | ρ' ω ≤ (t : WithTop ℝ)} =
        (A ∩ {ω | min (solHit τ Y G ω) (T : WithTop ℝ) ≤ (t : WithTop ℝ)}) ∪
          (Aᶜ ∩ {_ω | (((-1 : ℝ)) : WithTop ℝ) ≤ (t : WithTop ℝ)}) := by
      ext ω
      by_cases hω : ω ∈ A
      · simp [hρ'A ω hω, hω]
      · simp [hρ'nA ω hω, hω]
    rw [this]
    exact ((hA t).inter ((hρ₀.min_const T) t)).union ((hA t).compl.inter (MeasurableSet.const _))
  have hρ'T : ∀ ω, ρ' ω ≤ (T : WithTop ℝ) := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [hρ'A ω hω]; exact min_le_right _ _
    · rw [hρ'nA ω hω]; exact_mod_cast (by linarith : (-1 : ℝ) ≤ T)
  have hρ'τ : ∀ ω, ρ' ω < τ ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [hρ'A ω hω]
      by_cases hτ : τ ω = ⊤
      · rw [hτ]; exact lt_of_le_of_lt (min_le_right _ _) (WithTop.coe_lt_top T)
      · have hlt : τ ω < ⊤ := lt_top_iff_ne_top.2 hτ
        obtain ⟨r, hr0, hrτ, hrG⟩ := hexit ω hlt
        have := (pathHit_le_iff hG (hcontP ω) r).2 ⟨r, hr0, le_rfl, hrτ, hrG⟩
        exact lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt this hrτ)
    · rw [hρ'nA ω hω]
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (-1 : ℝ) < 0)) (hsol.pos ω).le
  have hρ'nn : ∀ ω ∈ A, (0 : WithTop ℝ) ≤ ρ' ω := fun ω hω => by
    rw [hρ'A ω hω]; exact le_min (hρ₀nn ω) (by exact_mod_cast hT)
  have hYK : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T, (t : WithTop ℝ) ≤ ρ' ω → Y t ω ∈ Kc := by
    intro ω t ht htρ
    by_cases hω : ω ∈ A
    · have htτ : (t : WithTop ℝ) < τ ω := lt_of_le_of_lt htρ (hρ'τ ω)
      rw [hρ'A ω hω] at htρ
      have h0 : (fun s => Y s ω) 0 ∈ Kc := by
        simp only [hsol.sol.init ω]; exact hAK ω hω
      exact pathHit_mem_of_le hG hKc.isClosed hGK (hcontP ω) h0 ht.1
        htτ (htρ.trans (min_le_left _ _))
    · rw [hρ'nA ω hω] at htρ
      exfalso
      have : t ≤ -1 := by exact_mod_cast htρ
      linarith [ht.1]
  obtain ⟨Ψ, hΨ, -, hmain⟩ := ito_along_solution D hK hV hW' hsol hT ρ' hρ' hρ'τ hU Kc hKc hKU
    hKfree hg hYK
  have hprog := isProgressive_stoppedPath ℱ Y hsol.sol.adapted hY0 hρ'
    (fun ω t ht htρ => hcontP ω t ht (lt_of_le_of_lt htρ (hρ'τ ω)))
  set Wp : ℝ → Ω → (Fin N → Euc d) := fun s ω =>
    Set.indicator {ω | (s : WithTop ℝ) ≤ ρ' ω} (fun ω => Y (max s 0) ω) ω with hWp
  have hZmeasT : StronglyMeasurable[ℱ T] (stoppedValue Wp ρ') :=
    stronglyMeasurable_stoppedValue_of_le hprog.isStronglyProgressive hρ' hρ'T
  have hZm : Measurable (stoppedValue Wp ρ') := hZmeasT.measurable.mono (ℱ.le T) le_rfl
  have hZ : ∀ ω ∈ A, ∃ r : ℝ, ρ' ω = (r : WithTop ℝ) ∧ 0 ≤ r ∧ r ≤ T ∧
      stoppedValue Wp ρ' ω = Y r ω := by
    intro ω hω
    have hne : ρ' ω ≠ ⊤ := ne_top_of_le_ne_top (WithTop.coe_ne_top) (hρ'T ω)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
    have hr' : ρ' ω = (r : WithTop ℝ) := hr.symm
    have hr0 : 0 ≤ r := by have := hρ'nn ω hω; rw [hr'] at this; exact_mod_cast this
    have hrT : r ≤ T := by have := hρ'T ω; rw [hr'] at this; exact_mod_cast this
    refine ⟨r, hr', hr0, hrT, ?_⟩
    simp only [stoppedValue, hr', hWp, untopA_coe']
    rw [Set.indicator_of_mem (show ω ∈ {ω | ((r : ℝ) : WithTop ℝ) ≤ ρ' ω} from by
      simp [hr']), max_eq_left hr0]
  have hZK : ∀ ω ∈ A, stoppedValue Wp ρ' ω ∈ Kc := by
    intro ω hω
    obtain ⟨r, hr, hr0, hrT, hZr⟩ := hZ ω hω
    rw [hZr]; exact hYK ω r ⟨hr0, hrT⟩ (by rw [hr])
  refine ⟨stoppedValue Wp ρ', hZm, hZK, ?_, ?_⟩
  · intro ω hω t ht0 htT hhit
    obtain ⟨r, hr, hr0, hrT, hZr⟩ := hZ ω hω
    rw [hρ'A ω hω, hhit, min_eq_left (by exact_mod_cast htT)] at hr
    have : t = r := by exact_mod_cast hr
    rw [hZr, this]
  have hAm : MeasurableSet A := ℱ.le 0 _ (hA 0)
  set u := itoIntegral P ℱ W' Ψ with hu
  have hmart := martingale_stoppedProcess_itoIntegral hW' hΨ hρ'
  have hΨs : IsProgressiveL2 P ℱ (stopIntegrand Ψ ρ') := hΨ.stopIntegrand hρ'
  have hloc := localItoIntegral_eq_itoIntegral hW' hΨs
  have hst := itoIntegral_stopIntegrand hW' hΨ hρ'
  have hae : ∀ᵐ ω ∂P, ω ∈ A → g (stoppedValue Wp ρ' ω) ≤
      g (Y₀ ω) + C' * T + stoppedProcess u ρ' T ω := by
    filter_upwards [hmain, hloc, hst] with ω h1 h2 h3 hω
    obtain ⟨r, hr, hr0, hrT, hZr⟩ := hZ ω hω
    obtain ⟨hint, heq⟩ := h1 r ⟨hr0, hrT⟩ (by rw [hr])
    have hM : localItoIntegral P ℱ W' (stopIntegrand Ψ ρ') r ω = stoppedProcess u ρ' T ω := by
      rw [h2 r, h3 r]
      simp only [stoppedProcess, hr, min_self]
      rw [min_eq_right (by exact_mod_cast hrT : (r : WithTop ℝ) ≤ T)]
    have hbd : ∫ s in Set.Icc 0 r, diffGen D g (Y s ω) ≤ C' * r := by
      have := setIntegral_mono_on hint (integrableOn_const (by simp)) measurableSet_Icc
        (fun s hs => hgen _ (hYK ω s ⟨hs.1, hs.2.trans hrT⟩ (by rw [hr]; exact_mod_cast hs.2)))
      simpa [Measure.real, hr0, mul_comm] using this
    rw [hZr, heq, hM]
    have : C' * r ≤ C' * T := mul_le_mul_of_nonneg_left hrT hC'
    linarith
  have hgc : ContinuousOn g Kc := hg.continuousOn.mono hKU
  set gm : (Fin N → Euc d) → ℝ := Kc.piecewise g (fun _ => 0) with hgm
  have hgm_meas : Measurable gm :=
    ContinuousOn.measurable_piecewise hgc continuousOn_const hKc.isClosed.measurableSet
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hgc
  have hgm_bd : ∀ x, ‖gm x‖ ≤ max B 0 := by
    intro x
    by_cases hx : x ∈ Kc
    · rw [hgm, Set.piecewise_eq_of_mem _ _ _ hx]; exact (hB x hx).trans (le_max_left _ _)
    · rw [hgm, Set.piecewise_eq_of_notMem _ _ _ hx]; simp
  have hY₀m : Measurable Y₀ := (hsol.init_meas 0).mono (ℱ.le 0) le_rfl
  have hint1 : Integrable (fun ω => gm (stoppedValue Wp ρ' ω)) P :=
    Integrable.of_bound (hgm_meas.comp hZm).aestronglyMeasurable (max B 0)
      (ae_of_all _ fun ω => hgm_bd _)
  have hint0 : Integrable (fun ω => gm (Y₀ ω)) P :=
    Integrable.of_bound (hgm_meas.comp hY₀m).aestronglyMeasurable (max B 0)
      (ae_of_all _ fun ω => hgm_bd _)
  have hintM : Integrable (stoppedProcess u ρ' T) P := hmart.integrable T
  have h1 : ∫ ω in A, g (stoppedValue Wp ρ' ω) ∂P = ∫ ω in A, gm (stoppedValue Wp ρ' ω) ∂P :=
    setIntegral_congr_fun hAm fun ω hω => by
      simp only [hgm, Set.piecewise_eq_of_mem _ _ _ (hZK ω hω)]
  have h2 : ∫ ω in A, g (Y₀ ω) ∂P = ∫ ω in A, gm (Y₀ ω) ∂P :=
    setIntegral_congr_fun hAm fun ω hω => by
      simp only [hgm, Set.piecewise_eq_of_mem _ _ _ (hAK ω hω)]
  have hM0 : ∫ ω in A, stoppedProcess u ρ' T ω ∂P = 0 := by
    rw [← hmart.setIntegral_eq hT (hA 0)]
    have : ∀ ω ∈ A, stoppedProcess u ρ' 0 ω = 0 := by
      intro ω hω
      simp only [stoppedProcess]
      rw [min_eq_left (by simpa using hρ'nn ω hω)]
      simpa [hu] using itoIntegral_of_nonpos P ℱ W' Ψ (le_refl (0 : ℝ)) ω
    rw [setIntegral_congr_fun hAm this]; simp
  have hae' : ∀ᵐ ω ∂P.restrict A, gm (stoppedValue Wp ρ' ω) ≤
      gm (Y₀ ω) + C' * T + stoppedProcess u ρ' T ω := by
    rw [ae_restrict_iff' hAm]
    filter_upwards [hae] with ω hω hωA
    have := hω hωA
    simpa only [hgm, Set.piecewise_eq_of_mem _ _ _ (hZK ω hωA),
      Set.piecewise_eq_of_mem _ _ _ (hAK ω hωA)] using this
  have e1 : Integrable (fun ω => gm (Y₀ ω) + C' * T) P := hint0.add (integrable_const _)
  have e2 : Integrable (fun ω => gm (Y₀ ω) + C' * T + stoppedProcess u ρ' T ω) P := e1.add hintM
  refine ⟨hint1.integrableOn.congr_fun (fun ω hω => (by
      simp only [hgm, Set.piecewise_eq_of_mem _ _ _ (hZK ω hω)] : gm _ = g _)) hAm,
    hint0.integrableOn.congr_fun (fun ω hω => (by
      simp only [hgm, Set.piecewise_eq_of_mem _ _ _ (hAK ω hω)] : gm _ = g _)) hAm, ?_⟩
  rw [h1, h2]
  calc ∫ ω in A, gm (stoppedValue Wp ρ' ω) ∂P
      ≤ ∫ ω in A, (gm (Y₀ ω) + C' * T + stoppedProcess u ρ' T ω) ∂P :=
        setIntegral_mono_ae_restrict hint1.integrableOn
          e2.integrableOn hae'
    _ = ∫ ω in A, gm (Y₀ ω) ∂P + C' * T * (P A).toReal := by
        rw [integral_add e1.integrableOn hintM.integrableOn,
          integral_add hint0.integrableOn (integrable_const (C' * T)).integrableOn, hM0,
          setIntegral_const]
        simp [Measure.real, mul_comm]

end StoppedEstimate

section PathEventually

variable {d N : ℕ}

/-- A compact piece of a collision-free path is bounded and uniformly separated. -/
theorem path_uniform_bounds {y : ℝ → (Fin N → Euc d)} {t : ℝ}
    (hcont : ContinuousOn y (Set.Icc 0 t)) (hfree : ∀ s ∈ Set.Icc (0 : ℝ) t, y s ∈ liftedFree d N) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ s ∈ Set.Icc (0 : ℝ) t, ‖y s‖ < (n : ℝ) + 1 ∧
      ∀ i j, i ≠ j → 1 / ((n : ℝ) + 1) < pairSep (y s) i j := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hcont
  have hinv : ContinuousOn (fun s => ∑ p : Fin N × Fin N,
      if p.1 ≠ p.2 then (pairSep (y s) p.1 p.2)⁻¹ else 0) (Set.Icc 0 t) := by
    refine continuousOn_finset_sum _ fun p _ => ?_
    by_cases hp : p.1 ≠ p.2
    · simp only [hp, ne_eq, not_false_eq_true, if_true]
      refine ContinuousOn.inv₀ ?_ fun s hs => (pairSep_pos (hfree s hs) hp).ne'
      exact (continuous_pairSep p.1 p.2).comp_continuousOn hcont
    · simp [hp]; exact continuousOn_const
  obtain ⟨B', hB'⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn hinv
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max B (max B' 0) + 1)
  refine ⟨n₀, fun n hn s hs => ⟨?_, fun i j hij => ?_⟩⟩
  · have h1 := hB s hs
    have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have := le_max_left B (max B' 0)
    linarith
  · have hpos := pairSep_pos (hfree s hs) hij
    have hle : (pairSep (y s) i j)⁻¹ ≤ B' := by
      have hterm : (pairSep (y s) i j)⁻¹ ≤ ∑ p : Fin N × Fin N,
          if p.1 ≠ p.2 then (pairSep (y s) p.1 p.2)⁻¹ else 0 := by
        have := Finset.single_le_sum (f := fun p : Fin N × Fin N =>
          if p.1 ≠ p.2 then (pairSep (y s) p.1 p.2)⁻¹ else 0)
          (fun p _ => by
            by_cases hp : p.1 ≠ p.2
            · simp only [hp, ne_eq, not_false_eq_true, if_true]
              exact (inv_pos.2 (pairSep_pos (hfree s hs) hp)).le
            · simp [hp]) (Finset.mem_univ (i, j))
        simpa [hij] using this
      exact hterm.trans ((le_abs_self _).trans (by simpa using hB' s hs))
    have hn' : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
    have hB'pos : B' < (n : ℝ) + 1 := by
      have := le_max_left B' 0
      have := le_max_right B (max B' 0)
      linarith [le_max_right B' 0, le_max_left B (max B' 0)]
    have : (pairSep (y s) i j)⁻¹ < (n : ℝ) + 1 := lt_of_le_of_lt hle hB'pos
    rw [one_div]
    exact (inv_lt_comm₀ hpos (by positivity)).1 this


/-- The deterministic eventuality: if the path reaches `{Q_I ≤ a}` by time `T` before any
one-point enlargement reaches `δ`, then for all large `n` it starts in `K_n` and its first
hitting time of `G_n` is a time `≤ T` at which `Q_I ≤ a`. -/
theorem reach_eventually {τ : WithTop ℝ} {y : ℝ → (Fin N → Euc d)} (I : Finset (Fin N))
    {a δ q₁ T : ℝ} (haq : a ≤ q₁)
    (hcont : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → ContinuousOn y (Set.Icc 0 t))
    (hfree : ∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < τ → y t ∈ liftedFree d N)
    (hq : q₁ ≤ clusterDispersionLift I (y 0))
    (hreach : ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ (t : WithTop ℝ) < τ ∧ clusterDispersionLift I (y t) ≤ a ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ t → ∀ j, j ∉ I → δ < clusterDispersionLift (insert j I) (y s)) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → y 0 ∈ barrierK I a δ n ∧
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ T ∧ pathHit τ y (barrierG I a δ n) = (r : WithTop ℝ) ∧
        clusterDispersionLift I (y r) ≤ a := by
  obtain ⟨t, ht0, htT, htτ, hQt, hδ⟩ := hreach
  have hc := hcont t ht0 htτ
  have hf : ∀ s ∈ Set.Icc (0 : ℝ) t, y s ∈ liftedFree d N := fun s hs =>
    hfree s hs.1 (lt_of_le_of_lt (by exact_mod_cast hs.2) htτ)
  obtain ⟨n₀, hn₀⟩ := path_uniform_bounds hc hf
  set S : Set ℝ := Set.Icc 0 t ∩ (fun s => clusterDispersionLift I (y s)) ⁻¹' Set.Iic a with hS
  have hQc : ContinuousOn (fun s => clusterDispersionLift I (y s)) (Set.Icc 0 t) :=
    (continuous_clusterDispersionLift I).comp_continuousOn hc
  have hScl : IsClosed S := hQc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset hScl Set.inter_subset_left
  have hSne : S.Nonempty := ⟨t, ⟨ht0, le_rfl⟩, hQt⟩
  set ts := sInf S with hts
  have htsS : ts ∈ S := hSc.sInf_mem hSne
  have hts_le : ∀ r ∈ S, ts ≤ r := fun r hr => csInf_le hSc.bddBelow hr
  have hts0 : 0 ≤ ts := htsS.1.1
  have htst : ts ≤ t := htsS.1.2
  have htsτ : (ts : WithTop ℝ) < τ := lt_of_le_of_lt (by exact_mod_cast htst) htτ
  refine ⟨n₀, fun n hn => ?_⟩
  have hbd := hn₀ n hn
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht0⟩
  refine ⟨⟨⟨⟨?_, fun i j hij => (hbd 0 h0).2 i j hij |>.le⟩, haq.trans hq⟩,
    fun j hj => (hδ 0 le_rfl ht0 j hj).le⟩, ?_⟩
  · rw [mem_closedBall_zero_iff]; exact (hbd 0 h0).1.le
  have hGcl := isClosed_barrierG (d := d) I a δ n
  have hyG : y ts ∈ barrierG (d := d) I a δ n := Or.inl (Or.inl (Or.inl htsS.2))
  obtain ⟨r₀, hr₀, hr₀0, hr₀τ, hr₀G, hmin⟩ := pathHit_spec hGcl hcont ⟨ts, hts0, htsτ, hyG⟩
  have hr₀le : r₀ ≤ ts := hmin ts hts0 htsτ hyG
  have hr₀eq : r₀ = ts := by
    refine le_antisymm hr₀le ?_
    by_contra hlt
    push_neg at hlt
    have hmem : r₀ ∈ Set.Icc (0 : ℝ) t := ⟨hr₀0, hr₀le.trans htst⟩
    have hnS : r₀ ∉ S := fun hr => absurd (hts_le r₀ hr) (not_le.2 hlt)
    have hQ : a < clusterDispersionLift I (y r₀) := by
      by_contra hh; exact hnS ⟨hmem, not_lt.1 hh⟩
    obtain ⟨hb1, hb2⟩ := hbd r₀ hmem
    rcases hr₀G with ((h1 | h2) | h3) | h4
    · exact absurd h1 (not_le.2 hQ)
    · obtain ⟨j, hj, hjle⟩ := h2
      exact absurd hjle (not_le.2 (hδ r₀ hr₀0 hmem.2 j hj))
    · exact absurd h3 (not_le.2 hb1)
    · obtain ⟨i, j, hij, hle⟩ := h4
      exact absurd hle (not_le.2 (hb2 i j hij))
  refine ⟨ts, hts0, htst.trans htT, ?_, htsS.2.out⟩
  rw [hr₀, hr₀eq]

end PathEventually

section LevelEstimate

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

/-- The level estimate for the logarithmic barrier: with `m = -log (q/2)` the minimum of `Φ`,
`(Φ(a) - m) P(B) ≤ Φ(q₁ ∧ q/2) - m + C' T`, where `B` contains the event that
the process starts in `K_n ∩ {Q_I ≥ q₁}` and its `G_n`-hitting time is `≤ T` with `Q_I ≤ a` there. -/
theorem barrier_level_estimate [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (I : Finset (Fin N)) (hI : 2 ≤ I.card)
    {q C' : ℝ} (hq : 0 < q) (hC' : 0 ≤ C') {δ : ℝ}
    (hgen : ∀ Z : Fin N → Euc d, (∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z) →
      Z ∈ liftedFree d N → diffGen D (barrierPhi q ∘ clusterDispersionLift I) Z ≤ C')
    {T : ℝ} (hT : 0 ≤ T) {a q₁ : ℝ} (ha : 0 < a) (hq₁ : 0 < q₁) (n : ℕ) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ ω, Y₀ ω ∈ barrierK I a δ n → q₁ ≤ clusterDispersionLift I (Y₀ ω) →
        (∃ r : ℝ, 0 ≤ r ∧ r ≤ T ∧ solHit τ Y (barrierG I a δ n) ω = (r : WithTop ℝ) ∧
          clusterDispersionLift I (Y r ω) ≤ a) → ω ∈ B) ∧
      (barrierPhi q a + Real.log (q / 2)) * (P B).toReal ≤
        barrierPhi q (min q₁ (q / 2)) + Real.log (q / 2) + C' * T := by
  classical
  set Kc := barrierK (d := d) I a δ n with hKc_def
  set G := barrierG (d := d) I a δ n with hG_def
  have hKc : IsCompact Kc := isCompact_barrierK I a δ n
  have hG : IsClosed G := isClosed_barrierG I a δ n
  have hGK : Gᶜ ⊆ Kc := barrierG_compl_subset I a δ n
  have hKfree : Kc ⊆ liftedFree d N := barrierK_subset_free I a δ n
  set Φ := barrierPhi q with hΦdef
  set Q := clusterDispersionLift (d := d) (N := N) I with hQdef
  have hQc : Continuous Q := continuous_clusterDispersionLift I
  have hU : IsOpen {Z : Fin N → Euc d | 0 < Q Z} := isOpen_lt continuous_const hQc
  have hKU : Kc ⊆ {Z | 0 < Q Z} := barrierK_subset_pos I ha δ n
  have hg : ContDiffOn ℝ 2 (Φ ∘ Q) {Z | 0 < Q Z} :=
    (barrierPhi_contDiffOn hq).comp (contDiff_two_clusterDispersionLift I).contDiffOn
      (fun Z hZ => hZ)
  have hgenK : ∀ Z ∈ Kc, diffGen D (Φ ∘ Q) Z ≤ C' := fun Z hZ => hgen Z hZ.2 (hKfree hZ)
  set A : Set Ω := Y₀ ⁻¹' (Kc ∩ {Z | q₁ ≤ Q Z}) with hAdef
  have hA : ∀ t : ℝ, MeasurableSet[ℱ t] A := fun t =>
    (hsol.init_meas t) ((hKc.isClosed.inter (isClosed_le continuous_const hQc)).measurableSet)
  have hAK : ∀ ω ∈ A, Y₀ ω ∈ Kc := fun ω hω => hω.1
  obtain ⟨Z, hZm, hZK, hZhit, hintZ, hint0, hineq⟩ := stopped_estimate D hK hV hW' hsol hT hU Kc hKc
    hKU hKfree hg hG hGK hC' hgenK hA hAK
  have hAm : MeasurableSet A := ℱ.le 0 _ (hA 0)
  set R : Set Ω := Z ⁻¹' {W | Q W ≤ a} with hR
  have hRm : MeasurableSet R := hZm (isClosed_le hQc continuous_const).measurableSet
  refine ⟨A ∩ R, hAm.inter hRm, ?_, ?_⟩
  · intro ω h1 h2 ⟨r, hr0, hrT, hhit, hQ⟩
    have hωA : ω ∈ A := ⟨h1, h2⟩
    refine ⟨hωA, ?_⟩
    show Q (Z ω) ≤ a
    rw [hZhit ω hωA r hr0 hrT hhit]; exact hQ
  set m : ℝ := -Real.log (q / 2) with hm
  have hmle : ∀ x, 0 < x → m ≤ Φ x := fun x hx => barrierPhi_ge hq hx
  set c := Φ a - m with hc
  have hc0 : 0 ≤ c := by have := hmle a ha; linarith
  have hanti := barrierPhi_antitoneOn hq
  have hQZpos : ∀ ω ∈ A, 0 < Q (Z ω) := fun ω hω => hKU (hZK ω hω)
  -- lower bound
  have hfint : Integrable (fun ω => m + R.indicator (fun _ => c) ω) P :=
    (integrable_const m).add ((integrable_const c).indicator hRm)
  have hlow : ∫ ω in A, (m + R.indicator (fun _ => c) ω) ∂P ≤ ∫ ω in A, (Φ ∘ Q) (Z ω) ∂P := by
    refine setIntegral_mono_on hfint.integrableOn hintZ hAm fun ω hω => ?_
    by_cases hωR : ω ∈ R
    · rw [Set.indicator_of_mem hωR]
      have : Φ a ≤ Φ (Q (Z ω)) := hanti (show Q (Z ω) ∈ Set.Ioi 0 from hQZpos ω hω)
        (show a ∈ Set.Ioi 0 from ha) hωR
      simp only [hc, Function.comp]; linarith
    · rw [Set.indicator_of_notMem hωR]
      simpa using hmle _ (hQZpos ω hω)
  have hlow' : ∫ ω in A, (m + R.indicator (fun _ => c) ω) ∂P =
      m * (P A).toReal + c * (P (A ∩ R)).toReal := by
    rw [integral_add (integrable_const m).integrableOn
      ((integrable_const c).indicator hRm).integrableOn, setIntegral_const,
      setIntegral_indicator hRm, setIntegral_const]
    simp [Measure.real, mul_comm]
  -- upper bound on the initial value
  set c₁ := Φ (min q₁ (q / 2)) with hc₁
  have hmin0 : 0 < min q₁ (q / 2) := lt_min hq₁ (by linarith)
  have hupp : ∫ ω in A, (Φ ∘ Q) (Y₀ ω) ∂P ≤ c₁ * (P A).toReal := by
    have : ∫ ω in A, (Φ ∘ Q) (Y₀ ω) ∂P ≤ ∫ ω in A, c₁ ∂P := by
      refine setIntegral_mono_on hint0 (integrableOn_const (by simp)) hAm fun ω hω => ?_
      have hQ : min q₁ (q / 2) ≤ Q (Y₀ ω) := (min_le_left _ _).trans hω.2
      exact hanti (show min q₁ (q / 2) ∈ Set.Ioi 0 from hmin0)
        (show Q (Y₀ ω) ∈ Set.Ioi 0 from lt_of_lt_of_le hmin0 hQ) hQ
    simpa [Measure.real, mul_comm] using this
  have hc₁m : m ≤ c₁ := hmle _ hmin0
  have hX1 : (P A).toReal ≤ 1 := measureReal_le_one
  have hX0 : 0 ≤ (P A).toReal := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ c₁ - m + C' * T := by have := mul_nonneg hC' hT; linarith
  have hfin : c * (P (A ∩ R)).toReal ≤ (c₁ - m + C' * T) * (P A).toReal := by
    have h1 := hlow.trans hineq
    rw [hlow'] at h1
    have : C' * T * (P A).toReal = C' * T * (P A).toReal := rfl
    nlinarith [hupp]
  have : (c₁ - m + C' * T) * (P A).toReal ≤ c₁ - m + C' * T :=
    mul_le_of_le_one_right hK0 hX1
  simp only [hc, hm, hc₁] at hfin this ⊢
  linarith

end LevelEstimate

end ClusterBarrier

open ClusterBarrier

/-- Lemma `B:lem:cluster-ito`, the Itô equation `B:eq:cluster-ito` (M L11784-11788), before
`τ_⋆` and below the cluster radius.  Let `ρ < τ` be a stopping time and `K ⊆ liftedFree d N` a
compact set on which `Q_I < clusterRadius I`, such that the path stays in `K` on `[0, T]` up to
`ρ`.  Then there is a progressively measurable square-integrable integrand `Ψ` which agrees with
the noise coefficient `s ↦ D Q_I(Y_s)[σ_k]` (`clusterNoiseIntegrand`) on `[0, T]` up to `ρ`, and
a.s. for all `t ∈ [0, T]` with `t ≤ ρ`,
`Q_I(Y_t) = Q_I(Y_0) + ∫_0^t (2d(k-1)/β + 𝒜_I + ℛ_I)(Y_s) ds + ℳ_I(t)`, where `ℳ_I` is the
local Itô integral of `Ψ` stopped at `ρ`; its quadratic-variation density is `(8/β) Q_I` by
`cluster_qv`.

The martingale part is stated through such a `Ψ` rather than through `clusterNoiseIntegrand`
itself because `IsMaximalParticleSolution` constrains `Y` only on `[0, τ)`: off that interval
`clusterNoiseIntegrand D I Y` need not be progressively measurable, and the local Itô integral of
a non-progressive integrand is a junk value.  The hypotheses `hK`, `hV` are the standing
hypotheses of Proposition B.1 (continuity of the drift on the collision-free region). -/
theorem cluster_ito_equation [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → (Fin N → Euc d)}
    {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (I : Finset (Fin N)) {T : ℝ} (hT : 0 ≤ T) (ρ : Ω → WithTop ℝ) (hρ : IsStoppingTime ℱ ρ)
    (hρτ : ∀ ω, ρ ω < τ ω) (K : Set (Fin N → Euc d)) (hKc : IsCompact K)
    (hKU : K ⊆ liftedFree d N) (hKq : ∀ Z ∈ K, clusterDispersionLift I Z < clusterRadius I)
    (hYK : ∀ ω, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ ρ ω → Y t ω ∈ K) :
    ∃ Ψ : ℝ → Ω → (Fin N × Fin d) → ℝ, IsProgressiveL2 P ℱ Ψ ∧
      (∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → s ≤ T → (s : WithTop ℝ) ≤ ρ ω → ∀ k,
        Ψ s ω k = clusterNoiseIntegrand D I Y s ω k) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ ρ ω →
        IntegrableOn (fun s => clusterGenerator D I (Y s ω)) (Set.Icc 0 t) ∧
        clusterDispersionLift I (Y t ω) = clusterDispersionLift I (Y₀ ω) +
          (∫ s in Set.Icc 0 t, (2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ +
            clusterInternal D I (Y s ω) + clusterRemainder D I (Y s ω))) +
          localItoIntegral P ℱ W' (stopIntegrand Ψ ρ) t ω := by
  obtain ⟨Ψ, hΨ, hΨeq, hito⟩ := ito_along_solution D hK hV hW' hsol hT ρ hρ hρτ isOpen_univ K
    hKc (Set.subset_univ K) hKU (((contDiff_clusterDispersionLift I).of_le
      (WithTop.coe_le_coe.2 le_top)).contDiffOn) hYK
  refine ⟨Ψ, hΨ, hΨeq, ?_⟩
  filter_upwards [hito] with ω hω t ht htρ
  obtain ⟨hint, heq⟩ := hω t ht htρ
  have hfun : (fun s => 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ + clusterInternal D I (Y s ω) +
      clusterRemainder D I (Y s ω)) = fun s => diffGen D (clusterDispersionLift I) (Y s ω) := by
    funext s
    simp only [clusterRemainder, clusterGenerator_eq_diffGen]
    ring
  refine ⟨by simpa only [clusterGenerator_eq_diffGen] using hint, ?_⟩
  rw [hfun]
  exact heq

/-- The hitting-probability estimate `B:eq:cluster-hitting-probability` (M L11889-11892), with
the random initial configuration localised to `{Q_I(Y₀) ≥ q₁}` (an `ℱ_0`-measurable event):
`P(Q_I(Y₀) ≥ q₁, σ_{I,a} ≤ T ∧ η_{I,δ} ∧ τ) ≤ C(I,δ,T,q₁)/|log a|` for `0 < a < a₀`.  Valid when
`d(k-1) ≥ 2` or `invβ = 0` (the only use of `d(k-1) ≥ 2` is the sign of the diffusion
contribution `(4 - 2d(k-1)) invβ / Q_I` in `B:eq:cluster-log-generator`, M L11867-11872).
Proof: the barrier `Φ` of M L11863, `cluster_ito_equation` up to
`T ∧ η_{I,δ} ∧ σ_{I,a} ∧ τ_n`, `clusterInternal_nonneg`, `clusterRemainder_bound`, the
set-integral form of optional stopping on `{Q_I(Y₀) ≥ q₁}` for the stopped `L²` martingale, and
monotone convergence in `n`. -/
theorem cluster_hitting_probability [IsProbabilityMeasure P] (D : DynData d)
    (hK : KernelLocal d D.s) (hM : Torus.SymNonpos D.M) (hV : Torus.IsCk 2 D.V)
    (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ}
    {Y : ℝ → Ω → (Fin N → Euc d)} (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (I : Finset (Fin N)) (hI : 2 ≤ I.card) (hdk : D.invβ = 0 ∨ 2 ≤ d * (I.card - 1))
    (δ : ℝ) (hδ : 0 < δ) (q₁ : ℝ) (hq₁ : 0 < q₁) (T : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ →
      P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ≤
        ENNReal.ofReal (C / |Real.log a|) := by
  classical
  obtain ⟨q, C₀, hq, hqr, hC₀, hrem⟩ := clusterRemainder_bound D hK hV I hI δ hδ
  obtain ⟨C', hC'0, hC'⟩ := barrier_generator_bound D hM I hdk hI hq hqr hC₀
    {Z | ∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z}
    (fun Y hYS hYf hYq => hrem Y hYf hYq hYS)
  have hgen : ∀ Z : Fin N → Euc d, (∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z) →
      Z ∈ liftedFree d N → diffGen D (barrierPhi q ∘ clusterDispersionLift I) Z ≤ C' :=
    fun Z hZS hZf => hC' Z hZS hZf
  set T' := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  set m : ℝ := Real.log (q / 2) with hm
  set Kb : ℝ := barrierPhi q (min q₁ (q / 2)) + m + C' * T' with hKb
  have hmin0 : 0 < min q₁ (q / 2) := lt_min hq₁ (by linarith)
  have hKb0 : 0 ≤ Kb := by
    have h1 : -Real.log (q / 2) ≤ barrierPhi q (min q₁ (q / 2)) := barrierPhi_ge hq hmin0
    have := mul_nonneg hC'0 hT'0
    simp only [hKb, hm]; linarith
  refine ⟨min (q / 4) (min q₁ (Real.exp (-(2 * |m|)))), 2 * Kb, ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min hq₁ (Real.exp_pos _))
  intro a ha hlt
  have haq : a < q / 4 := lt_of_lt_of_le hlt (min_le_left _ _)
  have haq₁ : a < q₁ := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have hae : a < Real.exp (-(2 * |m|)) :=
    lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : Real.log a < -(2 * |m|) := by
    rw [Real.log_lt_iff_lt_exp ha]; exact hae
  have hlogneg : Real.log a < 0 := by have := abs_nonneg m; linarith
  have habs : |Real.log a| = -Real.log a := abs_of_neg hlogneg
  have hΦa : barrierPhi q a = -Real.log a := barrierPhi_of_le hq haq.le
  have hca : |Real.log a| / 2 ≤ barrierPhi q a + m := by
    rw [hΦa, habs]
    have := neg_abs_le m
    have := le_abs_self m
    linarith
  have hca0 : 0 < barrierPhi q a + m := lt_of_lt_of_le (by rw [habs]; linarith) hca
  -- level estimates
  have hB : ∀ n : ℕ, ∃ B : Set Ω, MeasurableSet B ∧
      (∀ ω, Y₀ ω ∈ barrierK I a δ n → q₁ ≤ clusterDispersionLift I (Y₀ ω) →
        (∃ r : ℝ, 0 ≤ r ∧ r ≤ T' ∧ solHit τ Y (barrierG I a δ n) ω = (r : WithTop ℝ) ∧
          clusterDispersionLift I (Y r ω) ≤ a) → ω ∈ B) ∧
      (barrierPhi q a + Real.log (q / 2)) * (P B).toReal ≤
        barrierPhi q (min q₁ (q / 2)) + Real.log (q / 2) + C' * T' := fun n =>
    barrier_level_estimate D hK hV hW' hsol I hI hq hC'0 hgen hT'0 ha hq₁ n
  choose B hBm hBsub hBest using hB
  have hPB : ∀ n, P (B n) ≤ ENNReal.ofReal (2 * Kb / |Real.log a|) := by
    intro n
    have h1 : (P (B n)).toReal ≤ 2 * Kb / |Real.log a| := by
      have hlogpos : 0 < |Real.log a| := by rw [habs]; linarith
      rw [le_div_iff₀ hlogpos]
      have h2 := hBest n
      have h3 : (P (B n)).toReal * (|Real.log a| / 2) ≤
          (P (B n)).toReal * (barrierPhi q a + m) :=
        mul_le_mul_of_nonneg_left hca ENNReal.toReal_nonneg
      nlinarith
    calc P (B n) = ENNReal.ofReal (P (B n)).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h1
  -- the event is contained in the liminf
  have hsub : {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ⊆
      ⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n := by
    rintro ω ⟨hq0, t, ht0, htT, htτ, hQt, hδt⟩
    have hY0 : Y 0 ω = Y₀ ω := hsol.sol.init ω
    obtain ⟨n₀, hn₀⟩ := reach_eventually (τ := τ ω) (y := fun t => Y t ω) I (δ := δ) (q₁ := q₁)
      (T := T') haq₁.le (hsol.sol.cont ω) (hsol.mem ω) (by simpa [hY0] using hq0)
      ⟨t, ht0, htT.trans (le_max_left _ _), htτ, hQt, hδt⟩
    refine Set.mem_iUnion.2 ⟨n₀, Set.mem_iInter₂.2 fun n hn => ?_⟩
    obtain ⟨hK0, r, hr0, hrT, hhit, hQr⟩ := hn₀ n hn
    exact hBsub n ω (by simpa [hY0] using hK0) hq0 ⟨r, hr0, hrT, hhit, hQr⟩
  have hmono : Monotone fun n₀ : ℕ => ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n := by
    intro k l hkl
    exact Set.iInter₂_mono' fun n hn => ⟨n, hkl.trans hn, subset_rfl⟩
  calc P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω}
      ≤ P (⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n) := measure_mono hsub
    _ = ⨆ n₀ : ℕ, P (⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal (2 * Kb / |Real.log a|) := by
        refine iSup_le fun n₀ => ?_
        exact (measure_mono (Set.iInter₂_subset n₀ le_rfl)).trans (hPB n₀)

namespace ClusterBarrier

section Barrier

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

theorem cluster_barrier_of_hdk [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hM : Torus.SymNonpos D.M) (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (I : Finset (Fin N)) (hI : 2 ≤ I.card)
    (hdk : D.invβ = 0 ∨ 2 ≤ d * (I.card - 1))
    (hind : ∀ J : Finset (Fin N), I ⊂ J → J.card = I.card + 1 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse I T τ Y ω} = 0 := by
  classical
  set F : ℝ → Set Ω := fun δ => {ω | ∃ s : ℝ, 0 ≤ s ∧ s < T ∧ (s : WithTop ℝ) < τ ω ∧
    ∃ j, j ∉ I ∧ clusterDispersionLift (insert j I) (Y s ω) ≤ δ} with hF
  set X : ℕ → Set Ω := fun k => {ω | ClusterCollapse I T τ Y ω ∧
    1 / ((k : ℝ) + 1) ≤ clusterDispersionLift I (Y₀ ω)} with hX
  -- Step A
  have hA : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → P (X k ∩ (F δ)ᶜ) = 0 := by
    intro k δ hδ
    obtain ⟨a₀, C, ha₀, hC⟩ := cluster_hitting_probability D hK hM hV hW' hsol I hI hdk δ hδ
      (1 / ((k : ℝ) + 1)) (by positivity) T
    have hsub : ∀ a : ℝ, 0 < a → X k ∩ (F δ)ᶜ ⊆
        {ω | 1 / ((k : ℝ) + 1) ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} := by
      intro a ha ω ⟨⟨hcol, hq0⟩, hnF⟩
      refine ⟨hq0, ?_⟩
      obtain ⟨t, ht0, htT, htτ, hQt⟩ := hcol a ha
      refine ⟨t, ht0, htT.le, htτ, hQt.le, fun s hs0 hst j hj => ?_⟩
      by_contra hle
      push_neg at hle
      exact hnF ⟨s, hs0, lt_of_le_of_lt hst htT,
        lt_of_le_of_lt (by exact_mod_cast hst) htτ, j, hj, hle⟩
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (-Real.log a₀)
    have hev : ∀ n : ℕ, n₀ ≤ n → P (X k ∩ (F δ)ᶜ) ≤ ENNReal.ofReal (C / (n : ℝ)) := by
      intro n hn
      have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      have hlt : Real.exp (-(n : ℝ)) < a₀ := by
        rw [← Real.lt_log_iff_exp_lt ha₀]; linarith
      have := hC _ (Real.exp_pos _) hlt
      rw [Real.log_exp, abs_neg, Nat.abs_cast] at this
      exact (measure_mono (hsub _ (Real.exp_pos _))).trans this
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (C / (n : ℝ))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat C)
      simpa using this
    exact le_antisymm (ge_of_tendsto htend (Filter.eventually_atTop.2 ⟨n₀, hev⟩)) bot_le
  -- Step B
  have hB : ∀ k : ℕ, X k ⊆ (⋃ j ∈ ({j | j ∉ I} : Set (Fin N)),
        {ω | ClusterCollapse (insert j I) T τ Y ω}) ∪ ⋃ l : ℕ, X k ∩ (F (1 / ((l : ℝ) + 1)))ᶜ := by
    intro k ω hω
    by_cases hcol : ω ∈ ⋃ j ∈ ({j | j ∉ I} : Set (Fin N)), {ω | ClusterCollapse (insert j I) T τ Y ω}
    · exact Or.inl hcol
    right
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcol
    have hnc : ∀ j, ∃ ε : ℝ, 0 < ε ∧ (j ∉ I → ∀ t : ℝ, 0 ≤ t → t < T → (t : WithTop ℝ) < τ ω →
        ε ≤ clusterDispersionLift (insert j I) (Y t ω)) := by
      intro j
      by_cases hj : j ∈ I
      · exact ⟨1, one_pos, fun h => absurd hj h⟩
      · have := hcol j hj
        unfold ClusterCollapse at this
        push_neg at this
        obtain ⟨ε, hε, h⟩ := this
        exact ⟨ε, hε, fun _ t h0 h1 h2 => h t h0 h1 h2⟩
    choose ε hε0 hε using hnc
    set ε₀ : ℝ := (1 + ∑ j, 1 / ε j)⁻¹ with hε₀
    have hS : 0 ≤ ∑ j, 1 / ε j := Finset.sum_nonneg fun j _ => (one_div_pos.2 (hε0 j)).le
    have hε₀pos : 0 < ε₀ := inv_pos.2 (by linarith)
    have hε₀le : ∀ j, ε₀ ≤ ε j := by
      intro j
      have h1 : 1 / ε j ≤ ∑ j, 1 / ε j :=
        Finset.single_le_sum (f := fun j => 1 / ε j) (fun j _ => (one_div_pos.2 (hε0 j)).le)
          (Finset.mem_univ j)
      rw [hε₀]
      have : (1 + ∑ j, 1 / ε j)⁻¹ ≤ (1 / ε j)⁻¹ := inv_anti₀ (one_div_pos.2 (hε0 j)) (by linarith)
      simpa using this
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt hε₀pos
    refine Set.mem_iUnion.2 ⟨l, hω, ?_⟩
    rintro ⟨s, hs0, hsT, hsτ, j, hj, hle⟩
    have := hε j hj s hs0 hsT hsτ
    linarith [hε₀le j]
  -- conclusion
  have hk : {ω | ClusterCollapse I T τ Y ω} ⊆ ⋃ k : ℕ, X k := by
    intro ω hω
    have hfree : Y₀ ω ∈ liftedFree d N := by
      have := hsol.mem ω 0 le_rfl (by simpa using hsol.pos ω)
      rwa [hsol.sol.init ω] at this
    have hpos := clusterDispersionLift_pos hI hfree
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact Set.mem_iUnion.2 ⟨k, hω, hk.le⟩
  refine measure_mono_null hk (measure_iUnion_null fun k => ?_)
  refine measure_mono_null (hB k) (measure_union_null ?_ (measure_iUnion_null fun l => ?_))
  · refine measure_biUnion_null_iff (Set.to_countable _) |>.2 fun j hj => ?_
    exact hind (insert j I) (Finset.ssubset_insert hj) (Finset.card_insert_of_notMem hj) T
  · exact hA k _ (by positivity)

end Barrier

end ClusterBarrier

/-- Lemma `B:lem:cluster-barrier` (M L11849-11856): if `d(k-1) ≥ 2` and no strict one-point
enlargement of `I` collapses before `T ∧ τ` (for every `T`), then `I` does not collapse before
`T ∧ τ`.  Proof: `cluster_hitting_probability` with `a ↓ 0` (M L11893) and then `δ ↓ 0` through
the decreasing events `E_δ = {η_{I,δ} < T ∧ τ}`, whose intersection is contained in the union
of the collapse events of the finitely many enlargements (M L11895-11903). -/
theorem cluster_barrier [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hM : Torus.SymNonpos D.M) (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (I : Finset (Fin N)) (hI : 2 ≤ I.card)
    (hdk : 2 ≤ d * (I.card - 1))
    (hind : ∀ J : Finset (Fin N), I ⊂ J → J.card = I.card + 1 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse I T τ Y ω} = 0 := by
  exact cluster_barrier_of_hdk D hK hM hV hW' hsol I hI (Or.inr hdk) hind T

/-- Lemma `B:lem:cluster-barrier` at zero temperature (M L11905-11909): for `invβ = 0` the
conclusion holds for every cluster with `|I| ≥ 2` in every dimension (the equation is a random
ODE and `d/dt Q_I ≥ -C Q_I` is a Grönwall barrier).  Same proof as `cluster_barrier` through
`cluster_hitting_probability` with `hdk := Or.inl`. -/
theorem cluster_barrier_zero_temp [IsProbabilityMeasure P] (D : DynData d)
    (hK : KernelLocal d D.s) (hM : Torus.SymNonpos D.M) (hV : Torus.IsCk 2 D.V)
    (hβ : D.invβ = 0) (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → (Fin N → Euc d)}
    {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (I : Finset (Fin N)) (hI : 2 ≤ I.card)
    (hind : ∀ J : Finset (Fin N), I ⊂ J → J.card = I.card + 1 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse I T τ Y ω} = 0 := by
  exact cluster_barrier_of_hdk D hK hM hV hW' hsol I hI (Or.inl hβ) hind T

/-! ### No collision in dimension `d ≥ 2` (Proposition `B:prop:particle-no-collision-dge2`) -/

namespace ClusterBarrier

section NoCollision

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

/-- A finite family of positive numbers has a common positive lower bound. -/
theorem exists_pos_le_fintype {ι : Type*} [Fintype ι] (ε : ι → ℝ) (h : ∀ i, 0 < ε i) :
    ∃ e : ℝ, 0 < e ∧ ∀ i, e ≤ ε i := by
  have hS : 0 ≤ ∑ j, 1 / ε j := Finset.sum_nonneg fun j _ => (one_div_pos.2 (h j)).le
  refine ⟨(1 + ∑ j, 1 / ε j)⁻¹, inv_pos.2 (by linarith), fun j => ?_⟩
  have h1 : 1 / ε j ≤ ∑ j, 1 / ε j :=
    Finset.single_le_sum (f := fun j => 1 / ε j) (fun j _ => (one_div_pos.2 (h j)).le)
      (Finset.mem_univ j)
  have : (1 + ∑ j, 1 / ε j)⁻¹ ≤ (1 / ε j)⁻¹ := inv_anti₀ (one_div_pos.2 (h j)) (by linarith)
  simpa using this

/-- For a pair cluster `{i,j}` at distance `r < 1/8`, `Q = r²/2`. -/
theorem clusterDispersionLift_pair {i j : Fin N} (hij : i ≠ j) (Y : Fin N → Euc d)
    (hr : Torus.tdist (Torus.mk (Y i)) (Torus.mk (Y j)) < 1 / 8) :
    clusterDispersionLift ({i, j} : Finset (Fin N)) Y =
      (Torus.tdist (Torus.mk (Y i)) (Torus.mk (Y j))) ^ 2 / 2 := by
  have hr' : ‖geoRep (Y i - Y j)‖ < 1 / 8 := by
    simpa [Torus.tdist, geoRep, mk_sub'] using hr
  have hanti := geoRep_antisymm Y i j hr'
  unfold clusterDispersionLift clusterDispersion
  rw [Finset.card_pair hij, Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij]
  have h00 : ∀ k : Fin N, pairDispersion (Torus.mk (Y k) - Torus.mk (Y k)) = 0 := fun k => by
    rw [sub_self]; exact (pairDispersion_eq_zero_iff 0).2 rfl
  have e1 : pairDispersion (Torus.mk (Y i) - Torus.mk (Y j)) = ‖geoRep (Y i - Y j)‖ ^ 2 := by
    rw [← mk_sub']
    exact pairDispersion_eq_sq _ hr'.le
  have e2 : pairDispersion (Torus.mk (Y j) - Torus.mk (Y i)) = ‖geoRep (Y i - Y j)‖ ^ 2 := by
    rw [← mk_sub']
    rw [pairDispersion_eq_sq _ (by
      have : Torus.centeredRep (Torus.mk (Y j - Y i)) = geoRep (Y j - Y i) := rfl
      rw [this, hanti, norm_neg]; exact hr'.le)]
    have : Torus.centeredRep (Torus.mk (Y j - Y i)) = geoRep (Y j - Y i) := rfl
    rw [this, hanti, norm_neg]
  have e3 : Torus.tdist (Torus.mk (Y i)) (Torus.mk (Y j)) = ‖geoRep (Y i - Y j)‖ := by
    simp [Torus.tdist, geoRep, mk_sub']
  rw [h00, h00, e1, e2, e3]
  push_cast
  ring


end NoCollision

end ClusterBarrier

/-- Proposition `B:prop:particle-no-collision-dge2` (M L11912-11918): for `d ≥ 2` and
`Sym M ≤ 0`, no cluster `I` with `|I| ≥ 2` collapses before `T ∧ τ_⋆`
(`B:eq:no-cluster-collapse-dge2`), and consequently `τ_⋆ = ∞` a.s.  Proof: descending induction
on `|I|` (strong induction on `N - |I|`) with `cluster_barrier`, which applies at every step
since `d(|I|-1) ≥ 2`; then the collision alternative at a pair cluster
(`IsMaximalParticleSolution.collision_alternative`) on `{τ ≤ T}`, for integer `T`. -/
theorem particle_no_collision_dge2 [IsProbabilityMeasure P] (D : DynData d) (hd : 2 ≤ d)
    (hM : Torus.SymNonpos D.M) (hV : Torus.IsCk 2 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) :
    (∀ I : Finset (Fin N), 2 ≤ I.card → ∀ T : ℝ, P {ω | ClusterCollapse I T τ Y ω} = 0) ∧
      ∀ᵐ ω ∂P, τ ω = ⊤ := by
  classical
  have hK : KernelLocal d D.s := kernelLocal_of_two_le hd D.hs0 D.hsd
  have key : ∀ m : ℕ, ∀ I : Finset (Fin N), 2 ≤ I.card → N - I.card = m →
      ∀ T : ℝ, P {ω | ClusterCollapse I T τ Y ω} = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro I hI hm T
      have hIN : I.card ≤ N := by simpa using Finset.card_le_univ I
      refine cluster_barrier D hK hM hV hW' hsol I hI ?_ ?_ T
      · have h1 : 1 ≤ I.card - 1 := by omega
        calc 2 = 2 * 1 := rfl
          _ ≤ d * (I.card - 1) := Nat.mul_le_mul hd h1
      · intro J _ hJc T'
        have hJN : J.card ≤ N := by simpa using Finset.card_le_univ J
        exact ih (N - J.card) (by omega) J (by omega) rfl T'
  have h1 : ∀ I : Finset (Fin N), 2 ≤ I.card → ∀ T : ℝ, P {ω | ClusterCollapse I T τ Y ω} = 0 :=
    fun I hI T => key _ I hI rfl T
  refine ⟨h1, ?_⟩
  have hcol := IsMaximalParticleSolution.collision_alternative D hK hV hW' hsol
  have hnull : P (⋃ T : ℕ, ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j),
      {ω | ClusterCollapse ({i, j} : Finset (Fin N)) (T : ℝ) τ Y ω}) = 0 := by
    refine measure_iUnion_null fun T => measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => h1 _ ?_ _
    rw [Finset.card_pair hij]
  have hn2 := measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [hcol, hn2] with ω hω hnot
  by_contra hne
  have hlt : τ ω < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨τ₀, hτ₀⟩ := WithTop.ne_top_iff_exists.1 hne
  obtain ⟨T, hT⟩ := exists_nat_gt τ₀
  have hτT : ∀ t : ℝ, (t : WithTop ℝ) < τ ω → t < (T : ℝ) := by
    intro t ht
    rw [← hτ₀] at ht
    have : t < τ₀ := by exact_mod_cast ht
    linarith
  apply hnot
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  by_contra hno
  push_neg at hno
  -- every pair has a positive lower bound
  have hpair : ∀ p : Fin N × Fin N, ∃ ε : ℝ, 0 < ε ∧ (p.1 ≠ p.2 → ∀ t : ℝ, 0 ≤ t → t < T →
      (t : WithTop ℝ) < τ ω → ε ≤ clusterDispersionLift ({p.1, p.2} : Finset (Fin N)) (Y t ω)) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hp h⟩
    · have := hno T p.1 p.2 hp
      unfold ClusterCollapse at this
      push_neg at this
      obtain ⟨ε, hε, h⟩ := this
      exact ⟨ε, hε, fun _ t h0 h1 h2 => h t h0 h1 h2⟩
  choose ε hε0 hε using hpair
  obtain ⟨e, he0, hele⟩ := exists_pos_le_fintype ε hε0
  obtain ⟨t, ht1, htτ, i, j, hij, hdist⟩ := hω hlt (min (1 / 8) (16 * e)) (lt_min (by norm_num)
    (by linarith)) 0 le_rfl (by simpa using hsol.pos ω)
  have hr8 : Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < 1 / 8 :=
    lt_of_lt_of_le hdist (min_le_left _ _)
  have hr16 : Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < 16 * e :=
    lt_of_lt_of_le hdist (min_le_right _ _)
  have hQ := clusterDispersionLift_pair hij (Y t ω) hr8
  have hnn : 0 ≤ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) := norm_nonneg _
  have hlow := hε (i, j) hij t ht1.le (hτT t htτ) htτ
  have := hele (i, j)
  set r := Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j))
  simp only at hlow
  rw [hQ] at hlow
  nlinarith

/-! ### The one-dimensional regimes (M L11930-11975; cases (ii)-(iii) of Proposition B.1) -/

namespace ClusterBarrier

open Matrix in
theorem d1_force_term (D : DynData 1) (hs : 0 < D.s) (z : Euc 1) (hz : z ≠ 0) :
    inner ℝ z (Torus.matVec D.M (eucRieszGrad D.s z)) =
      -(D.M 0 0) * D.s * ‖z‖ ^ (-D.s) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have e : Torus.matVec D.M (eucRieszGrad D.s z) = -(rieszRadial D.s z) • Torus.matVec D.M z := by
    unfold eucRieszGrad Torus.matVec; exact map_smul _ _ _
  rw [e, real_inner_smul_right, inner_matVec_eq]
  have h1 : z.ofLp ⬝ᵥ (D.M *ᵥ z.ofLp) = D.M 0 0 * ‖z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Matrix.mulVec, dotProduct]
    ring
  rw [h1]
  have h2 : rieszRadial D.s z = D.s * ‖z‖ ^ (-D.s - 2) := by
    unfold rieszRadial; simp [hs.ne']
  rw [h2]
  have h3 : ‖z‖ ^ (-D.s - 2) * ‖z‖ ^ 2 = ‖z‖ ^ (-D.s) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hn]; norm_num
  calc -(D.s * ‖z‖ ^ (-D.s - 2)) * (D.M 0 0 * ‖z‖ ^ 2)
      = -(D.M 0 0) * D.s * (‖z‖ ^ (-D.s - 2) * ‖z‖ ^ 2) := by ring
    _ = _ := by rw [h3]


theorem d1_clusterInternal_pair (D : DynData 1) (hs : 0 < D.s) {i j : Fin N} (hij : i ≠ j)
    (Y : Fin N → Euc 1) (hr : ‖geoRep (Y i - Y j)‖ < 1 / 8) (hr0 : geoRep (Y i - Y j) ≠ 0) :
    clusterInternal D ({i, j} : Finset (Fin N)) Y =
      (2 / (N : ℝ)) * (-(D.M 0 0) * D.s * ‖geoRep (Y i - Y j)‖ ^ (-D.s)) := by
  have hanti := geoRep_antisymm Y i j hr
  unfold clusterInternal
  rw [Finset.sum_pair hij, Finset.sum_pair hij, Finset.sum_pair hij]
  have h0 : ∀ k : Fin N, geoRep (Y k - Y k) = 0 := fun k => by rw [sub_self]; exact geoRep_zero
  rw [h0, h0, hanti, d1_force_term D hs _ hr0, d1_force_term D hs _ (neg_ne_zero.2 hr0),
    norm_neg]
  simp [eucRieszGrad, Torus.matVec]
  ring


theorem d1_internal_ge (D : DynData 1) (hs : 0 < D.s) (ha : D.M 0 0 < 0) {i j : Fin N}
    (hij : i ≠ j) :
    ∃ q₂ : ℝ, 0 < q₂ ∧ q₂ ≤ clusterRadius ({i, j} : Finset (Fin N)) ∧
      ∀ Y : Fin N → Euc 1, 0 < clusterDispersionLift ({i, j} : Finset (Fin N)) Y →
        clusterDispersionLift ({i, j} : Finset (Fin N)) Y < q₂ →
        2 * D.invβ ≤ clusterInternal D ({i, j} : Finset (Fin N)) Y := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i
  set κ : ℝ := -(D.M 0 0) * D.s with hκ
  have hκ0 : 0 < κ := mul_pos (by linarith) hs
  set B : ℝ := N * D.invβ / κ with hB
  have hB0 : 0 ≤ B := by have := D.hβ; positivity
  set r₀ : ℝ := (B + 1) ^ (-1 / D.s) with hr₀
  have hr₀0 : 0 < r₀ := Real.rpow_pos_of_pos (by linarith) _
  have hr₀s : r₀ ^ (-D.s) = B + 1 := by
    rw [hr₀, ← Real.rpow_mul (by linarith)]
    have : -1 / D.s * -D.s = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hrad : clusterRadius ({i, j} : Finset (Fin N)) = 1 / 256 := by
    unfold clusterRadius; rw [Finset.card_pair hij]; norm_num
  refine ⟨min (r₀ ^ 2 / 2) (1 / 256), lt_min (by positivity) (by norm_num),
    hrad ▸ min_le_right _ _, fun Y hQ0 hQ => ?_⟩
  have hQrad : clusterDispersionLift ({i, j} : Finset (Fin N)) Y <
      clusterRadius ({i, j} : Finset (Fin N)) := by
    rw [hrad]; exact lt_of_lt_of_le hQ (min_le_right _ _)
  have hr8 : ‖geoRep (Y i - Y j)‖ < 1 / 8 :=
    (clusterDispersionLift_eq_euclid _ Y hQrad).1 i (by simp) j (by simp)
  have hQeq := clusterDispersionLift_pair hij Y (by simpa [Torus.tdist, geoRep, mk_sub'] using hr8)
  have he3 : Torus.tdist (Torus.mk (Y i)) (Torus.mk (Y j)) = ‖geoRep (Y i - Y j)‖ := by
    simp [Torus.tdist, geoRep, mk_sub']
  rw [he3] at hQeq
  set r := ‖geoRep (Y i - Y j)‖ with hr
  have hrpos : 0 < r := by
    by_contra h
    have : r = 0 := le_antisymm (not_lt.1 h) (norm_nonneg _)
    rw [hQeq, this] at hQ0; simp at hQ0
  have hz : geoRep (Y i - Y j) ≠ 0 := fun h => by rw [h] at hr; simp [hr] at hrpos
  have hrlt : r < r₀ := by
    have h1 : r ^ 2 / 2 < r₀ ^ 2 / 2 := by
      rw [← hQeq]; exact lt_of_lt_of_le hQ (min_le_left _ _)
    nlinarith
  have hpow : B + 1 < r ^ (-D.s) := by
    rw [← hr₀s]
    exact Real.rpow_lt_rpow_of_neg hrpos hrlt (by linarith)
  rw [d1_clusterInternal_pair D hs hij Y hr8 hz]
  have : B * κ = N * D.invβ := by rw [hB]; field_simp
  have h2 : (2 / (N : ℝ)) * (κ * r ^ (-D.s)) ≥ (2 / (N : ℝ)) * (κ * B) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith) hκ0.le
  calc 2 * D.invβ = (2 / (N : ℝ)) * (κ * B) := by field_simp; nlinarith
    _ ≤ _ := h2

section Generator

variable {d N : ℕ}

theorem barrier_generator_bound_of_internal (D : DynData d) (hM : Torus.SymNonpos D.M) (I : Finset (Fin N))
    (hI : 2 ≤ I.card) {q C₀ : ℝ} (hq : 0 < q)
    (hqr : q < clusterRadius I) (hC₀ : 0 ≤ C₀) (S : Set (Fin N → Euc d))
    (hrem : ∀ Y ∈ S, Y ∈ liftedFree d N → clusterDispersionLift I Y < q →
      -C₀ * clusterDispersionLift I Y ≤ clusterRemainder D I Y)
    (hA : ∀ Y ∈ S, Y ∈ liftedFree d N → clusterDispersionLift I Y < q / 4 →
      4 * D.invβ ≤ 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ + clusterInternal D I Y) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ Y ∈ S, Y ∈ liftedFree d N →
      diffGen D (barrierPhi q ∘ clusterDispersionLift I) Y ≤ C' := by
  have hΦ := barrierPhi_contDiffOn hq
  have hd1 : ContDiffOn ℝ 1 (deriv (barrierPhi q)) (Set.Ioi 0) :=
    hΦ.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)
  have hc1 : ContinuousOn (deriv (barrierPhi q)) (Set.Ioi 0) := hd1.continuousOn
  have hc2 : ContinuousOn (deriv (deriv (barrierPhi q))) (Set.Ioi 0) :=
    hd1.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl
  set f : ℝ → ℝ := fun x => |deriv (barrierPhi q) x| * C₀ * x +
    4 * D.invβ * x * |deriv (deriv (barrierPhi q)) x| with hf
  have hsub : Set.Icc (q / 4) (3 * q / 4) ⊆ Set.Ioi 0 := fun x hx => by
    simp only [Set.mem_Icc, Set.mem_Ioi] at hx ⊢; linarith [hx.1]
  have hfc : ContinuousOn f (Set.Icc (q / 4) (3 * q / 4)) := by
    have a1 := (hc1.mono hsub).abs
    have a2 := (hc2.mono hsub).abs
    exact ((a1.mul continuousOn_const).mul continuousOn_id).add
      (((continuousOn_const.mul continuousOn_id)).mul a2)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  have hc₁0 : 0 ≤ 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ := by
    have : (1 : ℝ) ≤ I.card := by exact_mod_cast (by omega : 1 ≤ I.card)
    have := D.hβ
    positivity
  refine ⟨C₀ + |B|, by positivity, fun Y hYS hYf => ?_⟩
  have hQpos := clusterDispersionLift_pos hI hYf
  set a := clusterDispersionLift I Y with ha
  rw [diffGen_barrier D I hq hQpos]
  rcases le_or_gt (3 * q / 4) a with h34 | h34
  · have h1 : deriv (barrierPhi q) a = 0 := deriv_barrierPhi_of_gt hq (by linarith)
    have h2 : deriv (deriv (barrierPhi q)) a = 0 := deriv2_barrierPhi_of_gt hq (by linarith)
    rw [h1, h2]; simp; positivity
  · have hQr : a < clusterRadius I := by linarith
    have hqv := cluster_qv D I Y hQr
    rw [hqv]
    have hG : clusterGenerator D I Y = 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ +
        clusterInternal D I Y + clusterRemainder D I Y := by
      unfold clusterRemainder; ring
    have hA := clusterInternal_nonneg D hM I Y
    have hR := hrem Y hYS hYf (by linarith)
    have hs := deriv_barrierPhi_nonpos hq hQpos
    set s := deriv (barrierPhi q) a with hsdef
    set c₁ := 2 * (d : ℝ) * ((I.card : ℝ) - 1) * D.invβ with hc₁def
    have hGlow : c₁ - C₀ * a ≤ clusterGenerator D I Y := by rw [hG]; linarith
    have h3 : s * clusterGenerator D I Y ≤ s * (c₁ - C₀ * a) :=
      mul_le_mul_of_nonpos_left hGlow hs
    rcases lt_or_ge a (q / 4) with h4 | h4
    · have e1 : s = -(1 / a) := deriv_barrierPhi_of_le hq hQpos h4
      have e2 : deriv (deriv (barrierPhi q)) a = 1 / a ^ 2 := deriv2_barrierPhi_of_le hq hQpos h4
      rw [e2]
      have hGlow' : c₁ + clusterInternal D I Y - C₀ * a ≤ clusterGenerator D I Y := by
        rw [hG]; linarith
      have h3' : s * clusterGenerator D I Y ≤ s * (c₁ + clusterInternal D I Y - C₀ * a) :=
        mul_le_mul_of_nonpos_left hGlow' hs
      have : s * (c₁ + clusterInternal D I Y - C₀ * a) + 1 / 2 * (1 / a ^ 2) * (8 * D.invβ * a) =
          (-(c₁ + clusterInternal D I Y) + 4 * D.invβ) / a + C₀ := by
        rw [e1]; field_simp; ring
      have h5 : (-(c₁ + clusterInternal D I Y) + 4 * D.invβ) / a ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith [hA Y hYS hYf h4]) hQpos.le
      have h6 : 1 / 2 * (1 / a ^ 2) * (8 * D.invβ * a) ≥ 0 := by
        have := D.hβ; positivity
      nlinarith [abs_nonneg B]
    · have hmem : a ∈ Set.Icc (q / 4) (3 * q / 4) := ⟨h4, h34.le⟩
      have hfa := hB a hmem
      rw [Real.norm_eq_abs] at hfa
      have hfa' : f a ≤ |B| := ((le_abs_self (f a)).trans hfa).trans (le_abs_self B)
      have habs : |s| = -s := abs_of_nonpos hs
      have e3 : s * (c₁ - C₀ * a) ≤ |s| * C₀ * a := by
        rw [habs]; nlinarith [mul_nonneg (neg_nonneg.2 hs) hc₁0]
      have e4 : 1 / 2 * deriv (deriv (barrierPhi q)) a * (8 * D.invβ * a) ≤
          4 * D.invβ * a * |deriv (deriv (barrierPhi q)) a| := by
        have := D.hβ
        have h0 : 0 ≤ 4 * D.invβ * a := by positivity
        calc 1 / 2 * deriv (deriv (barrierPhi q)) a * (8 * D.invβ * a)
            = 4 * D.invβ * a * deriv (deriv (barrierPhi q)) a := by ring
          _ ≤ 4 * D.invβ * a * |deriv (deriv (barrierPhi q)) a| :=
            mul_le_mul_of_nonneg_left (le_abs_self _) h0
      have : f a = |s| * C₀ * a + 4 * D.invβ * a * |deriv (deriv (barrierPhi q)) a| := rfl
      nlinarith [abs_nonneg B]
  
end Generator


section HitBarrier

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

theorem cluster_hitting_of_gen [IsProbabilityMeasure P] (D : DynData d)
    (hK : KernelLocal d D.s) (hV : Torus.IsCk 2 D.V)
    (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ}
    {Y : ℝ → Ω → (Fin N → Euc d)} (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (I : Finset (Fin N)) (hI : 2 ≤ I.card) {q C' : ℝ} (hq : 0 < q) (hC'0 : 0 ≤ C')
    (δ : ℝ) (hgen : ∀ Z : Fin N → Euc d, (∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z) →
      Z ∈ liftedFree d N → diffGen D (barrierPhi q ∘ clusterDispersionLift I) Z ≤ C')
    (q₁ : ℝ) (hq₁ : 0 < q₁) (T : ℝ) :
    ∃ a₀ C : ℝ, 0 < a₀ ∧ ∀ a : ℝ, 0 < a → a < a₀ →
      P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ≤
        ENNReal.ofReal (C / |Real.log a|) := by
  classical
  set T' := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  set m : ℝ := Real.log (q / 2) with hm
  set Kb : ℝ := barrierPhi q (min q₁ (q / 2)) + m + C' * T' with hKb
  have hmin0 : 0 < min q₁ (q / 2) := lt_min hq₁ (by linarith)
  have hKb0 : 0 ≤ Kb := by
    have h1 : -Real.log (q / 2) ≤ barrierPhi q (min q₁ (q / 2)) := barrierPhi_ge hq hmin0
    have := mul_nonneg hC'0 hT'0
    simp only [hKb, hm]; linarith
  refine ⟨min (q / 4) (min q₁ (Real.exp (-(2 * |m|)))), 2 * Kb, ?_, ?_⟩
  · exact lt_min (by linarith) (lt_min hq₁ (Real.exp_pos _))
  intro a ha hlt
  have haq : a < q / 4 := lt_of_lt_of_le hlt (min_le_left _ _)
  have haq₁ : a < q₁ := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have hae : a < Real.exp (-(2 * |m|)) :=
    lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  have hlog : Real.log a < -(2 * |m|) := by
    rw [Real.log_lt_iff_lt_exp ha]; exact hae
  have hlogneg : Real.log a < 0 := by have := abs_nonneg m; linarith
  have habs : |Real.log a| = -Real.log a := abs_of_neg hlogneg
  have hΦa : barrierPhi q a = -Real.log a := barrierPhi_of_le hq haq.le
  have hca : |Real.log a| / 2 ≤ barrierPhi q a + m := by
    rw [hΦa, habs]
    have := neg_abs_le m
    have := le_abs_self m
    linarith
  have hca0 : 0 < barrierPhi q a + m := lt_of_lt_of_le (by rw [habs]; linarith) hca
  -- level estimates
  have hB : ∀ n : ℕ, ∃ B : Set Ω, MeasurableSet B ∧
      (∀ ω, Y₀ ω ∈ barrierK I a δ n → q₁ ≤ clusterDispersionLift I (Y₀ ω) →
        (∃ r : ℝ, 0 ≤ r ∧ r ≤ T' ∧ solHit τ Y (barrierG I a δ n) ω = (r : WithTop ℝ) ∧
          clusterDispersionLift I (Y r ω) ≤ a) → ω ∈ B) ∧
      (barrierPhi q a + Real.log (q / 2)) * (P B).toReal ≤
        barrierPhi q (min q₁ (q / 2)) + Real.log (q / 2) + C' * T' := fun n =>
    barrier_level_estimate D hK hV hW' hsol I hI hq hC'0 hgen hT'0 ha hq₁ n
  choose B hBm hBsub hBest using hB
  have hPB : ∀ n, P (B n) ≤ ENNReal.ofReal (2 * Kb / |Real.log a|) := by
    intro n
    have h1 : (P (B n)).toReal ≤ 2 * Kb / |Real.log a| := by
      have hlogpos : 0 < |Real.log a| := by rw [habs]; linarith
      rw [le_div_iff₀ hlogpos]
      have h2 := hBest n
      have h3 : (P (B n)).toReal * (|Real.log a| / 2) ≤
          (P (B n)).toReal * (barrierPhi q a + m) :=
        mul_le_mul_of_nonneg_left hca ENNReal.toReal_nonneg
      nlinarith
    calc P (B n) = ENNReal.ofReal (P (B n)).toReal := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal h1
  -- the event is contained in the liminf
  have hsub : {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ⊆
      ⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n := by
    rintro ω ⟨hq0, t, ht0, htT, htτ, hQt, hδt⟩
    have hY0 : Y 0 ω = Y₀ ω := hsol.sol.init ω
    obtain ⟨n₀, hn₀⟩ := reach_eventually (τ := τ ω) (y := fun t => Y t ω) I (δ := δ) (q₁ := q₁)
      (T := T') haq₁.le (hsol.sol.cont ω) (hsol.mem ω) (by simpa [hY0] using hq0)
      ⟨t, ht0, htT.trans (le_max_left _ _), htτ, hQt, hδt⟩
    refine Set.mem_iUnion.2 ⟨n₀, Set.mem_iInter₂.2 fun n hn => ?_⟩
    obtain ⟨hK0, r, hr0, hrT, hhit, hQr⟩ := hn₀ n hn
    exact hBsub n ω (by simpa [hY0] using hK0) hq0 ⟨r, hr0, hrT, hhit, hQr⟩
  have hmono : Monotone fun n₀ : ℕ => ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n := by
    intro k l hkl
    exact Set.iInter₂_mono' fun n hn => ⟨n, hkl.trans hn, subset_rfl⟩
  calc P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω}
      ≤ P (⋃ n₀ : ℕ, ⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n) := measure_mono hsub
    _ = ⨆ n₀ : ℕ, P (⋂ n : ℕ, ⋂ (_ : n₀ ≤ n), B n) := hmono.measure_iUnion
    _ ≤ ENNReal.ofReal (2 * Kb / |Real.log a|) := by
        refine iSup_le fun n₀ => ?_
        exact (measure_mono (Set.iInter₂_subset n₀ le_rfl)).trans (hPB n₀)

theorem cluster_barrier_of_hit [IsProbabilityMeasure P] (D : DynData d) 
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (I : Finset (Fin N)) (hI : 2 ≤ I.card)
    (hhit : ∀ δ : ℝ, 0 < δ → ∀ q₁ : ℝ, 0 < q₁ → ∀ T : ℝ, ∃ a₀ C : ℝ, 0 < a₀ ∧
      ∀ a : ℝ, 0 < a → a < a₀ →
        P {ω | q₁ ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} ≤
          ENNReal.ofReal (C / |Real.log a|))
    (hind : ∀ J : Finset (Fin N), I ⊂ J → J.card = I.card + 1 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse I T τ Y ω} = 0 := by
  classical
  set F : ℝ → Set Ω := fun δ => {ω | ∃ s : ℝ, 0 ≤ s ∧ s < T ∧ (s : WithTop ℝ) < τ ω ∧
    ∃ j, j ∉ I ∧ clusterDispersionLift (insert j I) (Y s ω) ≤ δ} with hF
  set X : ℕ → Set Ω := fun k => {ω | ClusterCollapse I T τ Y ω ∧
    1 / ((k : ℝ) + 1) ≤ clusterDispersionLift I (Y₀ ω)} with hX
  -- Step A
  have hA : ∀ k : ℕ, ∀ δ : ℝ, 0 < δ → P (X k ∩ (F δ)ᶜ) = 0 := by
    intro k δ hδ
    obtain ⟨a₀, C, ha₀, hC⟩ := hhit δ hδ (1 / ((k : ℝ) + 1)) (by positivity) T
    have hsub : ∀ a : ℝ, 0 < a → X k ∩ (F δ)ᶜ ⊆
        {ω | 1 / ((k : ℝ) + 1) ≤ clusterDispersionLift I (Y₀ ω) ∧ ClusterReach I a δ T τ Y ω} := by
      intro a ha ω ⟨⟨hcol, hq0⟩, hnF⟩
      refine ⟨hq0, ?_⟩
      obtain ⟨t, ht0, htT, htτ, hQt⟩ := hcol a ha
      refine ⟨t, ht0, htT.le, htτ, hQt.le, fun s hs0 hst j hj => ?_⟩
      by_contra hle
      push_neg at hle
      exact hnF ⟨s, hs0, lt_of_le_of_lt hst htT,
        lt_of_le_of_lt (by exact_mod_cast hst) htτ, j, hj, hle⟩
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (-Real.log a₀)
    have hev : ∀ n : ℕ, n₀ ≤ n → P (X k ∩ (F δ)ᶜ) ≤ ENNReal.ofReal (C / (n : ℝ)) := by
      intro n hn
      have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
      have hlt : Real.exp (-(n : ℝ)) < a₀ := by
        rw [← Real.lt_log_iff_exp_lt ha₀]; linarith
      have := hC _ (Real.exp_pos _) hlt
      rw [Real.log_exp, abs_neg, Nat.abs_cast] at this
      exact (measure_mono (hsub _ (Real.exp_pos _))).trans this
    have htend : Tendsto (fun n : ℕ => ENNReal.ofReal (C / (n : ℝ))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal (tendsto_const_div_atTop_nhds_zero_nat C)
      simpa using this
    exact le_antisymm (ge_of_tendsto htend (Filter.eventually_atTop.2 ⟨n₀, hev⟩)) bot_le
  -- Step B
  have hB : ∀ k : ℕ, X k ⊆ (⋃ j ∈ ({j | j ∉ I} : Set (Fin N)),
        {ω | ClusterCollapse (insert j I) T τ Y ω}) ∪ ⋃ l : ℕ, X k ∩ (F (1 / ((l : ℝ) + 1)))ᶜ := by
    intro k ω hω
    by_cases hcol : ω ∈ ⋃ j ∈ ({j | j ∉ I} : Set (Fin N)), {ω | ClusterCollapse (insert j I) T τ Y ω}
    · exact Or.inl hcol
    right
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcol
    have hnc : ∀ j, ∃ ε : ℝ, 0 < ε ∧ (j ∉ I → ∀ t : ℝ, 0 ≤ t → t < T → (t : WithTop ℝ) < τ ω →
        ε ≤ clusterDispersionLift (insert j I) (Y t ω)) := by
      intro j
      by_cases hj : j ∈ I
      · exact ⟨1, one_pos, fun h => absurd hj h⟩
      · have := hcol j hj
        unfold ClusterCollapse at this
        push_neg at this
        obtain ⟨ε, hε, h⟩ := this
        exact ⟨ε, hε, fun _ t h0 h1 h2 => h t h0 h1 h2⟩
    choose ε hε0 hε using hnc
    set ε₀ : ℝ := (1 + ∑ j, 1 / ε j)⁻¹ with hε₀
    have hS : 0 ≤ ∑ j, 1 / ε j := Finset.sum_nonneg fun j _ => (one_div_pos.2 (hε0 j)).le
    have hε₀pos : 0 < ε₀ := inv_pos.2 (by linarith)
    have hε₀le : ∀ j, ε₀ ≤ ε j := by
      intro j
      have h1 : 1 / ε j ≤ ∑ j, 1 / ε j :=
        Finset.single_le_sum (f := fun j => 1 / ε j) (fun j _ => (one_div_pos.2 (hε0 j)).le)
          (Finset.mem_univ j)
      rw [hε₀]
      have : (1 + ∑ j, 1 / ε j)⁻¹ ≤ (1 / ε j)⁻¹ := inv_anti₀ (one_div_pos.2 (hε0 j)) (by linarith)
      simpa using this
    obtain ⟨l, hl⟩ := exists_nat_one_div_lt hε₀pos
    refine Set.mem_iUnion.2 ⟨l, hω, ?_⟩
    rintro ⟨s, hs0, hsT, hsτ, j, hj, hle⟩
    have := hε j hj s hs0 hsT hsτ
    linarith [hε₀le j]
  -- conclusion
  have hk : {ω | ClusterCollapse I T τ Y ω} ⊆ ⋃ k : ℕ, X k := by
    intro ω hω
    have hfree : Y₀ ω ∈ liftedFree d N := by
      have := hsol.mem ω 0 le_rfl (by simpa using hsol.pos ω)
      rwa [hsol.sol.init ω] at this
    have hpos := clusterDispersionLift_pos hI hfree
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hpos
    exact Set.mem_iUnion.2 ⟨k, hω, hk.le⟩
  refine measure_mono_null hk (measure_iUnion_null fun k => ?_)
  refine measure_mono_null (hB k) (measure_union_null ?_ (measure_iUnion_null fun l => ?_))
  · refine measure_biUnion_null_iff (Set.to_countable _) |>.2 fun j hj => ?_
    exact hind (insert j I) (Finset.ssubset_insert hj) (Finset.card_insert_of_notMem hj) T
  · exact hA k _ (by positivity)


end HitBarrier

theorem symNonpos_of_d1 (M : Matrix (Fin 1) (Fin 1) ℝ) (h : M 0 0 ≤ 0) : Torus.SymNonpos M := by
  unfold Torus.SymNonpos
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · ext i j
    fin_cases i; fin_cases j
    simp [Torus.symPart, Matrix.conjTranspose]
  · intro x
    simp [Torus.symPart, Matrix.mulVec, dotProduct]
    nlinarith [sq_nonneg (x 0)]

end ClusterBarrier

/-- Lemma `B:lem:d1-pair-barrier` (M L11938-11948), positive temperature: `d = 1`, `I = {i,j}`,
`0 < s < 1`, `β_N < ∞` (`invβ > 0`), `M = -a` with `a > 0`; if no three-point enlargement
collapses before `T ∧ τ` then the pair does not.  Proof: near the pair diagonal
`Q_I = r²/2`, `𝒜_I = (2/N) a s |r|^{-s} = (2/N) a s (2Q_I)^{-s/2}` (from `clusterInternal`
with `eucRieszGrad`), so `ℒ(-log Q_I) ≤ 2/(β Q_I) - (2as/N) 2^{-s/2} Q_I^{-1-s/2} + C_δ`
(`B:eq:d1-riesz-generator`), whose negative term dominates as `Q_I ↓ 0`; then the stopping
argument of `cluster_hitting_probability` with this barrier.  Uses the `d = 1` kernel inputs
through `hK`. -/
theorem d1_pair_barrier [IsProbabilityMeasure P] (D : DynData 1) (hK : KernelLocal 1 D.s)
    (hV : Torus.IsCk 2 D.V) (hs0 : 0 < D.s) (hβ : 0 < D.invβ) (ha : D.M 0 0 < 0)
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc 1)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc 1)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (i j : Fin N) (hij : i ≠ j)
    (hind : ∀ J : Finset (Fin N), ({i, j} : Finset (Fin N)) ⊂ J → J.card = 3 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse ({i, j} : Finset (Fin N)) T τ Y ω} = 0 := by
  have hI : 2 ≤ ({i, j} : Finset (Fin N)).card := by rw [Finset.card_pair hij]
  refine cluster_barrier_of_hit D hsol ({i, j} : Finset (Fin N)) hI ?_ ?_ T
  · intro δ hδ q₁ hq₁ T'
    obtain ⟨q, C₀, hq, hqr, hC₀, hrem⟩ := clusterRemainder_bound D hK hV _ hI δ hδ
    obtain ⟨q₂, hq₂, -, hint⟩ := d1_internal_ge D hs0 ha hij
    obtain ⟨C', hC'0, hC'⟩ := barrier_generator_bound_of_internal D (symNonpos_of_d1 D.M ha.le) _ hI (q := min q q₂)
      (lt_min hq hq₂) (lt_of_le_of_lt (min_le_left _ _) hqr) hC₀
      {Z | ∀ j', j' ∉ ({i, j} : Finset (Fin N)) → δ ≤ clusterDispersionLift (insert j' {i, j}) Z}
      (fun Y hYS hYf hYq => hrem Y hYf (lt_of_lt_of_le hYq (min_le_left _ _)) hYS)
      (fun Y _ hYf hYq => by
        have hpos := clusterDispersionLift_pos hI hYf
        have h2 := hint Y hpos (by linarith [min_le_right q q₂])
        rw [Finset.card_pair hij]
        norm_num
        linarith)
    exact cluster_hitting_of_gen D hK hV hW' hsol _ hI (lt_min hq hq₂) hC'0 δ
      (fun Z hZS hZf => hC' Z hZS hZf) q₁ hq₁ T'
  · intro J hJ hJc T'
    exact hind J hJ (by rw [hJc, Finset.card_pair hij]) T'

/-- Lemma `B:lem:d1-pair-barrier`, zero-temperature clause (M L11947, L11966): for
`invβ = 0`, every `0 ≤ s < 1` and every `a ≥ 0` (`Sym M ≤ 0`), the pair does not collapse.
A corollary of `cluster_barrier_zero_temp`. -/
theorem d1_pair_barrier_zero_temp [IsProbabilityMeasure P] (D : DynData 1)
    (hK : KernelLocal 1 D.s) (hV : Torus.IsCk 2 D.V) (hβ : D.invβ = 0)
    (hM : Torus.SymNonpos D.M) {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {Y₀ : Ω → (Fin N → Euc 1)} {τ : Ω → WithTop ℝ}
    {Y : ℝ → Ω → (Fin N → Euc 1)} (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y)
    (i j : Fin N) (hij : i ≠ j)
    (hind : ∀ J : Finset (Fin N), ({i, j} : Finset (Fin N)) ⊂ J → J.card = 3 →
      ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0)
    (T : ℝ) : P {ω | ClusterCollapse ({i, j} : Finset (Fin N)) T τ Y ω} = 0 := by
  refine cluster_barrier_zero_temp D hK hM hV hβ hW' hsol ({i, j} : Finset (Fin N))
    (by rw [Finset.card_pair hij]) ?_ T
  intro J hJ hJc T'
  exact hind J hJ (by rw [hJc, Finset.card_pair hij]) T'

/-- Proposition `B:prop:particle-no-collision-d1` (M L11969-11975): `d = 1`, `Sym M ≤ 0`, and
either `β_N = ∞` (`invβ = 0`), or `β_N < ∞`, `0 < s < 1` and `M = -a` with `a > 0`; then
`τ_⋆ = ∞` a.s.  Proof: descending induction; clusters with `|I| ≥ 3` by `cluster_barrier`
(`1·(|I|-1) ≥ 2`), pairs by `d1_pair_barrier` / `d1_pair_barrier_zero_temp`; then the collision
alternative as in `particle_no_collision_dge2`.  The kernel inputs are `kernelLocal_d1`
(section `KernelD1Inputs`, from `HRS/Kernel/D1.lean`). -/
theorem particle_no_collision_d1 [IsProbabilityMeasure P] (D : DynData 1)
    (hM : Torus.SymNonpos D.M) (hV : Torus.IsCk 2 D.V)
    (hcase : D.invβ = 0 ∨ (0 < D.invβ ∧ 0 < D.s ∧ D.M 0 0 < 0))
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc 1)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc 1)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) :
    ∀ᵐ ω ∂P, τ ω = ⊤ := by
  classical
  have hs1 : D.s < 1 := by simpa using D.hsd
  have hK : KernelLocal 1 D.s := kernelLocal_d1 D.hs0 hs1
  have key : ∀ m : ℕ, ∀ I : Finset (Fin N), 2 ≤ I.card → N - I.card = m →
      ∀ T : ℝ, P {ω | ClusterCollapse I T τ Y ω} = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro I hI hm T
      have hIN : I.card ≤ N := by simpa using Finset.card_le_univ I
      have hind : ∀ J : Finset (Fin N), I ⊂ J → J.card = I.card + 1 →
          ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0 := by
        intro J _ hJc T'
        have hJN : J.card ≤ N := by simpa using Finset.card_le_univ J
        exact ih (N - J.card) (by omega) J (by omega) rfl T'
      by_cases h3 : 3 ≤ I.card
      · refine cluster_barrier D hK hM hV hW' hsol I hI ?_ hind T
        have : 2 ≤ I.card - 1 := by omega
        simpa using this
      · have h2 : I.card = 2 := by omega
        obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.1 h2
        have hind' : ∀ J : Finset (Fin N), ({i, j} : Finset (Fin N)) ⊂ J → J.card = 3 →
            ∀ T : ℝ, P {ω | ClusterCollapse J T τ Y ω} = 0 :=
          fun J hJ hJc T' => hind J hJ (by rw [hJc, h2]) T'
        rcases hcase with hβ | ⟨hβ, hs0, ha⟩
        · exact d1_pair_barrier_zero_temp D hK hV hβ hM hW' hsol i j hij hind' T
        · exact d1_pair_barrier D hK hV hs0 hβ ha hW' hsol i j hij hind' T
  have h1 : ∀ I : Finset (Fin N), 2 ≤ I.card → ∀ T : ℝ, P {ω | ClusterCollapse I T τ Y ω} = 0 :=
    fun I hI T => key _ I hI rfl T
  have hcol := IsMaximalParticleSolution.collision_alternative D hK hV hW' hsol
  have hnull : P (⋃ T : ℕ, ⋃ i : Fin N, ⋃ j : Fin N, ⋃ (_ : i ≠ j),
      {ω | ClusterCollapse ({i, j} : Finset (Fin N)) (T : ℝ) τ Y ω}) = 0 := by
    refine measure_iUnion_null fun T => measure_iUnion_null fun i => measure_iUnion_null fun j =>
      measure_iUnion_null fun hij => h1 _ ?_ _
    rw [Finset.card_pair hij]
  have hn2 := measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [hcol, hn2] with ω hω hnot
  by_contra hne
  have hlt : τ ω < ⊤ := lt_top_iff_ne_top.2 hne
  obtain ⟨τ₀, hτ₀⟩ := WithTop.ne_top_iff_exists.1 hne
  obtain ⟨T, hT⟩ := exists_nat_gt τ₀
  have hτT : ∀ t : ℝ, (t : WithTop ℝ) < τ ω → t < (T : ℝ) := by
    intro t ht
    rw [← hτ₀] at ht
    have : t < τ₀ := by exact_mod_cast ht
    linarith
  apply hnot
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  by_contra hno
  push_neg at hno
  have hpair : ∀ p : Fin N × Fin N, ∃ ε : ℝ, 0 < ε ∧ (p.1 ≠ p.2 → ∀ t : ℝ, 0 ≤ t → t < T →
      (t : WithTop ℝ) < τ ω → ε ≤ clusterDispersionLift ({p.1, p.2} : Finset (Fin N)) (Y t ω)) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun h => absurd hp h⟩
    · have := hno T p.1 p.2 hp
      unfold ClusterCollapse at this
      push_neg at this
      obtain ⟨ε, hε, h⟩ := this
      exact ⟨ε, hε, fun _ t h0 h1 h2 => h t h0 h1 h2⟩
  choose ε hε0 hε using hpair
  obtain ⟨e, he0, hele⟩ := exists_pos_le_fintype ε hε0
  obtain ⟨t, ht1, htτ, i, j, hij, hdist⟩ := hω hlt (min (1 / 8) (16 * e)) (lt_min (by norm_num)
    (by linarith)) 0 le_rfl (by simpa using hsol.pos ω)
  have hr8 : Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < 1 / 8 :=
    lt_of_lt_of_le hdist (min_le_left _ _)
  have hr16 : Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) < 16 * e :=
    lt_of_lt_of_le hdist (min_le_right _ _)
  have hQ := clusterDispersionLift_pair hij (Y t ω) hr8
  have hnn : 0 ≤ Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j)) := norm_nonneg _
  have hlow := hε (i, j) hij t ht1.le (hτT t htτ) htτ
  have := hele (i, j)
  set r := Torus.tdist (Torus.mk (Y t ω i)) (Torus.mk (Y t ω j))
  simp only at hlow
  rw [hQ] at hlow
  nlinarith

/-! ### Conclusion (M L11987-12000) -/

/-- **Corrected reduction for existence** (replaces `exists_isStrongSolution_of_no_exit` of
`Bridge.lean`, stated through the bundle `IsMaximalParticleSolution`; the Bridge version has been
corrected to require `0 < τ` in its `hnoexit` premise, which as first stated was unsatisfiable): with the
lifted drift locally Lipschitz on the collision-free region, and given that every maximal
solution (`IsMaximalParticleSolution`, for every Brownian filtration carrying `X₀`) has infinite
lifetime a.s., the particle system has a global collision-free strong solution for every
horizon `T`.  Same proof as in `Bridge.lean`, with positivity carried along. -/
theorem exists_isStrongSolution_of_maximal (P : Measure Ω) [IsProbabilityMeasure P]
    (D : DynData d) (hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z))
    (X₀ : Ω → Config d N) (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    (hnoexit : ∀ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      IsBrownianFiltration P ℱ W' → (∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j) →
      ∀ (Y₀ : Ω → (Fin N → Euc d)) (τ : Ω → WithTop ℝ) (Y : ℝ → Ω → (Fin N → Euc d)),
      IsMaximalParticleSolution P ℱ W' D Y₀ τ Y →
      (∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω) →
      ∀ᵐ ω ∂P, τ ω = ⊤)
    (T : ℝ) : ∃ X, IsStrongSolution P D T X₀ W X := by
  classical
  obtain ⟨W', hW'm, hWW', hBF, hX₀ℱ⟩ :=
    exists_isBrownianFiltration_of_isVectorBrownian P W hW X₀ hX₀ hind
  set ℱ := generatedFiltration P X₀ hX₀ W' hW'm with hℱ
  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, X₀ ω₀ ∉ collisionSet d N := hdist.exists
  let rep : Ω → Fin N → Euc d := fun ω i => Torus.rep (X₀ ω i)
  have hmk : ∀ ω, (fun i => Torus.mk (rep ω i)) = X₀ ω := fun ω =>
    funext fun i => Torus.mk_rep _
  have hcoll : MeasurableSet (collisionSet d N) := (isClosed_collisionSet d N).measurableSet
  let Y₀ : Ω → Fin N → Euc d := fun ω => if X₀ ω ∈ collisionSet d N then rep ω₀ else rep ω
  have hY₀m : ∀ t : ℝ, Measurable[ℱ t] Y₀ := by
    intro t
    let _ : MeasurableSpace Ω := ℱ t
    have hrep : Measurable rep := measurable_pi_iff.2 fun i =>
      (measurable_torusRep d).comp ((measurable_pi_apply i).comp (hX₀ℱ t))
    exact Measurable.ite (hX₀ℱ t hcoll) measurable_const hrep
  have hY₀0 : ∀ ω, Y₀ ω ∈ liftedFree d N := by
    intro ω
    show (fun i => Torus.mk (Y₀ ω i)) ∉ collisionSet d N
    by_cases h : X₀ ω ∈ collisionSet d N
    · simp only [Y₀, h, ↓reduceIte]
      rw [hmk ω₀]
      exact hω₀
    · simp only [Y₀, h, ↓reduceIte]
      rw [hmk ω]
      exact h
  have hY₀ae : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω := by
    filter_upwards [hdist] with ω h
    simp only [Y₀, h, ↓reduceIte]
    exact hmk ω
  obtain ⟨τ, Y, hstop, hpos, hsol, hmem, hexit, hmax⟩ := exists_sde_solution_maximal hBF
    (liftedFree d N) (isOpen_liftedFree d N) (fun _ Z => liftedDrift D Z) hb (liftedNoise D) Y₀
    hY₀m hY₀0
  have htop : ∀ᵐ ω ∂P, τ ω = ⊤ :=
    hnoexit ℱ W' hBF hWW' Y₀ τ Y ⟨hY₀m, hstop, hpos, hsol, hmem, hexit⟩ hY₀ae
  -- redefine on the null set `{τ ≠ ⊤}`
  have hAmeas : MeasurableSet {ω | τ ω ≠ ⊤} := by
    have : {ω | τ ω ≠ ⊤} = ⋃ n : ℕ, {ω | τ ω ≤ ((n : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      constructor
      · intro h
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 h
        obtain ⟨n, hn⟩ := exists_nat_ge r
        exact ⟨n, by rw [← hr]; exact_mod_cast hn⟩
      · rintro ⟨n, hn⟩ h
        rw [h] at hn
        exact absurd hn (by simp)
    rw [this]
    exact MeasurableSet.iUnion fun n => ℱ.le _ _ (hstop (n : ℝ))
  have hA0 : P {ω | τ ω ≠ ⊤} = 0 := ae_iff.1 htop
  have hAt : ∀ t : ℝ, MeasurableSet[ℱ t] {ω | τ ω = ⊤} := fun t => by
    have := (hBF.complete t _ hAmeas hA0).compl
    have e : {ω | τ ω = ⊤} = {ω | τ ω ≠ ⊤}ᶜ := by ext ω; simp
    rw [e]
    exact this
  let Yg : ℝ → Ω → Fin N → Euc d := fun t ω => if τ ω = ⊤ then Y t ω else Y₀ ω
  have hsolTop : IsAdditiveSDESolution P ℱ W' (fun _ Z => liftedDrift D Z) (liftedNoise D) Y₀
      (fun _ => ⊤) Yg := by
    refine ⟨fun t => ?_, fun ω => ?_, fun ω t ht _ => ?_, ?_⟩
    · let _ : MeasurableSpace Ω := ℱ t
      exact Measurable.ite (hAt t) (hsol.adapted t) (hY₀m t)
    · by_cases h : τ ω = ⊤
      · simp only [Yg, h, ↓reduceIte]; exact hsol.init ω
      · simp only [Yg, h, ↓reduceIte]
    · by_cases h : τ ω = ⊤
      · simp only [Yg, h, ↓reduceIte]
        exact hsol.cont ω t ht (by rw [h]; exact WithTop.coe_lt_top _)
      · simp only [Yg, h, ↓reduceIte]
        exact continuousOn_const
    · filter_upwards [hsol.eq, htop] with ω h1 h2 t ht _
      simp only [Yg, h2, ↓reduceIte]
      exact h1 t ht (by rw [h2]; exact WithTop.coe_lt_top _)
  have hfree : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Yg t ω ∈ liftedFree d N := by
    filter_upwards [htop] with ω h t ht
    simp only [Yg, h, ↓reduceIte]
    exact hmem ω t ht (by rw [h]; exact WithTop.coe_lt_top _)
  have hS := isStrongSolution_of_sde P ℱ D W hW W' hBF hWW' Y₀ Yg hsolTop hfree T
  refine ⟨_, { hS with init := ?_ }⟩
  filter_upwards [hS.init, hY₀ae] with ω h1 h2
  rw [h1]
  exact h2

/-- The uniform separation `B:eq:particle-uniform-separation` (M L11653-11655, L11990-11994):
for every strong solution on `[0,T]`, a.s. `min_{0≤t≤T} min_{i<j} dist(x_i^t, x_j^t) > 0`.
From `IsStrongSolution.no_collision` and `IsStrongSolution.cont`: a continuous positive
function on the compact `[0,T]` has a positive minimum. -/
theorem particle_uniform_separation (P : Measure Ω) [IsProbabilityMeasure P] (D : DynData d)
    (T : ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
    (X : ℝ≥0 → Ω → Config d N) (hX : IsStrongSolution P D T X₀ W X) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ i j : Fin N, i ≠ j →
      c ≤ Torus.tdist (X t ω i) (X t ω j) := by
  filter_upwards [hX.cont, hX.no_collision] with ω hcont hnc
  let S : Set ℝ≥0 := {t | (t : ℝ) ≤ T}
  let P : Set (Fin N × Fin N) := {p | p.1 ≠ p.2}
  have hS : IsCompact S := by
    refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (0 : ℝ≥0)) (b := Real.toNNReal T))
      (isClosed_le NNReal.continuous_coe continuous_const) fun t ht => ⟨bot_le, ?_⟩
    simpa using Real.toNNReal_mono (show (t : ℝ) ≤ T from ht)
  have hP : IsCompact P := (Set.toFinite P).isCompact
  let g : ℝ≥0 × (Fin N × Fin N) → ℝ := fun q => Torus.tdist (X q.1 ω q.2.1) (X q.1 ω q.2.2)
  have hg : Continuous g := by
    refine continuous_prod_of_discrete_right.2 fun p => ?_
    exact Torus.continuous_tdist_comp (hcont p.1) (hcont p.2)
  by_cases hne : (S ×ˢ P).Nonempty
  · obtain ⟨q, hq, hmin⟩ := (hS.prod hP).exists_isMinOn hne hg.continuousOn
    have hmin' : ∀ x ∈ S ×ˢ P, g q ≤ g x := fun x hx => isMinOn_iff.1 hmin x hx
    refine ⟨g q, ?_, fun t ht i j hij => ?_⟩
    · exact Torus.tdist_pos_of_ne fun h => hnc q.1 hq.1 ⟨q.2.1, q.2.2, hq.2, h⟩
    · have hmem : (t, (i, j)) ∈ S ×ˢ P := Set.mk_mem_prod ht hij
      have h5 := hmin' (t, (i, j)) hmem
      simp only [g] at h5
      exact h5
  · refine ⟨1, one_pos, fun t ht i j hij => ?_⟩
    exact absurd ⟨(t, (i, j)), ht, hij⟩ hne

end Probabilistic

/-- **Proposition B.1 `B:thm:particle-wp`, case (i)** (M L11645-11656, L11989-12000), with
exactly the statement of `HRS.particle_wellposed` (`HRS/Dynamics/Setup.lean`): for `N ≥ 2`,
`0 ≤ s < d`, `Sym M ≤ 0`, `V ∈ C²`, a.s. pairwise distinct `X₀` independent of `W`, and
`d ≥ 2`, the particle system has a collision-free strong solution on `[0,T]` and is pathwise
unique there.  Existence: `exists_isStrongSolution_of_maximal` with `particle_no_collision_dge2`;
uniqueness: `pathwiseUnique_of_locLipschitz` with `liftedDrift_locLipschitz`. -/
theorem particle_wellposed_proof {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData d) (hd : 2 ≤ d) (hN : 2 ≤ N)
    (hM : Torus.SymNonpos D.M) (hV : Torus.IsCk 2 D.V)
    (X₀ : Ω → Config d N) (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hW : IsVectorBrownian P W)
    (hind : ProbabilityTheory.IndepFun X₀ (fun ω => fun t => W t ω) P) (T : ℝ) (hT : 0 < T) :
    (∃ X, IsStrongSolution P D T X₀ W X) ∧ PathwiseUnique P D T X₀ W := by
  have hK : KernelLocal d D.s := kernelLocal_of_two_le hd D.hs0 D.hsd
  have hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) :=
    liftedDrift_locLipschitz D hK.smoothOffZero hV
  refine ⟨?_, pathwiseUnique_of_locLipschitz P D hb T X₀ W hW⟩
  refine exists_isStrongSolution_of_maximal P D hb X₀ hX₀ hdist W hW hind ?_ T
  intro ℱ W' hW' _ Y₀ τ Y hsol _
  exact (particle_no_collision_dge2 D hd hM hV hW' hsol).2

/-- **Proposition B.1 `B:thm:particle-wp`, case (ii)** (M L11649): `d = 1`, `β_N = ∞`
(`invβ = 0`), `N ≥ 2`, `0 ≤ s < 1`, `Sym M ≤ 0`, `V ∈ C²`; same conclusion as case (i).
Uses the `d = 1` kernel inputs (`kernelLocal_d1`). -/
theorem particle_wellposed_d1_zero_temp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData 1) (hN : 2 ≤ N) (hM : Torus.SymNonpos D.M)
    (hV : Torus.IsCk 2 D.V) (hβ : D.invβ = 0)
    (X₀ : Ω → Config 1 N) (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    (W : ℝ≥0 → Ω → (Fin N → Euc 1)) (hW : IsVectorBrownian P W)
    (hind : ProbabilityTheory.IndepFun X₀ (fun ω => fun t => W t ω) P) (T : ℝ) (hT : 0 < T) :
    (∃ X, IsStrongSolution P D T X₀ W X) ∧ PathwiseUnique P D T X₀ W := by
  have hs1 : D.s < 1 := by simpa using D.hsd
  have hK : KernelLocal 1 D.s := kernelLocal_d1 D.hs0 hs1
  have hb : IsLocLipschitzDrift (liftedFree 1 N) (fun _ Z => liftedDrift D Z) :=
    liftedDrift_locLipschitz D hK.smoothOffZero hV
  refine ⟨?_, pathwiseUnique_of_locLipschitz P D hb T X₀ W hW⟩
  refine exists_isStrongSolution_of_maximal P D hb X₀ hX₀ hdist W hW hind ?_ T
  intro ℱ W' hW' _ Y₀ τ Y hsol _
  exact particle_no_collision_d1 D hM hV (Or.inl hβ) hW' hsol

/-- **Proposition B.1 `B:thm:particle-wp`, case (iii)** (M L11650): `d = 1`, `β_N < ∞`
(`invβ > 0`), `0 < s < 1`, `M = -a` with `a > 0`, `N ≥ 2`, `Sym M ≤ 0`, `V ∈ C²`; same
conclusion as case (i).  Uses the `d = 1` kernel inputs (`kernelLocal_d1`). -/
theorem particle_wellposed_d1_riesz {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (D : DynData 1) (hN : 2 ≤ N) (hM : Torus.SymNonpos D.M)
    (hV : Torus.IsCk 2 D.V) (hβ : 0 < D.invβ) (hs0 : 0 < D.s) (ha : D.M 0 0 < 0)
    (X₀ : Ω → Config 1 N) (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    (W : ℝ≥0 → Ω → (Fin N → Euc 1)) (hW : IsVectorBrownian P W)
    (hind : ProbabilityTheory.IndepFun X₀ (fun ω => fun t => W t ω) P) (T : ℝ) (hT : 0 < T) :
    (∃ X, IsStrongSolution P D T X₀ W X) ∧ PathwiseUnique P D T X₀ W := by
  have hs1 : D.s < 1 := by simpa using D.hsd
  have hK : KernelLocal 1 D.s := kernelLocal_d1 D.hs0 hs1
  have hb : IsLocLipschitzDrift (liftedFree 1 N) (fun _ Z => liftedDrift D Z) :=
    liftedDrift_locLipschitz D hK.smoothOffZero hV
  refine ⟨?_, pathwiseUnique_of_locLipschitz P D hb T X₀ W hW⟩
  refine exists_isStrongSolution_of_maximal P D hb X₀ hX₀ hdist W hW hind ?_ T
  intro ℱ W' hW' _ Y₀ τ Y hsol _
  exact particle_no_collision_d1 D hM hV (Or.inr ⟨hβ, hs0, ha⟩) hW' hsol

end HRS
