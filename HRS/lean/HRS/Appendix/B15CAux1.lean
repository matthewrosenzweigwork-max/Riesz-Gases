import HRS.Appendix.B15Aux1
import HRS.Appendix.B15Aux2
import HRS.Kernel.D1
import HRS.Kernel.GradSmooth

/-!
# Packet B15-C: force regularisation `g_ε`, regularised dynamics `X^ε`, convergences `ε → 0`

Source: Proposition B.15 (`M:B:prop:sde-entropy-law`), TeX M L12140-12235 (statement L12140-12152, proof
L12153-12235); Steps 1-4 L12157-12232.  Plan: "2026-10-16 plan for the M external cluster", packet C.

Section A  `b15c_phi`, `b15c_trunc`, `b15c_cap`: the smooth vertical truncation profile (proved).
Section B  kernel inputs unified for `1 ≤ d` (`g → +∞` at `0`, `g` bounded above off a ball, ...; proved).
Section C  `b15c_gReg`: the regularised kernel `g_ε`: smooth, even, `≤ g`, monotone, `= g` off balls,
           uniformly bounded below (all proved).
Section D  `b15c_potentialOf`, `b15c_potentialReg`: `U^ε_{N,V}`: `≤ U`, monotone, eventually `= U`, lower
           bound, `C^n` (proved).
Section E  `b15c_gibbsWeightGen/PartitionGen/RefGen/EntropyGen`: Gibbs objects with a potential argument,
           with the bridges to `gibbsWeight/gibbsPartition/gibbsRef/gibbsEntropy` (proved).
Section F  `b15c_liftedDriftReg`, the regularised drift, drift agreement (proved), gradient structure
           (SORRIED), Lipschitz property (SORRIED), existence of `X^ε` (proved from the Lipschitz sorry),
           `X^ε = X` on `[0,T]` eventually (`b15c_regularised_eq_strong`, SORRIED).
Section G  law convergence of time marginals (proved from the previous), spacetime convergence (SORRIED),
           Step 3 (`G_ε ≥ G`, domination, `L¹` and partition convergence, uniform bounds, normalised
           densities `L¹`; all proved), Step 4 local equality of potentials on compacts and eventual
           equality of the Fisher integrands (proved), `𝓗_{G_ε} ≤ 𝓗_G` (SORRIED).

Sorried statements: `b15c_fderiv_potentialReg`, `b15c_liftedDriftReg_isLipschitz`,
`b15c_regularised_eq_strong`, `b15c_spacetime_tendsto`, `b15c_gibbsEntropyGen_le`.  (Plus, inherited
from packet A0 and used through `b15_periodicRiesz_lower`: `b15_periodicRiesz_ge_d1`.)

## Representation decisions (see also the docstrings)

* **Vertical truncation instead of a radial cutoff.**  The TeX (L12157-12159) chooses "smooth even kernels
  `g_ε` which agree with `g` outside `B(0,2ε)`, `g_ε ≤ g`, increasing pointwise to `g` off the diagonal,
  `∇g_ε` globally Lipschitz".  Here `g_M := trunc_M ∘ g` (with the value `cap M` at `0`), where
  `trunc_M(u) = u - ∫_0^{u-M} smoothTransition` is smooth, nondecreasing, `≤ id`, `= id` on `(-∞, M]`
  and constant on `[M+1, ∞)`.  Since `g(x) → +∞` as `x → 0`, `g_M` is constant near `0`, hence smooth on
  the torus; `g_M = g` on `{g ≤ M}`, which contains `{tdist x 0 ≥ r}` as soon as `M ≥ sup_{tdist ≥ r} g`
  (`b15c_gReg_eventually_eq_off_ball`, the substitute for "agrees with `g` outside `B(0, 2ε)`").  The
  family is indexed by the *level* `M` (`M = ε⁻¹` or any `M → ∞`); the pointwise monotonicity in `M` is
  `b15c_gReg_mono`.  Everything Steps 1-4 use is stated below.
* **The TeX claim `g_ε ≥ 0 when s > 0` is not reproduced**: with the repository's normalisation
  `ĝ(0) = 0` (`rieszCoeff d s 0 = 0`) the kernel has mean zero, so `g` (and every `g_ε` agreeing with `g`
  off a small ball) takes negative values.  Only a *uniform lower bound* `g_M ≥ -B` is used in Step 3
  ("dominated by a constant"); this is `b15c_gReg_ge` (from `b15_periodicRiesz_lower`).
* `V ∈ C²` only (hypothesis of B.15), so `U^ε` is `C²`, not `C^∞` (`b15c_potentialReg_contDiff`);
  the "smooth gradient SDE" of Step 1 has a `C¹` globally Lipschitz drift.  Packets D1-D3 must work with
  `C²` potentials, or (the adopted plan, since the D1 specs in `PDE/TorusFPSpec.lean` require a smooth
  `U`) packet E mollifies `V_δ → V` in `C²` at fixed level and lets `δ → 0` before the level limit.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

/-! ## Section A: the smooth vertical truncation profile -/

/-- `Φ(x) = ∫_0^x smoothTransition`, a smooth nondecreasing function, `0` on `(-∞,0]`, `Φ(x) = Φ(1) + x - 1`
on `[1,∞)`. -/
def b15c_phi (x : ℝ) : ℝ := ∫ v in (0 : ℝ)..x, Real.smoothTransition v

theorem b15c_phi_hasDerivAt (x : ℝ) : HasDerivAt b15c_phi (Real.smoothTransition x) x :=
  (Real.smoothTransition.continuous.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem b15c_phi_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b15c_phi := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (b15c_phi_hasDerivAt x).differentiableAt, ?_⟩
  have : deriv b15c_phi = Real.smoothTransition := funext fun x => (b15c_phi_hasDerivAt x).deriv
  rw [this]
  exact Real.smoothTransition.contDiff

theorem b15c_phi_of_nonpos {x : ℝ} (hx : x ≤ 0) : b15c_phi x = 0 := by
  unfold b15c_phi
  rw [intervalIntegral.integral_symm, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
  · simp
  · intro v hv
    rw [Set.uIcc_of_le hx] at hv
    exact Real.smoothTransition.zero_of_nonpos hv.2

theorem b15c_phi_nonneg (x : ℝ) : 0 ≤ b15c_phi x := by
  rcases le_total x 0 with hx | hx
  · rw [b15c_phi_of_nonpos hx]
  · exact intervalIntegral.integral_nonneg hx fun v _ => Real.smoothTransition.nonneg v

theorem b15c_phi_le_of_nonneg {x : ℝ} (hx : 0 ≤ x) : b15c_phi x ≤ x := by
  have h : b15c_phi x ≤ ∫ v in (0 : ℝ)..x, (1 : ℝ) :=
    intervalIntegral.integral_mono_on hx
      (Real.smoothTransition.continuous.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) fun v _ => Real.smoothTransition.le_one v
  simpa using h

theorem b15c_phi_mono : Monotone b15c_phi := by
  refine monotone_of_deriv_nonneg (fun x => (b15c_phi_hasDerivAt x).differentiableAt) fun x => ?_
  rw [(b15c_phi_hasDerivAt x).deriv]
  exact Real.smoothTransition.nonneg x

theorem b15c_phi_of_one_le {x : ℝ} (hx : 1 ≤ x) : b15c_phi x = b15c_phi 1 + (x - 1) := by
  unfold b15c_phi
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (Real.smoothTransition.continuous.intervalIntegrable 0 1)
    (Real.smoothTransition.continuous.intervalIntegrable 1 x)]
  congr 1
  rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))]
  · simp
  · intro v hv
    rw [Set.uIcc_of_le hx] at hv
    exact Real.smoothTransition.one_of_one_le hv.1

/-- The truncation profile at level `M`: `trunc_M(u) = u - Φ(u - M)`.  Smooth in `u`, nondecreasing,
`≤ u`, equal to `u` for `u ≤ M`, constant `M + 1 - Φ(1)` for `u ≥ M + 1`, nondecreasing in `M`. -/
def b15c_trunc (M u : ℝ) : ℝ := u - b15c_phi (u - M)

/-- The constant value of `trunc_M` on `[M+1, ∞)` (and the value of `g_M` at `0`). -/
def b15c_cap (M : ℝ) : ℝ := M + 1 - b15c_phi 1

theorem b15c_trunc_of_le {M u : ℝ} (h : u ≤ M) : b15c_trunc M u = u := by
  unfold b15c_trunc
  rw [b15c_phi_of_nonpos (by linarith)]; ring

theorem b15c_trunc_le (M u : ℝ) : b15c_trunc M u ≤ u := by
  unfold b15c_trunc; linarith [b15c_phi_nonneg (u - M)]

theorem b15c_min_le_trunc (M u : ℝ) : min u M ≤ b15c_trunc M u := by
  rcases le_total u M with h | h
  · rw [b15c_trunc_of_le h]; exact min_le_left _ _
  · have := b15c_phi_le_of_nonneg (x := u - M) (by linarith)
    unfold b15c_trunc
    exact (min_le_right _ _).trans (by linarith)

theorem b15c_trunc_of_cap {M u : ℝ} (h : M + 1 ≤ u) : b15c_trunc M u = b15c_cap M := by
  unfold b15c_trunc b15c_cap
  rw [b15c_phi_of_one_le (by linarith)]; ring

theorem b15c_trunc_mono_level {M M' : ℝ} (h : M ≤ M') (u : ℝ) : b15c_trunc M u ≤ b15c_trunc M' u := by
  unfold b15c_trunc
  have := b15c_phi_mono (show u - M' ≤ u - M by linarith)
  linarith

theorem b15c_trunc_contDiff (M : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (b15c_trunc M) := by
  unfold b15c_trunc
  exact contDiff_id.sub (b15c_phi_contDiff.comp (contDiff_id.sub contDiff_const))

theorem b15c_le_cap (M : ℝ) : M ≤ b15c_cap M := by
  unfold b15c_cap
  have : b15c_phi 1 ≤ 1 := b15c_phi_le_of_nonneg zero_le_one
  linarith

theorem b15c_cap_mono {M M' : ℝ} (h : M ≤ M') : b15c_cap M ≤ b15c_cap M' := by
  unfold b15c_cap; linarith


/-! ## Section B: kernel inputs, unified for `1 ≤ d` -/

section KernelInputs

variable {s : ℝ}

theorem b15c_mk_zero : (Torus.mk (0 : Euc d)) = 0 := by
  funext i; simp [Torus.mk]

theorem b15c_isSmooth_continuous {φ : Torus d → ℝ} (h : Torus.IsSmooth φ) : Continuous φ :=
  b15_continuous_of_isCk (show Torus.IsCk 2 φ from
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from h)
      (by norm_cast))

/-- Local singularity at `0`, unified in the four cases `d = 1 / d ≥ 2`, `s = 0 / s > 0`
(`periodicRiesz_local_singularity`, `periodicLog_local_singularity` and their `_d1` versions):
`g(mk y) = sing ‖y‖ + r(mk y)` for `0 < ‖y‖ < δ`, `r` smooth, `sing(u) → +∞` as `u → 0+`
(`sing u = u^{-s}` or `-log u`). -/
theorem b15c_local_sing (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (sing : ℝ → ℝ) (r : Torus d → ℝ) (δ : ℝ),
      (∀ A : ℝ, ∃ δ1 : ℝ, 0 < δ1 ∧ ∀ u : ℝ, 0 < u → u < δ1 → A ≤ sing u) ∧
      0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) = sing ‖x‖ + r (Torus.mk x) := by
  rcases eq_or_lt_of_le hs0 with h0 | hpos
  · subst h0
    have hlog : ∀ A : ℝ, ∃ δ1 : ℝ, 0 < δ1 ∧ ∀ u : ℝ, 0 < u → u < δ1 → A ≤ -Real.log u := by
      intro A
      refine ⟨Real.exp (-A), Real.exp_pos _, fun u hu hlt => ?_⟩
      have := Real.log_lt_log hu hlt
      rw [Real.log_exp] at this
      linarith
    rcases hd.eq_or_lt with h1 | h2
    · subst h1
      obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicLog_local_singularity_d1
      exact ⟨fun u => -Real.log u, r, δ, hlog, hδ, hr, hloc⟩
    · obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicLog_local_singularity (d := d) (by omega)
      exact ⟨fun u => -Real.log u, r, δ, hlog, hδ, hr, hloc⟩
  · have hpow : ∀ A : ℝ, ∃ δ1 : ℝ, 0 < δ1 ∧ ∀ u : ℝ, 0 < u → u < δ1 → A ≤ u ^ (-s) := by
      intro A
      set A' := max A 1 with hA'
      have hA'pos : 0 < A' := lt_of_lt_of_le one_pos (le_max_right _ _)
      refine ⟨A' ^ (-(1 / s)), Real.rpow_pos_of_pos hA'pos _, fun u hu hlt => ?_⟩
      have h1 : (A' ^ (-(1 / s))) ^ (-s) < u ^ (-s) :=
        Real.rpow_lt_rpow_of_neg hu hlt (by linarith)
      have h2 : (A' ^ (-(1 / s))) ^ (-s) = A' := by
        rw [← Real.rpow_mul hA'pos.le]
        have : -(1 / s) * -s = 1 := by field_simp
        rw [this, Real.rpow_one]
      rw [h2] at h1
      exact (le_max_left A 1).trans h1.le
    rcases hd.eq_or_lt with h1 | h2
    · subst h1
      have hs1 : s < 1 := by simpa using hsd
      obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity_d1 hpos hs1
      exact ⟨fun u => u ^ (-s), r, δ, hpow, hδ, hr, hloc⟩
    · obtain ⟨r, δ, hδ, hr, hloc⟩ := periodicRiesz_local_singularity (d := d) (by omega) hpos hsd
      exact ⟨fun u => u ^ (-s), r, δ, hpow, hδ, hr, hloc⟩

/-- `g(x) → +∞` as `x → 0`: for every `A` there is `δ > 0` with `g(mk y) ≥ A` for `0 < ‖y‖ < δ`
(`y ∈ ℝ^d`, `y ≠ 0`; the value at lattice points other than `0` is covered by periodicity). -/
theorem b15c_periodicRiesz_large_near_zero (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (A : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : Euc d, y ≠ 0 → ‖y‖ < δ → A ≤ periodicRiesz d s (Torus.mk y) := by
  obtain ⟨sing, r, δ0, hsing, hδ0, hr, hloc⟩ := b15c_local_sing hd hs0 hsd
  obtain ⟨R, hR⟩ := b15_bounded_of_continuous (b15c_isSmooth_continuous hr)
  obtain ⟨δ1, hδ1, h1⟩ := hsing (A + R)
  refine ⟨min δ0 δ1, lt_min hδ0 hδ1, fun y hy hlt => ?_⟩
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  rw [hloc y (lt_of_lt_of_le hlt (min_le_left _ _)) hy]
  have := h1 ‖y‖ hpos (lt_of_lt_of_le hlt (min_le_right _ _))
  have := neg_abs_le (r (Torus.mk y))
  have := hR (Torus.mk y)
  linarith

/-- `g∘mk` is `C^∞` at every `y` with `mk y ≠ 0`, for all `d ≥ 1` (`KernelD1Aux.contDiffAt_lift_g`). -/
theorem b15c_contDiffAt_lift_periodicRiesz (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {y : Euc d}
    (hy : Torus.mk y ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (periodicRiesz d s)) y :=
  KernelD1Aux.contDiffAt_lift_g hd hs0 hsd y (fun m => KernelGrad.wsq_pos_of_mk_ne_zero hy m)

theorem b15c_mk_ne_zero_of_box {y : Euc d} (hy : ∀ i, |y i| ≤ 1 / 2) (hy0 : y ≠ 0) :
    Torus.mk y ≠ 0 := by
  intro h
  apply hy0
  ext i
  have h1 : Torus.mk y i = 0 := by rw [h]; rfl
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).1 h1
  have hn' : (n : ℝ) = y i := by simpa using hn
  have h2 : |(n : ℝ)| ≤ 1 / 2 := by rw [hn']; exact hy i
  have h3 : n = 0 := by
    have : |n| < 1 := by
      have : |(n : ℝ)| < 1 := by linarith
      exact_mod_cast this
    exact Int.abs_lt_one_iff.mp this
  rw [← hn', h3]; simp

/-- `g` is bounded above away from `0`: `sup_{tdist x 0 ≥ r} g < ∞` (compactness of the box minus a ball
and continuity of `g` off `0`). -/
theorem b15c_periodicRiesz_bddAbove_off_ball (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {r : ℝ}
    (hr : 0 < r) : ∃ C : ℝ, ∀ x : Torus d, r ≤ Torus.tdist x 0 → periodicRiesz d s x ≤ C := by
  set K : Set (Euc d) := {y | (∀ i, |y i| ≤ 1 / 2) ∧ r ≤ ‖y‖} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine IsClosed.inter (s₁ := {y : Euc d | ∀ i, |y i| ≤ 1 / 2}) (s₂ := {y : Euc d | r ≤ ‖y‖}) ?_
        (isClosed_le continuous_const continuous_norm)
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Euc d)) (r := d)).subset fun y hy => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      exact KernelGrad.norm_le_card_of_box hy.1
  have hcont : ContinuousOn (Torus.lift (periodicRiesz d s)) K := by
    intro y hy
    have hy0 : y ≠ 0 := by
      intro h
      have h2 : r ≤ ‖y‖ := hy.2
      rw [h, norm_zero] at h2; exact absurd h2 (not_le.mpr hr)
    exact (b15c_contDiffAt_lift_periodicRiesz hd hs0 hsd
      (b15c_mk_ne_zero_of_box hy.1 hy0)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨y, hyx, hybox⟩ := KernelGrad.exists_mk_box x
  have hnorm : ‖y‖ = Torus.tdist x 0 := by
    rw [← hyx]; exact (KernelGrad.tdist_mk hybox).symm
  have hyK : y ∈ K := ⟨hybox, by rw [hnorm]; exact hx⟩
  have := hC y hyK
  rw [← hyx]
  exact (le_abs_self _).trans (by simpa [Torus.lift] using this)

end KernelInputs

/-! ## Section C: the regularised kernel `g_M` -/

open Classical in
/-- The regularised kernel at level `M` (TeX `g_ε`, L12157-12159; `M = ε⁻¹`): `trunc_M ∘ g` off `0`,
and the constant `cap M` at `0` (where `periodicRiesz` has a junk value).  See the module docstring. -/
def b15c_gReg (d : ℕ) (s M : ℝ) (x : Torus d) : ℝ :=
  if x = 0 then b15c_cap M else b15c_trunc M (periodicRiesz d s x)

theorem b15c_gReg_zero (d : ℕ) (s M : ℝ) : b15c_gReg d s M 0 = b15c_cap M := by
  simp [b15c_gReg]

theorem b15c_gReg_of_ne {x : Torus d} (s M : ℝ) (hx : x ≠ 0) :
    b15c_gReg d s M x = b15c_trunc M (periodicRiesz d s x) := by
  simp [b15c_gReg, hx]

/-- `g_M` is even (as `g`, `periodicRiesz_neg`; TeX "smooth even kernels"). -/
theorem b15c_gReg_neg (s M : ℝ) (x : Torus d) : b15c_gReg d s M (-x) = b15c_gReg d s M x := by
  by_cases hx : x = 0
  · subst hx; simp
  · have : -x ≠ 0 := neg_ne_zero.mpr hx
    rw [b15c_gReg_of_ne s M this, b15c_gReg_of_ne s M hx, periodicRiesz_neg]

/-- `g_M ≤ g` off `0` (TeX `g_ε ≤ g`). -/
theorem b15c_gReg_le {x : Torus d} (s M : ℝ) (hx : x ≠ 0) : b15c_gReg d s M x ≤ periodicRiesz d s x := by
  rw [b15c_gReg_of_ne s M hx]; exact b15c_trunc_le _ _

/-- `g_M = g` on `{g ≤ M}`. -/
theorem b15c_gReg_eq_of_le {x : Torus d} (s M : ℝ) (hx : x ≠ 0) (h : periodicRiesz d s x ≤ M) :
    b15c_gReg d s M x = periodicRiesz d s x := by
  rw [b15c_gReg_of_ne s M hx]; exact b15c_trunc_of_le h

/-- Monotone in the level: `g_M ↑ g` as `M ↑ ∞` (TeX "increase pointwise to `g` off the diagonal"). -/
theorem b15c_gReg_mono (s : ℝ) (x : Torus d) {M M' : ℝ} (h : M ≤ M') :
    b15c_gReg d s M x ≤ b15c_gReg d s M' x := by
  by_cases hx : x = 0
  · subst hx; rw [b15c_gReg_zero, b15c_gReg_zero]; exact b15c_cap_mono h
  · rw [b15c_gReg_of_ne s M hx, b15c_gReg_of_ne s M' hx]; exact b15c_trunc_mono_level h _

/-- Pointwise convergence `g_M(x) → g(x)` as `M → ∞` for `x ≠ 0` (eventual equality). -/
theorem b15c_gReg_eventuallyEq {x : Torus d} (s : ℝ) (hx : x ≠ 0) :
    ∀ᶠ M in atTop, b15c_gReg d s M x = periodicRiesz d s x :=
  (eventually_ge_atTop (periodicRiesz d s x)).mono fun _ h => b15c_gReg_eq_of_le s _ hx h

/-- The uniform lower bound used in Step 3 (TeX: "the regularized weights are dominated by a constant",
L12186): if `g ≥ -B` (`B ≥ 0`) then `g_M ≥ -B` for every level `M ≥ 0`.  This replaces the TeX claim
`g_ε ≥ 0` (false for the mean-zero kernel, see the module docstring). -/
theorem b15c_gReg_ge (s : ℝ) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M) (hg : ∀ z : Torus d, -B ≤ periodicRiesz d s z)
    (x : Torus d) : -B ≤ b15c_gReg d s M x := by
  by_cases hx : x = 0
  · subst hx; rw [b15c_gReg_zero]; linarith [b15c_le_cap M]
  · rw [b15c_gReg_of_ne s M hx]
    exact le_trans (le_min (hg x) (by linarith)) (b15c_min_le_trunc M _)

/-- **`g_M` is `C^∞` on the torus** (the smoothness requirement of D1-D3).  Off `0`: `trunc_M ∘ g`
with `g` smooth (`b15c_contDiffAt_lift_periodicRiesz`); near any lattice point: `g ≥ M + 1`
(`b15c_periodicRiesz_large_near_zero`), so `trunc_M ∘ g = cap M` is locally constant. -/
theorem b15c_gReg_isSmooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    Torus.IsSmooth (b15c_gReg d s M) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : Torus.mk y = 0
  · obtain ⟨δ, hδ, hlarge⟩ := b15c_periodicRiesz_large_near_zero hd hs0 hsd (M + 1)
    have hev : ∀ᶠ y' in 𝓝 y, Torus.lift (b15c_gReg d s M) y' = b15c_cap M := by
      filter_upwards [Metric.ball_mem_nhds y hδ] with y' hy'
      have hz : ‖y' - y‖ < δ := by simpa [dist_eq_norm] using hy'
      have hmk : Torus.mk y' = Torus.mk (y' - y) := by
        rw [KernelGrad.mk_sub, hy, sub_zero]
      show b15c_gReg d s M (Torus.mk y') = _
      rw [hmk]
      by_cases hz0 : Torus.mk (y' - y) = 0
      · rw [hz0, b15c_gReg_zero]
      · have hne : y' - y ≠ 0 := fun h => hz0 (by rw [h]; exact b15c_mk_zero)
        rw [b15c_gReg_of_ne s M hz0]
        exact b15c_trunc_of_cap (hlarge _ hne hz)
    exact (contDiffAt_const (c := b15c_cap M)).congr_of_eventuallyEq hev
  · have hopen : IsOpen {y : Euc d | Torus.mk y ≠ 0} :=
      isOpen_compl_singleton.preimage Torus.continuous_mk
    have h1 := (b15c_trunc_contDiff M).contDiffAt.comp y (b15c_contDiffAt_lift_periodicRiesz hd hs0 hsd hy)
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hy] with y' hy'
    show b15c_gReg d s M (Torus.mk y') = _
    rw [b15c_gReg_of_ne s M hy']
    rfl

/-- **`g_M = g` away from a small ball**: for every `r > 0` there is `M₀` such that for all levels
`M ≥ M₀` and all `x` with `tdist x 0 ≥ r`, `g_M x = g x`.  Substitute for TeX "agree with `g` outside
`B(0,2ε)`" (take `r = 2ε` and `M₀ = sup_{tdist ≥ 2ε} g`): uniform in `x`, hence also all derivatives
agree on the open set `{tdist > r}` (`b15c_grad_gReg_eq` for the gradient). -/
theorem b15c_gReg_eventually_eq_off_ball (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {r : ℝ}
    (hr : 0 < r) :
    ∃ M₀ : ℝ, ∀ M, M₀ ≤ M → ∀ x : Torus d, r ≤ Torus.tdist x 0 → b15c_gReg d s M x = periodicRiesz d s x := by
  obtain ⟨C, hC⟩ := b15c_periodicRiesz_bddAbove_off_ball hd hs0 hsd hr
  refine ⟨C, fun M hM x hx => ?_⟩
  have hx0 : x ≠ 0 := by
    intro h
    have : Torus.tdist x 0 = 0 := by
      subst h
      have h0 := KernelGrad.tdist_mk (d := d) (y := 0) (by simp)
      rw [b15c_mk_zero, norm_zero] at h0
      exact h0
    linarith
  exact b15c_gReg_eq_of_le s M hx0 ((hC x hx).trans hM)


/-! ## Section D: the regularised potential `U^ε_{N,V}` -/

/-- `U(X) = (1/2N) ∑_{i≠j} g(x_i - x_j) + ∑_i V(x_i)` for an arbitrary kernel `g`
(`B:eq:particle-total-potential`, TeX M L12006, and the display of Step 2, L12171-12173). -/
def b15c_potentialOf (g V : Torus d → ℝ) (X : Config d N) : ℝ :=
  (1 / (2 * (N : ℝ))) * ∑ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j) + ∑ i, V (X i)

/-- `totalPotential` is `b15c_potentialOf` at the Riesz kernel. -/
theorem b15c_totalPotential_eq_potentialOf (D : DynData d) (X : Config d N) :
    totalPotential D X = b15c_potentialOf (periodicRiesz d D.s) D.V X := rfl

/-- `U^ε_{N,V} := (1/2N) ∑_{i≠j} g_ε(x_i - x_j) + ∑_i V(x_i)` (TeX Step 2, L12171-12173) at level `M`.
Defined on *all* of `Config d N` (no collision indicator: `g_M` is bounded). -/
def b15c_potentialReg (D : DynData d) (M : ℝ) : Config d N → ℝ :=
  b15c_potentialOf (b15c_gReg d D.s M) D.V

theorem b15c_potentialOf_eq_hamiltonian {g V : Torus d → ℝ} (hg : ∀ z, g (-z) = g z) (X : Config d N) :
    b15c_potentialOf g V X = canonicalHamiltonian g V X := by
  unfold b15c_potentialOf canonicalHamiltonian
  rw [b15_sum_erase_eq (fun i j => g (X i - X j)) (fun i j => by
    rw [← hg (X i - X j), neg_sub])]
  rw [add_comm]
  congr 1
  rcases N.eq_zero_or_pos with h0 | hN
  · subst h0; simp
  · have : (N : ℝ) ≠ 0 := by positivity
    field_simp

/-- `U^ε ≤ U` off the collision set (TeX: `g_ε ≤ g`; gives `G_{N,ε} ≥ G_{N,β_N,V}^𝔻`, used for the
last inequality of `B:eq:selected-regularized-entropy`, L12177). -/
theorem b15c_potentialReg_le (D : DynData d) (M : ℝ) {X : Config d N} (hX : X ∉ collisionSet d N) :
    b15c_potentialReg D M X ≤ totalPotential D X := by
  unfold b15c_potentialReg
  rw [b15c_totalPotential_eq_potentialOf]
  unfold b15c_potentialOf
  refine add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j hj => ?_) (by positivity)) le_rfl
  have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
  have hne : X i - X j ≠ 0 := sub_ne_zero.mpr fun h => hX ⟨i, j, hij, h⟩
  exact b15c_gReg_le D.s M hne

/-- Monotone in the level: `U^ε ↑ U` as `ε ↓ 0`. -/
theorem b15c_potentialReg_mono (D : DynData d) {M M' : ℝ} (h : M ≤ M') (X : Config d N) :
    b15c_potentialReg D M X ≤ b15c_potentialReg D M' X := by
  unfold b15c_potentialReg b15c_potentialOf
  exact add_le_add (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun j _ => b15c_gReg_mono D.s _ h) (by positivity)) le_rfl

/-- Pointwise convergence off the collision set: `U^ε(X) = U(X)` for all large levels. -/
theorem b15c_potentialReg_eventuallyEq (D : DynData d) {X : Config d N} (hX : X ∉ collisionSet d N) :
    ∀ᶠ M in atTop, b15c_potentialReg D M X = totalPotential D X := by
  have h : ∀ᶠ M in atTop, ∀ i : Fin N, ∀ j ∈ Finset.univ.erase i,
      b15c_gReg d D.s M (X i - X j) = periodicRiesz d D.s (X i - X j) := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all_finset]
    intro j hj
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    exact b15c_gReg_eventuallyEq D.s (sub_ne_zero.mpr fun h => hX ⟨i, j, hij, h⟩)
  filter_upwards [h] with M hM
  unfold b15c_potentialReg
  rw [b15c_totalPotential_eq_potentialOf]
  unfold b15c_potentialOf
  congr 2
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => hM i j hj

/-- Uniform lower bound `U^ε ≥ -(N‖V‖_∞ + N B)` for levels `M ≥ 0` (Step 3: the regularised weights
"are dominated by a constant"). -/
theorem b15c_potentialReg_ge (D : DynData d) {B Vm M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hg : ∀ z, -B ≤ periodicRiesz d D.s z) (hV : ∀ x, |D.V x| ≤ Vm) (X : Config d N) :
    -((N : ℝ) * Vm + N * B) ≤ b15c_potentialReg D M X := by
  unfold b15c_potentialReg
  rw [b15c_potentialOf_eq_hamiltonian (b15c_gReg_neg D.s M)]
  exact b15_hamiltonian_lower hB (b15c_gReg_ge D.s hB hM hg) hV X

/-- `U^ε` is `C^n` as a function on the covering space `(ℝ^d)^N` (through `Y ↦ mk ∘ Y`) whenever
`V ∈ C^n`, `n ≤ ∞` (`g_M` is `C^∞`).  Since B.15 assumes only `V ∈ C²`, `n = 2` is what the hypotheses
give; see the module docstring. -/
theorem b15c_potentialReg_contDiff (D : DynData d) {n : WithTop ℕ∞}
    (hn : n ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)) (hV : Torus.IsCk n D.V) (M : ℝ) :
    ContDiff ℝ n (fun Y : Fin N → Euc d => b15c_potentialReg D M (fun i => Torus.mk (Y i))) := by
  have hg : ContDiff ℝ n (Torus.lift (b15c_gReg d D.s M)) :=
    ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift (b15c_gReg d D.s M)) from
      b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M) hn
  have hV' : ContDiff ℝ n (Torus.lift D.V) := hV
  unfold b15c_potentialReg b15c_potentialOf
  refine ContDiff.add (contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_))
    (ContDiff.sum fun i _ => ?_)
  · have : (fun Y : Fin N → Euc d => b15c_gReg d D.s M (Torus.mk (Y i) - Torus.mk (Y j))) =
        (Torus.lift (b15c_gReg d D.s M)) ∘ (fun Y : Fin N → Euc d => Y i - Y j) := by
      funext Y; simp [Torus.lift, KernelGrad.mk_sub]
    simp only [this]
    exact hg.comp ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j))
  · exact hV'.comp (contDiff_apply ℝ (Euc d) i)

/-! ## Section E: Gibbs weights, partition functions and entropies with a potential argument -/

/-- The Gibbs weight `exp(-β U)` for a potential `U` (`β = invβ⁻¹`), *without* a collision indicator:
the weight `G_{N,ε} = e^{-β_N U^ε_{N,V}}` of Step 2 (TeX L12173-12174). -/
def b15c_gibbsWeightGen (invβ : ℝ) (U : Config d N → ℝ) (X : Config d N) : ℝ :=
  Real.exp (-(invβ⁻¹) * U X)

/-- Partition function `Z = ∫ G dX` (`lintegral`, as `gibbsPartition`). -/
def b15c_gibbsPartitionGen (invβ : ℝ) (U : Config d N → ℝ) : ℝ≥0∞ :=
  ∫⁻ X : Config d N, ENNReal.ofReal (b15c_gibbsWeightGen invβ U X)

/-- The normalised Gibbs measure `Z⁻¹ G dX` (`Q_{N,ε}` of Step 4, TeX L12195). -/
def b15c_gibbsRefGen (invβ : ℝ) (U : Config d N → ℝ) : Measure (Config d N) :=
  (b15c_gibbsPartitionGen invβ U)⁻¹ •
    (volume : Measure (Config d N)).withDensity fun X => ENNReal.ofReal (b15c_gibbsWeightGen invβ U X)

/-- `𝓗_G(P) = H(P | Z⁻¹ G dX) - log Z` for the weight `G = exp(-β U)` (same convention as
`gibbsEntropy`, `B:eq:gibbs-entropy-measure-convention`; the identity `H(P|Q_{N,ε}) = 𝓗_{G_{N,ε}}(P) +
log Z_{N,ε}` of TeX L12198 is the definition). -/
def b15c_gibbsEntropyGen (invβ : ℝ) (U : Config d N → ℝ) (P : Measure (Config d N)) : EReal :=
  ((relEntropy P (b15c_gibbsRefGen invβ U) : ℝ≥0∞) : EReal) -
    ((Real.log (b15c_gibbsPartitionGen invβ U).toReal : ℝ) : EReal)

/-- The collision indicator is invisible for the Gibbs partition (the collision set is null). -/
theorem b15c_gibbsPartition_eq_gen (D : DynData d) :
    gibbsPartition D N = b15c_gibbsPartitionGen D.invβ (totalPotential (N := N) D) := by
  have hd := b15_one_le_d D
  unfold gibbsPartition b15c_gibbsPartitionGen
  refine lintegral_congr_ae ?_
  filter_upwards [b15_ae_not_collision (d := d) (N := N) hd] with X hX
  classical
  simp only [gibbsWeight, b15c_gibbsWeightGen, hX, ↓reduceIte]

/-- `gibbsRef D N = b15c_gibbsRefGen D.invβ (totalPotential (N := N) D)`. -/
theorem b15c_gibbsRef_eq_gen (D : DynData d) :
    gibbsRef D N = b15c_gibbsRefGen D.invβ (totalPotential (N := N) D) := by
  have hd := b15_one_le_d D
  unfold gibbsRef b15c_gibbsRefGen
  rw [b15c_gibbsPartition_eq_gen]
  congr 1
  refine withDensity_congr_ae ?_
  filter_upwards [b15_ae_not_collision (d := d) (N := N) hd] with X hX
  classical
  simp only [gibbsWeight, b15c_gibbsWeightGen, hX, ↓reduceIte]

/-- `gibbsEntropy D = b15c_gibbsEntropyGen D.invβ (totalPotential D)`. -/
theorem b15c_gibbsEntropy_eq_gen (D : DynData d) (P : Measure (Config d N)) :
    gibbsEntropy D P = b15c_gibbsEntropyGen D.invβ (totalPotential (N := N) D) P := by
  unfold gibbsEntropy b15c_gibbsEntropyGen
  rw [b15c_gibbsRef_eq_gen, b15c_gibbsPartition_eq_gen]


/-! ## Section F: the regularised dynamics `X^ε` (Step 1, TeX L12157-12166) -/

/-- The lifted particle drift with an arbitrary force kernel `G : 𝕋^d → ℝ^d`:
`b_i(Y) = N⁻¹ ∑_{j≠i} M G(y_i - y_j) - ∇V(y_i)` on the covering space `(ℝ^d)^N`.  With
`G = periodicRieszGrad` this is `liftedDrift D` (`b15c_liftedDrift_eq`). -/
def b15c_liftedDriftOf (D : DynData d) (G : Torus d → Euc d) (Y : Fin N → Euc d) : Fin N → Euc d :=
  fun i => (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
      Torus.matVec D.M (G (Torus.mk (Y i) - Torus.mk (Y j))) - Torus.grad D.V (Torus.mk (Y i))

theorem b15c_liftedDrift_eq (D : DynData d) :
    (liftedDrift D : (Fin N → Euc d) → Fin N → Euc d) =
      b15c_liftedDriftOf D (periodicRieszGrad d D.s) := rfl

/-- The drift of the regularised ("smooth gradient") SDE of Step 1, at level `M`: the force kernel is
`∇g_M = Torus.grad (g_M)`, which is `C^∞`, bounded with bounded derivatives (`g_M` smooth and periodic).
The SDE is `dY = b^M(Y) dt + √(2 invβ) dW` (`liftedNoise D`). -/
def b15c_liftedDriftReg (D : DynData d) (M : ℝ) : (Fin N → Euc d) → Fin N → Euc d :=
  b15c_liftedDriftOf D (Torus.grad (b15c_gReg d D.s M))

/-- `∇g_M = ∇g` (`Torus.grad` of the lift) for `x ≠ 0`, all `d ≥ 1`: `periodicRieszGrad` is the gradient
of the lift of `periodicRiesz` away from `0`.  `d ≥ 2`: `KernelGrad.periodicRieszGrad_hasGradientAt`;
`d = 1`: assembled from `KernelD1Aux.hasDerivAt_g_ev` and `KernelD1Aux.hasDerivAt_lift_ev`. -/
theorem b15c_periodicRieszGrad_eq_grad (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {z : Torus d}
    (hz : z ≠ 0) : Torus.grad (periodicRiesz d s) z = periodicRieszGrad d s z := by
  rcases hd.eq_or_lt with h1 | h2
  · subst h1
    have hs1 : s < 1 := by simpa using hsd
    set y : ℝ := (Torus.rep z) 0 with hy
    have hx : Torus.rep z = KernelD1Aux.ev y := KernelD1Aux.ev_eq _
    have hmk : Torus.mk (KernelD1Aux.ev y) = z := by rw [← hx, Torus.mk_rep]
    have hy0 : ∀ n : ℤ, y ≠ n :=
      KernelD1Aux.off_int_of_mk_ne (x := Torus.rep z) (by rw [Torus.mk_rep]; exact hz)
    have h1 := KernelD1Aux.hasDerivAt_g_ev hs0 hs1 hy0
    rw [hmk] at h1
    have hdiff : DifferentiableAt ℝ (Torus.lift (periodicRiesz 1 s)) (KernelD1Aux.ev y) :=
      (b15c_contDiffAt_lift_periodicRiesz (by norm_num) hs0 hsd (by rw [hmk]; exact hz)).differentiableAt
        (by simp)
    have h2 := KernelD1Aux.hasDerivAt_lift_ev hdiff
    have h3 := h2.unique (by simpa [Torus.lift] using h1)
    show gradient (Torus.lift (periodicRiesz 1 s)) (Torus.rep z) = _
    rw [hx]
    ext i; fin_cases i; simpa using h3
  · have h := KernelGrad.periodicRieszGrad_hasGradientAt (d := d) (s := s) (by omega) hs0 hsd hz
      (Torus.rep z) (Torus.mk_rep z)
    exact h.gradient

theorem b15c_tdist_sub_zero (x y : Torus d) : Torus.tdist (x - y) 0 = Torus.tdist x y := by
  simp [Torus.tdist]

theorem b15c_tdist_zero_right_zero : Torus.tdist (0 : Torus d) 0 = 0 := by
  have h0 := KernelGrad.tdist_mk (d := d) (y := 0) (by simp)
  rw [b15c_mk_zero, norm_zero] at h0
  exact h0

/-- `∇g_M = ∇g` on `{tdist z 0 ≥ r}` for all large levels, uniformly in `z`: `g_M = g` on the open set
`{tdist > r/2}` (`b15c_gReg_eventually_eq_off_ball`), so the gradients coincide, and
`∇g = periodicRieszGrad` there (`b15c_periodicRieszGrad_eq_grad`). -/
theorem b15c_grad_gReg_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {r : ℝ} (hr : 0 < r) :
    ∃ M₀ : ℝ, ∀ M, M₀ ≤ M → ∀ z : Torus d, r ≤ Torus.tdist z 0 →
      Torus.grad (b15c_gReg d s M) z = periodicRieszGrad d s z := by
  obtain ⟨M₀, hM₀⟩ := b15c_gReg_eventually_eq_off_ball hd hs0 hsd (half_pos hr)
  refine ⟨M₀, fun M hM z hz => ?_⟩
  have hz0 : z ≠ 0 := by
    intro h; subst h; rw [b15c_tdist_zero_right_zero] at hz; linarith
  rw [← b15c_periodicRieszGrad_eq_grad hd hs0 hsd hz0]
  unfold Torus.grad
  have hopen : IsOpen {y : Euc d | r / 2 < Torus.tdist (Torus.mk y) 0} :=
    isOpen_lt continuous_const (Torus.continuous_tdist_comp Torus.continuous_mk continuous_const)
  have hmem : Torus.rep z ∈ {y : Euc d | r / 2 < Torus.tdist (Torus.mk y) 0} := by
    show r / 2 < Torus.tdist (Torus.mk (Torus.rep z)) 0
    rw [Torus.mk_rep]; linarith
  have hev : Torus.lift (b15c_gReg d s M) =ᶠ[𝓝 (Torus.rep z)] Torus.lift (periodicRiesz d s) := by
    filter_upwards [hopen.mem_nhds hmem] with y hy
    exact hM₀ M hM _ (le_of_lt hy)
  unfold gradient
  rw [hev.fderiv_eq]

/-- **Drift agreement away from collisions** (TeX L12162-12166: the regularised and singular drifts
coincide while the pair distances stay away from `0`): for every `r > 0` there is a level `M₀` such that for
all `M ≥ M₀` and all `Y ∈ (ℝ^d)^N` all of whose pair distances `tdist (y_i) (y_j) ≥ r`,
`b^M(Y) = b(Y)` (`liftedDrift D`).  Proved from `b15c_grad_gReg_eq`. -/
theorem b15c_liftedDriftReg_eq_of_sep (D : DynData d) {r : ℝ} (hr : 0 < r) :
    ∃ M₀ : ℝ, ∀ M, M₀ ≤ M → ∀ Y : Fin N → Euc d,
      (∀ i j, i ≠ j → r ≤ Torus.tdist (Torus.mk (Y i)) (Torus.mk (Y j))) →
        b15c_liftedDriftReg D M Y = liftedDrift D Y := by
  obtain ⟨M₀, hM₀⟩ := b15c_grad_gReg_eq (b15_one_le_d D) D.hs0 D.hsd hr
  refine ⟨M₀, fun M hM Y hY => ?_⟩
  have key : ∀ i : Fin N, ∀ j ∈ Finset.univ.erase i,
      Torus.grad (b15c_gReg d D.s M) (Torus.mk (Y i) - Torus.mk (Y j)) =
        periodicRieszGrad d D.s (Torus.mk (Y i) - Torus.mk (Y j)) := fun i j hj =>
    hM₀ M hM _ (by rw [b15c_tdist_sub_zero]; exact hY i j (Finset.mem_erase.mp hj).1.symm)
  rw [b15c_liftedDrift_eq]
  funext i
  unfold b15c_liftedDriftReg b15c_liftedDriftOf
  rw [Finset.sum_congr rfl fun j hj => by rw [key i j hj]]

/-- `Σ_i ⟪b^M_i(Y), v_i⟫` form of the gradient structure: for `M_D = -I` (`ζ_BM = -I`) the regularised
drift is `-∇U^ε`, i.e. `D(U^ε∘mk)(Y)[v] = -∑_i ⟪b^M_i(Y), v_i⟫`.  This is what makes the generator of the
smooth SDE `β⁻¹ G_ε⁻¹ Div(G_ε ∇)` (TeX L12174-12175) and is the input of the entropy identity (D3).
STATEMENT (sorried: product/chain rule, oddness of `∇g_M` and periodicity of `Torus.grad`). -/
theorem b15c_fderiv_potentialReg (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV : Torus.IsCk 2 D.V) (M : ℝ) (Y : Fin N → Euc d) (v : Fin N → Euc d) :
    fderiv ℝ (fun Z : Fin N → Euc d => b15c_potentialReg D M (fun i => Torus.mk (Z i))) Y v =
      -∑ i, inner ℝ (b15c_liftedDriftReg D M Y i) (v i) := by
  sorry

/-- The regularised drift is globally Lipschitz (uniformly in time; it is time-independent), for
`V ∈ C²`: `Torus.grad g_M` is `C^∞` and periodic hence bounded with bounded derivative, and `∇V` is
`C¹` and periodic.  This is the hypothesis of `exists_sde_solution_global`.  STATEMENT (sorried). -/
theorem b15c_liftedDriftReg_isLipschitz (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ) :
    IsLipschitzDrift (fun _ : ℝ => (b15c_liftedDriftReg D M : (Fin N → Euc d) → Fin N → Euc d)) := by
  sorry

/-- The torus-level regularised process `X^ε_t = mk ∘ Y^ε_t` (the notation `X_N^ε` of Step 1). -/
def b15c_regProcess {Ω : Type*} (Y : ℝ → Ω → (Fin N → Euc d)) : ℝ≥0 → Ω → Config d N :=
  projectPath fun t ω => Y (t : ℝ) ω

/-- **Existence of `X^ε`** (TeX L12159-12160: "Let `X_N^ε` solve the corresponding smooth gradient SDE with
the same initial random variable and Brownian motions as `X_N`").  The lifted regularised SDE has a global
strong solution `Y` (`IsAdditiveSDESolution`, additive noise, `τ = ⊤`), pathwise unique, for every
Brownian filtration `(ℱ, W')` and every initial lift `Y₀` adapted at all times; `X^ε = b15c_regProcess Y`.
In the assembly take `W'` the filtration coordinates of `hF : IsFilteredSolution P ℱ W' W X` and
`Y₀ = rep ∘ X 0` (`X 0` is `ℱ 0`-measurable by `hF.adapted`; a.s. `= X₀`).  Note the hypothesis
`∀ t : ℝ, Measurable[ℱ t] Y₀` is the one of `exists_sde_solution_global`, for *all real* `t`; the
assembly packet must supply a filtration with this property (e.g. `ℱ t := ℱ (max t 0)`) since
`IsFilteredSolution.adapted` constrains only `t : ℝ≥0`. -/
theorem b15c_exists_regularised_solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    (D : DynData d) (hV : Torus.IsCk 2 D.V) (M : ℝ) (Y₀ : Ω → Fin N → Euc d)
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) :
    ∃ Y : ℝ → Ω → (Fin N → Euc d),
      IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀ (fun _ => ⊤) Y ∧
      ∀ Y' : ℝ → Ω → (Fin N → Euc d),
        IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D M) (liftedNoise D) Y₀
          (fun _ => ⊤) Y' → ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω = Y' t ω :=
  exists_sde_solution_global hW' _ (b15c_liftedDriftReg_isLipschitz D hV M) (liftedNoise D) Y₀ hY₀

/-- **`X^ε = X` on `[0,T]` for all large `ε⁻¹`** (TeX Step 1, L12160-12166, the displayed convergence
`B:eq:selected-pathlaw-convergence`): if `X` is a collision-free strong solution on `[0,T]` and
`Y^{M_n}` are the global solutions of the regularised SDEs at levels `M_n → ∞` driven by the same Brownian
motion (`hWW'`) with an initial lift of `X₀`, then almost surely `X^{M_n} = X` on `[0,T]` for all large `n`.

Representation.  (i) A *sequence* of levels instead of a real `ε`: for uncountably many `ε` each solution
holds off its own null set; a sequence gives the a.s. statement with a single null set, and is all that the
weak-convergence statements of Step 4 need.  (ii) The TeX argument "stopped pathwise uniqueness" is
formalised as a deterministic Gronwall argument for the lifted equations (additive noise; after
`IsPathSolution.congr_drift` and the drift agreement
`b15c_liftedDriftReg_eq_of_sep`: along `X` the regularised drift equals the singular one, so the lift of
`X` is also a pathwise solution of the *globally Lipschitz* regularised equation, and uniqueness
`ode_additive_unique` with `U = univ`, `IsLipschitzDrift.toLoc`, applies), with the a.s. positive minimal
pair distance `c(ω)` from
`particle_uniform_separation` (TeX `B:eq:particle-uniform-separation`), because `X^ε` is not known to be
collision-free (so it is not an `IsStrongSolution` and `PathwiseUnique` does not apply to it directly).
(iii) `Y₀` is any lift of `X₀` (`hY₀`): lifts differ by lattice vectors and the drifts are periodic.
STATEMENT, sorried (size M). -/
theorem b15c_regularised_eq_strong
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (D : DynData d) (hV : Torus.IsCk 2 D.V) {T : ℝ}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hW : IsVectorBrownian P W)
    {X : ℝ≥0 → Ω → Config d N} (hS : IsStrongSolution P D T X₀ W X)
    (hWW' : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j)
    {Y₀ : Ω → Fin N → Euc d} (hY₀ : ∀ᵐ ω ∂P, (fun i => Torus.mk (Y₀ ω i)) = X₀ ω)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop)
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω := by
  sorry

/-! ## Section G: the convergences `ε → 0` of Steps 1, 3, 4 -/

theorem b15c_regProcess_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {b : ℝ → (Fin N → Euc d) → (Fin N → Euc d)} {σ : (Fin N × Fin d) → (Fin N → Euc d)}
    {Y₀ : Ω → Fin N → Euc d} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' b σ Y₀ (fun _ => ⊤) Y) (t : ℝ≥0) :
    Measurable (b15c_regProcess Y t) := by
  have h1 : Measurable (Y (t : ℝ)) := (hY.adapted (t : ℝ)).mono (ℱ.le _) le_rfl
  exact measurable_pi_iff.mpr fun i => Torus.continuous_mk.measurable.comp (measurable_pi_apply i |>.comp h1)

/-- Convergence of integrals from a.s. eventual equality (generic). -/
theorem b15c_integral_tendsto_of_eventually_eq
    {Ω α : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace α] {P : Measure Ω} [IsProbabilityMeasure P]
    {Xn : ℕ → Ω → α} {X : Ω → α} (hXn : ∀ n, Measurable (Xn n)) (hX : Measurable X)
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Xn n ω = X ω) {φ : α → ℝ} (hφ : Measurable φ) {C : ℝ}
    (hC : ∀ x, |φ x| ≤ C) :
    Tendsto (fun n => ∫ x, φ x ∂(P.map (Xn n))) atTop (𝓝 (∫ x, φ x ∂(P.map X))) := by
  have e : ∀ Z : Ω → α, Measurable Z → ∫ x, φ x ∂(P.map Z) = ∫ ω, φ (Z ω) ∂P := fun Z hZ =>
    integral_map hZ.aemeasurable hφ.aestronglyMeasurable
  simp only [e _ (hXn _), e _ hX]
  refine tendsto_integral_of_dominated_convergence (fun _ => C)
    (fun n => (hφ.comp (hXn n)).aestronglyMeasurable) (integrable_const C)
    (fun n => Filter.Eventually.of_forall fun ω => by simpa using hC _) ?_
  filter_upwards [h] with ω hω
  exact tendsto_const_nhds.congr' (hω.mono fun n hn => by show _ = φ (Xn n ω); rw [hn])

/-- **Weak convergence of the time marginals** (TeX `B:eq:selected-pathlaw-convergence`, second
statement, L12166): for every `t ∈ [0,T]` and every continuous `φ : (𝕋^d)^N → ℝ`,
`∫ φ dP^t_{N,ε_n} → ∫ φ dP^t_N`, where `P^t_{N,ε} = Law(X^ε_t) = selectedLaw P X^ε t`.
(The configuration space is compact, so continuous `φ` is bounded: this is convergence against
`C_b`.)  Proved from `b15c_regularised_eq_strong`'s conclusion (hypothesis `hev`). -/
theorem b15c_marginal_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} {Y₀ : Ω → Fin N → Euc d} {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {φ : Config d N → ℝ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ x, φ x ∂(selectedLaw P (b15c_regProcess (Y n)) t)) atTop
      (𝓝 (∫ x, φ x ∂(selectedLaw P X t))) := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hφ.continuousOn
  have hle : ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ T := by
    rw [Real.coe_toNNReal t ht0]; exact htT
  refine b15c_integral_tendsto_of_eventually_eq (fun n => b15c_regProcess_measurable (hY n) _)
    (hS.adapted _) ?_ hφ.measurable (C := C) (fun x => by simpa using hC x (mem_univ x))
  filter_upwards [hev] with ω hω
  filter_upwards [hω] with n hn using hn _ hle

/-- **Convergence of the spacetime laws** (TeX Step 4: "the convergence of the spacetime laws", L12218):
for `t ∈ [0,T]` and continuous `ψ : ℝ × (𝕋^d)^N → ℝ`,
`∫_0^t ∫ ψ(r,·) dP^r_{N,ε_n} dr → ∫_0^t ∫ ψ(r,·) dP^r_N dr`.  This is the form in which the variational
Fisher functional (`b15_fisherInfoGen`, with `ζ` time-independent, or `ψ(r,x) = integrand_r(x)`) passes to
the limit; packet B (lower semicontinuity) consumes it.  STATEMENT (sorried): dominated convergence in
`r`, with measurability of `r ↦ ∫ ψ(r,·) dP^r_{N,ε}` from path continuity of `X^ε`
(`IsAdditiveSDESolution.cont`) and of `X` (`IsStrongSolution.cont`). -/
theorem b15c_spacetime_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} {Y₀ : Ω → Fin N → Euc d} {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {ψ : ℝ → Config d N → ℝ}
    (hψ : Continuous (Function.uncurry ψ)) :
    Tendsto (fun n => ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ψ r x ∂(selectedLaw P (b15c_regProcess (Y n)) r))
      atTop (𝓝 (∫ r in Set.Icc (0 : ℝ) t, ∫ x, ψ r x ∂(selectedLaw P X r))) := by
  sorry


/-! ### Step 3: convergence of the Gibbs weights (TeX L12183-12187) -/

theorem b15c_potentialReg_continuous (D : DynData d) (hV : Continuous D.V) (M : ℝ) :
    Continuous (b15c_potentialReg (N := N) D M) := by
  have hg : Continuous (b15c_gReg d D.s M) :=
    b15c_isSmooth_continuous (b15c_gReg_isSmooth (b15_one_le_d D) D.hs0 D.hsd M)
  unfold b15c_potentialReg b15c_potentialOf
  refine Continuous.add (continuous_const.mul (continuous_finset_sum _ fun i _ =>
    continuous_finset_sum _ fun j _ => ?_)) (continuous_finset_sum _ fun i _ => ?_)
  · exact hg.comp ((continuous_apply i).sub (continuous_apply j))
  · exact hV.comp (continuous_apply i)

theorem b15c_measurable_gibbsWeight (D : DynData d) (hV : Continuous D.V) :
    Measurable (gibbsWeight (N := N) D) := by
  have hd := b15_one_le_d D
  have hg := CoercAux.measurable_periodicRiesz_one (d := d) (s := D.s) hd D.hs0 D.hsd
  have hU : Measurable (totalPotential (N := N) D) := by
    unfold totalPotential
    refine Measurable.add (measurable_const.mul (Finset.measurable_sum _ fun i _ =>
      Finset.measurable_sum _ fun j _ => ?_)) (Finset.measurable_sum _ fun i _ =>
        hV.measurable.comp (measurable_pi_apply i))
    exact hg.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  classical
  unfold gibbsWeight
  exact Measurable.ite (isClosed_collisionSet d N).measurableSet measurable_const
    (Real.measurable_exp.comp (measurable_const.mul hU))

/-- `G_{N,ε} ≥ G_{N,β_N,V}^𝔻` (TeX L12177, "The final inequality uses `G_{N,ε} ≥ G`"), at every `X`
(on the collision set the right-hand side is `0`). -/
theorem b15c_gibbsWeight_le_reg (D : DynData d) (hβ : 0 < D.invβ) (M : ℝ) (X : Config d N) :
    gibbsWeight D X ≤ b15c_gibbsWeightGen D.invβ (b15c_potentialReg D M) X := by
  classical
  unfold gibbsWeight
  by_cases hX : X ∈ collisionSet d N
  · simp only [hX, ↓reduceIte]; exact (Real.exp_pos _).le
  · simp only [hX, ↓reduceIte]
    unfold b15c_gibbsWeightGen
    refine Real.exp_le_exp.mpr ?_
    have := b15c_potentialReg_le D M hX
    have hβ' : 0 < D.invβ⁻¹ := inv_pos.mpr hβ
    nlinarith

/-- The regularised weights are dominated by a constant, uniformly in the level `M ≥ 0` (TeX L12186). -/
theorem b15c_gibbsWeightReg_le_const (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) :
    ∃ C : ℝ, ∀ M : ℝ, 0 ≤ M → ∀ X : Config d N,
      b15c_gibbsWeightGen D.invβ (b15c_potentialReg D M) X ≤ C := by
  obtain ⟨B, hB⟩ := b15_periodicRiesz_lower D
  obtain ⟨Vm, hVm⟩ := b15_bounded_of_continuous (b15_continuous_of_isCk hV)
  set B' := max B 0
  have hB' : ∀ z, -B' ≤ periodicRiesz d D.s z := fun z => (neg_le_neg (le_max_left _ _)).trans (hB z)
  refine ⟨Real.exp (D.invβ⁻¹ * ((N : ℝ) * Vm + N * B')), fun M hM X => ?_⟩
  have hlow := b15c_potentialReg_ge D (le_max_right B 0) hM hB' hVm X
  unfold b15c_gibbsWeightGen
  refine Real.exp_le_exp.mpr ?_
  have hβ' : 0 < D.invβ⁻¹ := inv_pos.mpr hβ
  nlinarith

/-- Pointwise convergence of the weights off the collision set: `G_{N,ε}(X) = G(X)` for all large levels. -/
theorem b15c_gibbsWeightReg_eventuallyEq (D : DynData d) {X : Config d N} (hX : X ∉ collisionSet d N) :
    ∀ᶠ M in atTop, b15c_gibbsWeightGen D.invβ (b15c_potentialReg D M) X = gibbsWeight D X := by
  classical
  filter_upwards [b15c_potentialReg_eventuallyEq D hX] with M hM
  simp only [gibbsWeight, b15c_gibbsWeightGen, hX, ↓reduceIte, hM]

/-- **Step 3 (TeX L12183-12187)**: `G_{N,ε} → G_{N,β_N,V}^𝔻` in `L¹(dX)` (along levels `M_n → ∞`,
`M_n ≥ 0`): dominated convergence, with the constant bound `b15c_gibbsWeightReg_le_const`, and a.e.
(off the null collision set) eventual equality. -/
theorem b15c_gibbsWeightReg_tendsto_L1 (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) :
    Tendsto (fun n => ∫⁻ X : Config d N,
      ENNReal.ofReal ‖b15c_gibbsWeightGen D.invβ (b15c_potentialReg D (M n)) X - gibbsWeight D X‖)
      atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := b15c_gibbsWeightReg_le_const (N := N) D hβ hV
  have hVc := b15_continuous_of_isCk hV
  refine tendsto_lintegral_norm_of_dominated_convergence (bound := fun _ => C) ?_
    (integrable_const C).hasFiniteIntegral ?_ ?_
  · intro n
    exact (Real.measurable_exp.comp (measurable_const.mul
      (b15c_potentialReg_continuous D hVc (M n)).measurable)).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun X => ?_
    have hpos : 0 < b15c_gibbsWeightGen D.invβ (b15c_potentialReg D (M n)) X := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact hC _ (hM0 n) X
  · filter_upwards [b15_ae_not_collision (d := d) (N := N) (b15_one_le_d D)] with X hX
    have := (hM.eventually (b15c_gibbsWeightReg_eventuallyEq D hX))
    exact tendsto_const_nhds.congr' (this.mono fun n hn => hn.symm)

/-- The real partition function of the regularised weight equals the (real) integral of the weight. -/
theorem b15c_gibbsPartitionGen_toReal {U : Config d N → ℝ} (hU : Continuous U) (invβ : ℝ) :
    (b15c_gibbsPartitionGen invβ U).toReal = ∫ X, b15c_gibbsWeightGen invβ U X := by
  have hm : AEStronglyMeasurable (fun X => Real.exp (-invβ⁻¹ * U X)) volume :=
    (Real.measurable_exp.comp (measurable_const.mul hU.measurable)).aestronglyMeasurable
  unfold b15c_gibbsPartitionGen b15c_gibbsWeightGen
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le) hm]

theorem b15c_gibbsPartition_toReal (D : DynData d) (hV : Continuous D.V) :
    (gibbsPartition D N).toReal = ∫ X : Config d N, gibbsWeight D X := by
  have hm : AEStronglyMeasurable (gibbsWeight (N := N) D) volume :=
    (b15c_measurable_gibbsWeight (N := N) D hV).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume] gibbsWeight (N := N) D := Filter.Eventually.of_forall fun X => by
    classical
    unfold gibbsWeight; split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm]
  rfl

/-- **Step 4, first half (TeX L12192-12194)**: `Z_{N,ε_n} → Z_N` (real partition functions), with
`Z_N = (gibbsPartition D N).toReal`.  By the `L¹` convergence of the weights. -/
theorem b15c_partition_tendsto (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) :
    Tendsto (fun n => (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (M n))).toReal)
      atTop (𝓝 (gibbsPartition D N).toReal) := by
  obtain ⟨C, hC⟩ := b15c_gibbsWeightReg_le_const (N := N) D hβ hV
  have hVc := b15_continuous_of_isCk hV
  have hcont := fun n => b15c_potentialReg_continuous (N := N) D hVc (M n)
  simp only [b15c_gibbsPartitionGen_toReal (hcont _), b15c_gibbsPartition_toReal D hVc]
  refine tendsto_integral_of_dominated_convergence (fun _ => C) ?_ (integrable_const C) ?_ ?_
  · intro n
    exact (Real.measurable_exp.comp (measurable_const.mul
      (hcont n).measurable)).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun X => ?_
    have hpos : 0 < b15c_gibbsWeightGen D.invβ (b15c_potentialReg D (M n)) X := Real.exp_pos _
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    exact hC _ (hM0 n) X
  · filter_upwards [b15_ae_not_collision (d := d) (N := N) (b15_one_le_d D)] with X hX
    have := (hM.eventually (b15c_gibbsWeightReg_eventuallyEq D hX))
    exact tendsto_const_nhds.congr' (this.mono fun n hn => hn.symm)


/-- Uniform two-sided bounds on the regularised partition functions (TeX L12199-12202: "the right-hand side
is bounded below uniformly in `ε`", since `H(P|Q) ≥ 0` and `-log Z_{N,ε} ≥ -log C`): for all levels
`M ≥ 0`, `Z_N ≤ Z_{N,ε} ≤ C` and `0 < Z_N`. -/
theorem b15c_partition_bounds (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) :
    0 < (gibbsPartition D N).toReal ∧ ∃ C : ℝ, ∀ M : ℝ, 0 ≤ M →
      (gibbsPartition D N).toReal ≤ (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal ∧
      (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D M)).toReal ≤ C := by
  obtain ⟨hpos, hlt⟩ := b15_gibbsPartition_pos_lt_top (N := N) D hV hβ
  refine ⟨ENNReal.toReal_pos hpos.ne' hlt.ne, ?_⟩
  obtain ⟨C, hC⟩ := b15c_gibbsWeightReg_le_const (N := N) D hβ hV
  have hVc := b15_continuous_of_isCk hV
  refine ⟨C, fun M hM => ?_⟩
  have hcont := b15c_potentialReg_continuous (N := N) D hVc M
  rw [b15c_gibbsPartitionGen_toReal hcont, b15c_gibbsPartition_toReal D hVc]
  have hint : Integrable (b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M)) :=
    Integrable.mono' (integrable_const C)
      (Real.measurable_exp.comp (measurable_const.mul hcont.measurable)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by
        have hpos : 0 < b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X := Real.exp_pos _
        rw [Real.norm_eq_abs, abs_of_pos hpos]; exact hC _ hM X)
  have hGint : Integrable (gibbsWeight (N := N) D) :=
    Integrable.mono' hint (b15c_measurable_gibbsWeight D hVc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by
        have h0 : 0 ≤ gibbsWeight D X := by
          classical
          unfold gibbsWeight; split_ifs
          · exact le_rfl
          · exact (Real.exp_pos _).le
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
        exact b15c_gibbsWeight_le_reg D hβ M X)
  refine ⟨integral_mono hGint hint fun X => b15c_gibbsWeight_le_reg D hβ M X, ?_⟩
  have := norm_integral_le_of_norm_le_const (μ := (volume : Measure (Config d N)))
    (f := b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M)) (C := C)
    (Filter.Eventually.of_forall fun X => by
      have hpos : 0 < b15c_gibbsWeightGen D.invβ (b15c_potentialReg (N := N) D M) X := Real.exp_pos _
      rw [Real.norm_eq_abs, abs_of_pos hpos]; exact hC _ hM X)
  simp [Measure.real, measure_univ] at this
  exact (le_abs_self _).trans this

/-- **Step 4, TV convergence of the normalised Gibbs measures (TeX L12192-12194: "`Q_{N,ε} → Q_N` in total
variation")**, in the concrete form: the normalised densities `Z_{N,ε}⁻¹ G_{N,ε} → Z_N⁻¹ G` converge in
`L¹(dX)` (along `M_n → ∞`, `M_n ≥ 0`).  `Q_{N,ε} = b15c_gibbsRefGen _ U^ε` and `Q_N = gibbsRef D N` have these
densities (`b15c_gibbsRefGen_eq_withDensity`), and `sup_A |Q_{N,ε}(A) - Q_N(A)| ≤ ` this `L¹` norm. -/
theorem b15c_normDensity_tendsto_L1 (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) :
    Tendsto (fun n => ∫⁻ X : Config d N, ENNReal.ofReal ‖
        ((b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (M n))).toReal)⁻¹ *
          b15c_gibbsWeightGen D.invβ (b15c_potentialReg D (M n)) X -
        ((gibbsPartition D N).toReal)⁻¹ * gibbsWeight D X‖) atTop (𝓝 0) := by
  obtain ⟨hZpos, C, hZ⟩ := b15c_partition_bounds (N := N) D hβ hV
  obtain ⟨C', hC'⟩ := b15c_gibbsWeightReg_le_const (N := N) D hβ hV
  have hVc := b15_continuous_of_isCk hV
  have hZt := b15c_partition_tendsto (N := N) D hβ hV hM hM0
  refine tendsto_lintegral_norm_of_dominated_convergence
    (bound := fun _ => ((gibbsPartition D N).toReal)⁻¹ * C') ?_
    (integrable_const _).hasFiniteIntegral ?_ ?_
  · intro n
    exact (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      (b15c_potentialReg_continuous D hVc (M n)).measurable))).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun X => ?_
    have hpos : 0 < b15c_gibbsWeightGen D.invβ (b15c_potentialReg D (M n)) X := Real.exp_pos _
    have hZn := (hZ (M n) (hM0 n)).1
    have hZnpos : 0 < (b15c_gibbsPartitionGen D.invβ (b15c_potentialReg (N := N) D (M n))).toReal :=
      lt_of_lt_of_le hZpos hZn
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc _ ≤ ((gibbsPartition D N).toReal)⁻¹ *
          b15c_gibbsWeightGen D.invβ (b15c_potentialReg D (M n)) X := by
          gcongr
      _ ≤ _ := by gcongr; exact hC' _ (hM0 n) X
  · filter_upwards [b15_ae_not_collision (d := d) (N := N) (b15_one_le_d D)] with X hX
    have h1 := (hZt.inv₀ hZpos.ne')
    have h2 := (hM.eventually (b15c_gibbsWeightReg_eventuallyEq D hX))
    have h3 : Tendsto (fun n => b15c_gibbsWeightGen D.invβ (b15c_potentialReg D (M n)) X) atTop
        (𝓝 (gibbsWeight D X)) := tendsto_const_nhds.congr' (h2.mono fun n hn => hn.symm)
    exact h1.mul h3


/-- `Q_{N,ε} = Z⁻¹ G dX` has density `Z.toReal⁻¹ * G` (for `0 < Z < ∞`): the form in which the `L¹` statement
`b15c_normDensity_tendsto_L1` is a total-variation statement. -/
theorem b15c_gibbsRefGen_eq_withDensity (invβ : ℝ) (U : Config d N → ℝ)
    (hZ : b15c_gibbsPartitionGen invβ U ≠ ⊤) (hZ0 : b15c_gibbsPartitionGen invβ U ≠ 0) :
    b15c_gibbsRefGen invβ U = (volume : Measure (Config d N)).withDensity fun X =>
      ENNReal.ofReal ((b15c_gibbsPartitionGen invβ U).toReal⁻¹ * b15c_gibbsWeightGen invβ U X) := by
  unfold b15c_gibbsRefGen
  have hf : ∀ X : Config d N, ENNReal.ofReal ((b15c_gibbsPartitionGen invβ U).toReal⁻¹ *
      b15c_gibbsWeightGen invβ U X) =
      (b15c_gibbsPartitionGen invβ U)⁻¹ • ENNReal.ofReal (b15c_gibbsWeightGen invβ U X) := by
    intro X
    have hpos : 0 < (b15c_gibbsPartitionGen invβ U).toReal := ENNReal.toReal_pos hZ0 hZ
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le), ENNReal.ofReal_inv_of_pos hpos,
      ENNReal.ofReal_toReal hZ, smul_eq_mul]
  simp only [hf]
  exact (withDensity_smul' _ _ (ENNReal.inv_ne_top.mpr hZ0)).symm

/-! ### Step 4: the Fisher information and the local convergence of the potentials -/

/-- The integrand of the variational Fisher formula `B:eq:selected-fisher-variational`
(TeX L12205-12209) for the potential `U`; `b15_fisherInfoGen invβ U P = sup_ζ ∫ b15c_fisherIntegrand ... dP`
(`b15c_fisherInfoGen_eq`, `rfl`). -/
def b15c_fisherIntegrand (invβ : ℝ) (U : Config d N → ℝ) (ζ : Config d N → (Fin N → Euc d))
    (X : Config d N) : ℝ :=
  -2 * configDiv ζ X
    + 2 * invβ⁻¹ * fderiv ℝ (fun Z : Fin N → Euc d => U (fun i => Torus.mk (Z i)))
        (fun i => Torus.rep (X i)) (ζ X)
    - ∑ i, ‖ζ X i‖ ^ 2

theorem b15c_fisherInfoGen_eq (invβ : ℝ) (U : Config d N → ℝ) (P : Measure (Config d N)) :
    b15_fisherInfoGen invβ U P =
      ⨆ (ζ : Config d N → (Fin N → Euc d)) (_ : IsFisherTestField ζ),
        ENNReal.ofReal (∫ X, b15c_fisherIntegrand invβ U ζ X ∂P) := rfl

/-- A compact set of collision-free configurations has a uniform positive pair separation. -/
theorem b15c_exists_sep_of_compact {K : Set (Config d N)} (hK : IsCompact K)
    (hKd : Disjoint K (collisionSet d N)) :
    ∃ r : ℝ, 0 < r ∧ ∀ X ∈ K, ∀ i j : Fin N, i ≠ j → 2 * r ≤ Torus.tdist (X i) (X j) := by
  have hpos : ∀ X ∈ K, ∀ i j : Fin N, i ≠ j → 0 < Torus.tdist (X i) (X j) := by
    intro X hX i j hij
    refine Torus.tdist_pos_of_ne fun h => ?_
    exact Set.disjoint_left.mp hKd hX ⟨i, j, hij, h⟩
  set G : Config d N → ℝ := fun X => ∑ i, ∑ j ∈ Finset.univ.erase i, (Torus.tdist (X i) (X j))⁻¹ with hG
  have hGc : ContinuousOn G K := by
    refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j hj => ?_
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    refine ContinuousOn.inv₀ ?_ fun X hX => (hpos X hX i j hij).ne'
    exact (Torus.continuous_tdist_comp (continuous_apply i) (continuous_apply j)).continuousOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hGc
  refine ⟨1 / (2 * (|C| + 1)), by positivity, fun X hX i j hij => ?_⟩
  have ht := hpos X hX i j hij
  have h1 : (Torus.tdist (X i) (X j))⁻¹ ≤ G X := by
    have hnn : ∀ i : Fin N, ∀ j ∈ Finset.univ.erase i, 0 ≤ (Torus.tdist (X i) (X j))⁻¹ :=
      fun i j hj => inv_nonneg.mpr (norm_nonneg _)
    calc (Torus.tdist (X i) (X j))⁻¹ ≤ ∑ j ∈ Finset.univ.erase i, (Torus.tdist (X i) (X j))⁻¹ :=
          Finset.single_le_sum (f := fun j => (Torus.tdist (X i) (X j))⁻¹) (hnn i)
            (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩)
      _ ≤ G X := Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.univ.erase i, (Torus.tdist (X i) (X j))⁻¹)
            (fun i _ => Finset.sum_nonneg (hnn i)) (Finset.mem_univ i)
  have hGX : G X ≤ C := (le_abs_self (G X)).trans (by rw [← Real.norm_eq_abs]; exact hC X hX)
  have h2 : (Torus.tdist (X i) (X j))⁻¹ ≤ |C| + 1 :=
    h1.trans (hGX.trans (by linarith [le_abs_self C]))
  have h3 : 1 ≤ Torus.tdist (X i) (X j) * (|C| + 1) := by
    have := mul_le_mul_of_nonneg_left h2 ht.le
    rwa [mul_inv_cancel₀ ht.ne'] at this
  have hp : 0 < |C| + 1 := by positivity
  have e : 2 * (1 / (2 * (|C| + 1))) = (|C| + 1)⁻¹ := by field_simp
  rw [e]
  calc (|C| + 1)⁻¹ = (|C| + 1)⁻¹ * 1 := by ring
    _ ≤ (|C| + 1)⁻¹ * (Torus.tdist (X i) (X j) * (|C| + 1)) := by gcongr
    _ = Torus.tdist (X i) (X j) := by field_simp

/-- **Local equality of the potentials on compacts away from collisions** (TeX L12214-12216: "the local
`C¹` convergence `G_{N,ε} → G` on `Ω_N`"; here stronger: exact equality on a neighbourhood): for every compact
`K ⊆ Ω_N = 𝔇_N^c` there is a level `M₀` such that for all `M ≥ M₀` and `X ∈ K`, `U^ε = U` on a
neighbourhood of the lift of `X` in `(ℝ^d)^N` (hence all derivatives agree there). -/
theorem b15c_potential_eventuallyEq_nhds (D : DynData d) {K : Set (Config d N)} (hK : IsCompact K)
    (hKd : Disjoint K (collisionSet d N)) :
    ∃ M₀ : ℝ, ∀ M, M₀ ≤ M → ∀ X ∈ K, ∀ᶠ Z in 𝓝 (fun i => Torus.rep (X i)),
      b15c_potentialReg D M (fun i => Torus.mk (Z i)) = totalPotential D (fun i => Torus.mk (Z i)) := by
  obtain ⟨r, hr, hsep⟩ := b15c_exists_sep_of_compact hK hKd
  obtain ⟨M₀, hM₀⟩ := b15c_gReg_eventually_eq_off_ball (b15_one_le_d D) D.hs0 D.hsd hr
  refine ⟨M₀, fun M hM X hX => ?_⟩
  have hnb : ∀ᶠ Z in 𝓝 (fun i => Torus.rep (X i)),
      ∀ i j : Fin N, i ≠ j → r < Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j)) := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun Z h => absurd hij h
    · have hc : Continuous fun Z : Fin N → Euc d => Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j)) :=
        Torus.continuous_tdist_comp (Torus.continuous_mk.comp (continuous_apply i))
          (Torus.continuous_mk.comp (continuous_apply j))
      have h0 : r < (fun Z : Fin N → Euc d => Torus.tdist (Torus.mk (Z i)) (Torus.mk (Z j)))
          (fun i => Torus.rep (X i)) := by
        show r < Torus.tdist (Torus.mk (Torus.rep (X i))) (Torus.mk (Torus.rep (X j)))
        rw [Torus.mk_rep, Torus.mk_rep]; linarith [hsep X hX i j hij]
      have h1 := (hc.tendsto (fun i => Torus.rep (X i))).eventually (lt_mem_nhds h0)
      exact h1.mono fun Z h _ => h
  filter_upwards [hnb] with Z hZ
  unfold b15c_potentialReg
  rw [b15c_totalPotential_eq_potentialOf]
  unfold b15c_potentialOf
  congr 2
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
  exact hM₀ M hM _ (by rw [b15c_tdist_sub_zero]; exact (hZ i j hij).le)


/-- Consequence: the lifted differentials of `U^ε` and `U` agree on `K` for large levels. -/
theorem b15c_fderiv_potentialReg_eq (D : DynData d) {K : Set (Config d N)} (hK : IsCompact K)
    (hKd : Disjoint K (collisionSet d N)) :
    ∃ M₀ : ℝ, ∀ M, M₀ ≤ M → ∀ X ∈ K,
      fderiv ℝ (fun Z : Fin N → Euc d => b15c_potentialReg D M (fun i => Torus.mk (Z i)))
          (fun i => Torus.rep (X i)) =
        fderiv ℝ (fun Z : Fin N → Euc d => totalPotential D (fun i => Torus.mk (Z i)))
          (fun i => Torus.rep (X i)) := by
  obtain ⟨M₀, h⟩ := b15c_potential_eventuallyEq_nhds D hK hKd
  exact ⟨M₀, fun M hM X hX => Filter.EventuallyEq.fderiv_eq (h M hM X hX)⟩

/-- **The Fisher integrands converge (are eventually equal), for each fixed test field** (TeX L12205-12216:
"The local `C¹` convergence `G_{N,ε} → G` on `Ω_N`, the convergence of the spacetime laws, and a countable
exhaustion of `Ω_N` therefore imply `B:eq:selected-fisher-lsc-bound`"): for `ζ ∈ C_c^∞(Ω_N; ℝ^{dN})`
(`IsFisherTestField`) there is `M₀` such that for all `M ≥ M₀` the integrand of the variational formula for
`U^ε` coincides *everywhere* with that for `U` (outside `supp ζ` both reduce to the `U`-independent terms).
Combined with `b15c_spacetime_tendsto` (taking `ψ(r,x)` = the integrand) this is exactly what the
lower-semicontinuity argument of packet B needs: for every fixed `ζ`, the `ε`-dependent functional
`∫_0^t ∫ integrand_ε(ζ) dP_ε^r dr` converges to the `ε = 0` one. -/
theorem b15c_fisherIntegrand_eventuallyEq (D : DynData d) {ζ : Config d N → (Fin N → Euc d)}
    (hζ : IsFisherTestField ζ) :
    ∃ M₀ : ℝ, ∀ M, M₀ ≤ M → ∀ X : Config d N,
      b15c_fisherIntegrand D.invβ (b15c_potentialReg D M) ζ X =
        b15c_fisherIntegrand D.invβ (totalPotential D) ζ X := by
  obtain ⟨K, hKc, hKd, hK0⟩ := hζ.support
  obtain ⟨M₀, h⟩ := b15c_fderiv_potentialReg_eq D hKc hKd
  refine ⟨M₀, fun M hM X => ?_⟩
  unfold b15c_fisherIntegrand
  by_cases hX : X ∈ K
  · rw [h M hM X hX]
  · have h0 : ζ X = 0 := hK0 X hX
    rw [h0]
    simp

/-- **Step 2, last inequality (TeX L12176-12177)**: `𝓗_{G_{N,ε}}(P) ≤ 𝓗_G(P)` for every probability measure
`P`, because `G_{N,ε} ≥ G`: `𝓗_G(P) - 𝓗_{G_ε}(P) = ∫ log(G_ε/G) dP ≥ 0` (for `P ≪ Q` both sides are
`∫ f log(f/G)`-type integrals; if `P` is not `≪` the Gibbs measure, the right-hand side is `+∞`).  Used for
`𝓗_{G_{N,ε}}(f_N^0) ≤ 𝓗_G(f_N^0)` (here `P = law X_0`).  STATEMENT, sorried (`klDiv` manipulation).  With
`Q_ε ∼ Q ∼ dX` and `llr(P|Q_ε) = llr(P|Q) + log(G/G_ε) + log(Z_ε/Z)`, where `log(G/G_ε) ≤ 0` and
`Z_ε ≤ C` (`b15c_partition_bounds`), the positive part of `llr(P|Q_ε)` is dominated by that of `llr(P|Q)`
plus a constant, and the negative part is automatically integrable for probability measures
(`log x ≥ 1 - 1/x`); so `P ≪ Q ⇒ P ≪ Q_ε`, integrability transfers, and
`𝓗_G(P) - 𝓗_{G_ε}(P) = ∫ log(G_ε/G) dP ≥ 0`; if `P` is not `≪ Q` the right-hand side is `+∞`.
Size M-L; may equally be proved in packet D3/B. -/
theorem b15c_gibbsEntropyGen_le (D : DynData d) (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {M : ℝ}
    (hM : 0 ≤ M) (P : Measure (Config d N)) [IsProbabilityMeasure P] :
    b15c_gibbsEntropyGen D.invβ (b15c_potentialReg D M) P ≤ gibbsEntropy D P := by
  sorry


/-- `∇g_M` is `C^∞` on the torus (the drift field of the regularised SDE, as consumed by D1):
`KernelD1Aux.isSmooth_grad` applied to `b15c_gReg_isSmooth`. -/
theorem b15c_grad_gReg_isSmooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : ℝ) :
    Torus.IsSmooth (Torus.grad (b15c_gReg d s M)) :=
  KernelD1Aux.isSmooth_grad (b15c_gReg_isSmooth hd hs0 hsd M)

/-- **Passage of the Fisher functional to the limit, for one test field** (TeX L12205-12216, the input of
`B:eq:selected-fisher-lsc-bound`): for a test field `ζ ∈ C_c^∞(Ω_N)` whose `ε = 0` integrand
`b15c_fisherIntegrand D.invβ (totalPotential D) ζ` is continuous on `(𝕋^d)^N` (`hcont`: a lemma of packet B,
from periodicity of the `fderiv` of lifts, `iteratedFDeriv_lift_periodic`; it is *not* proved here),
the spacetime integrals of the `ε`-integrands against the laws `P^r_{N,ε_n}` converge to those of the
`ε = 0` integrand against `P^r_N`.  Proof: for large `n` the integrands coincide
(`b15c_fisherIntegrand_eventuallyEq`), then `b15c_spacetime_tendsto` with the time-independent
`ψ(r,x) = integrand(x)` (so this inherits that sorry). -/
theorem b15c_fisher_spacetime_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (hS : IsStrongSolution P D T X₀ W X)
    {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hY : ∀ n, IsAdditiveSDESolution P ℱ W' (fun _ => b15c_liftedDriftReg D (M n)) (liftedNoise D)
      Y₀ (fun _ => ⊤) (Y n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → b15c_regProcess (Y n) t ω = X t ω)
    {ζ : Config d N → (Fin N → Euc d)} (hζ : IsFisherTestField ζ)
    (hcont : Continuous (b15c_fisherIntegrand D.invβ (totalPotential D) ζ))
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    Tendsto (fun n => ∫ r in Set.Icc (0 : ℝ) t,
        ∫ x, b15c_fisherIntegrand D.invβ (b15c_potentialReg D (M n)) ζ x
          ∂(selectedLaw P (b15c_regProcess (Y n)) r)) atTop
      (𝓝 (∫ r in Set.Icc (0 : ℝ) t,
        ∫ x, b15c_fisherIntegrand D.invβ (totalPotential D) ζ x ∂(selectedLaw P X r))) := by
  obtain ⟨M₀, hM₀⟩ := b15c_fisherIntegrand_eventuallyEq D hζ
  have h1 := b15c_spacetime_tendsto hS hY hev ht0 htT
    (ψ := fun _ x => b15c_fisherIntegrand D.invβ (totalPotential D) ζ x)
    (hcont.comp continuous_snd)
  refine h1.congr' ?_
  filter_upwards [hM.eventually (eventually_ge_atTop M₀)] with n hn
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hM₀ (M n) hn x]

end HRS
