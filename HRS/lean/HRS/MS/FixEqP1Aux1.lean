import HRS.MS.FixEqAux1

/-!
# S5.7 `fixed_equation` (worker S57P), part 1: the weighted space `E_{k,P}`, the dual bound, the initial term (packet P2 core)

Infrastructure for the proof of `HRS.Whole.fixed_equation` (repaired statement R1-R3, ED3).  Prefix `s57p_`,
namespace `HRS.MS.FixEq`.

## What this file proves

* `s57p_dual_bound` (the density step behind R1): if `η` is a bounded linear functional on the `C^r` functions of finite
  `E_{r,P}`-norm (`IsBoundedLinearOnE`) then for every `f ∈ C_b^r` (and `2P > d`)
  `|η f| ≤ dualNormE r P η * ‖f‖_{E_{r,P}}`, although `dualNormE` is a supremum over `C_c^∞` only.  Proof: cut off `χ(x/n) f`
  and mollify (`s57p_smooth_approx`), dominated convergence for the `E`-norms.
* `s57p_E_le_cb`: `‖f‖_{E_{r,(d+3)/2}} ≤ c_{d,r} sup_{j≤r}‖D^j f‖_∞` (the weight `⟨x⟩^{-(d+3)}` is integrable).
* `s57p_initial_bound`: `|η f| ≤ dualNormE r P η * c_{d,r} B` for `f ∈ C^r` with `‖D^j f‖_∞ ≤ B` (the initial term of the
  cost estimate: `f = U^{0,t}φ_α` etc.).

## Status of the whole proof (worker S57P, 2026-10-23): PARTIAL

Done (complete, no gaps): P2 core (this file), P4 core (`FixEqP1Aux2`: a.s. `l^2`, fourth moments; `FixEqP1Aux3`: `s57p_noise_exists`,
continuous `OscDual`-valued Gaussian process from one isonormal process, so two families can share the noise).
Open, with estimates and blockers:
* Uniqueness of classical adjoint solutions for `fixedEqCoeff` (free time-dependent drift `-Qx + c_t`, nonlocal term with time-dependent
  `rho_t`, general `M`, `nu >= 0`): the engine `Fcau.propagatorW_unique_star` is stated for `WholeDyn` drifts `M grad g * rho - grad V`
  (about 17.7k lines in `HRS/MS/Uniq*`); `UniqQ` covers only `nu > 0`, `M = -1`, time-independent Schwartz `rho`.  Needs a decision:
  a uniqueness hypothesis in `FixedEqFcauHyp` (cheap) or a generalised engine (several k lines).
* Linear layer (linearity/continuity of `phi -> U phi` on `Sigma^m`, semigroup, terminal-time derivative `d_t U^{r,t}phi = U^{r,t} L_t phi`,
  continuity in `t`): ~1.5k lines, uses uniqueness.
* P1 Duhamel difference `(U_N - U)psi = int U_N (L_N - L) U psi` with the nonlocal term for `s` up to `d` (cancellation convention;
  `far_derivatives` only covers `s <= d-2`, plain integral) and derivatives up to order `k+4+ceil(d/2)`: ~2.5k lines.
* P3 difference of noise fields: sup_t bound of the Gaussian difference (chaining with fourth moments or `orbit_maximal` for a
  continuum white-noise martingale), features/Hilbert-Schmidt differences: ~2k lines; P5 assembly ~0.5k.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace HRS.MS.FixEq

open HRS HRS.Whole

variable {d : ℕ}

/-! ### The weight -/

/-- the weight `⟨x⟩^{-2P}` -/
def s57pW (d : ℕ) (P : ℝ) (x : Euc d) : ℝ := jbracket x ^ (-2 * P)

theorem s57p_jbracket_pos (x : Euc d) : 0 < jbracket x := by
  unfold jbracket
  positivity

theorem s57p_jbracket_ge (x : Euc d) : (1 + ‖x‖) / Real.sqrt 2 ≤ jbracket x := by
  unfold jbracket
  rw [div_le_iff₀ (by positivity)]
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (1 - ‖x‖), norm_nonneg x]

theorem s57pW_nonneg (P : ℝ) (x : Euc d) : 0 ≤ s57pW d P x :=
  (Real.rpow_pos_of_pos (s57p_jbracket_pos x) _).le

theorem s57pW_le {P : ℝ} (hP : 0 ≤ P) (x : Euc d) : s57pW d P x ≤ 2 ^ P * (1 + ‖x‖) ^ (-(2 * P)) := by
  unfold s57pW
  have h1 : (1 + ‖x‖) / Real.sqrt 2 ≤ jbracket x := s57p_jbracket_ge x
  have h2 : 0 < (1 + ‖x‖) / Real.sqrt 2 := by positivity
  have h3 : jbracket x ^ (-2 * P) ≤ ((1 + ‖x‖) / Real.sqrt 2) ^ (-2 * P) :=
    Real.rpow_le_rpow_of_nonpos h2 h1 (by linarith)
  refine h3.trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) (by positivity)]
  have : Real.sqrt 2 ^ (-2 * P) = (2 : ℝ) ^ (-P) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
    congr 1; ring
  rw [this, show -2 * P = -(2 * P) by ring, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) P, div_inv_eq_mul, mul_comm]

theorem s57pW_integrable {P : ℝ} (hP : (d : ℝ) < 2 * P) : Integrable (s57pW d P) (volume : Measure (Euc d)) := by
  have hP0 : 0 ≤ P := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-(2 * P))) (volume : Measure (Euc d)) :=
    integrable_one_add_norm (by simpa using hP)
  refine Integrable.mono' (hint.const_mul (2 ^ P)) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have : Continuous (s57pW d P) := by
      unfold s57pW
      refine Continuous.rpow_const ?_ (fun x => Or.inl (s57p_jbracket_pos x).ne')
      unfold jbracket
      fun_prop
    exact this.aestronglyMeasurable
  · rw [Real.norm_of_nonneg (s57pW_nonneg P x)]
    exact s57pW_le hP0 x

/-! ### The sum under the square root of `weightedSobolevE` -/

/-- `∑_{j≤r} ∑_{i} ∫ ⟨x⟩^{-2P} |∂^i f|²` (the square of `weightedSobolevE`) -/
def s57pS (d : ℕ) (r : ℕ) (P : ℝ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d,
    ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)

theorem s57p_E_eq (r : ℕ) (P : ℝ) (f : Euc d → ℝ) :
    weightedSobolevE r P f = (s57pS d r P f) ^ (1 / 2 : ℝ) := rfl

/-- the number of index tuples of order `≤ r` -/
def s57pN (d r : ℕ) : ℕ := ∑ j ∈ Finset.range (r + 1), d ^ j

theorem s57p_abs_partialDeriv_le {j : ℕ} (i : Fin j → Fin d) (f : Euc d → ℝ) (x : Euc d) :
    |partialDeriv i f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
  unfold partialDeriv
  have := (iteratedFDeriv ℝ j f x).le_opNorm (fun l => EuclideanSpace.single (i l) (1 : ℝ))
  simpa [Real.norm_eq_abs, EuclideanSpace.norm_single] using this

theorem s57p_S_le {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) {f : Euc d → ℝ} {B : ℝ}
    (hB : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i f x| ≤ B) :
    s57pS d r P f ≤ ENNReal.ofReal ((s57pN d r : ℝ) * (B ^ 2 * ∫ x, s57pW d P x)) := by
  have hW := s57pW_integrable (d := d) hP
  have key : ∀ j ≤ r, ∀ i : Fin j → Fin d,
      ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) ≤
        ENNReal.ofReal (B ^ 2 * ∫ x, s57pW d P x) := by
    intro j hj i
    have h1 : ∀ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) ≤
        ENNReal.ofReal (B ^ 2 * s57pW d P x) := by
      intro x
      apply ENNReal.ofReal_le_ofReal
      have h2 : (partialDeriv i f x) ^ 2 ≤ B ^ 2 := by
        have := hB j hj i x
        exact sq_le_sq' (by linarith [abs_nonneg (partialDeriv i f x), neg_abs_le (partialDeriv i f x)])
          (le_trans (le_abs_self _) this)
      have h3 : 0 ≤ jbracket x ^ (-2 * P) := (Real.rpow_pos_of_pos (s57p_jbracket_pos x) _).le
      calc jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2 ≤ jbracket x ^ (-2 * P) * B ^ 2 :=
            mul_le_mul_of_nonneg_left h2 h3
        _ = B ^ 2 * s57pW d P x := by unfold s57pW; ring
    calc ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)
        ≤ ∫⁻ x, ENNReal.ofReal (B ^ 2 * s57pW d P x) := lintegral_mono h1
      _ = ENNReal.ofReal (∫ x, B ^ 2 * s57pW d P x) := by
          rw [ofReal_integral_eq_lintegral_ofReal (hW.const_mul _)
            (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg B) (s57pW_nonneg P x))]
      _ = ENNReal.ofReal (B ^ 2 * ∫ x, s57pW d P x) := by rw [integral_const_mul]
  unfold s57pS
  calc ∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d,
        ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)
      ≤ ∑ j ∈ Finset.range (r + 1), ∑ _i : Fin j → Fin d, ENNReal.ofReal (B ^ 2 * ∫ x, s57pW d P x) := by
        refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i _ => ?_
        exact key j (by simpa [Nat.lt_succ_iff] using hj) i
    _ = ENNReal.ofReal ((s57pN d r : ℝ) * (B ^ 2 * ∫ x, s57pW d P x)) := by
        have hnn : 0 ≤ B ^ 2 * ∫ x, s57pW d P x :=
          mul_nonneg (sq_nonneg B) (integral_nonneg fun x => s57pW_nonneg P x)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        unfold s57pN
        push_cast
        rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
        simp


theorem s57p_partialDeriv_succ {j : ℕ} {h : Euc d → ℝ} (hh : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) h)
    (i : Fin (j + 1) → Fin d) (x : Euc d) :
    partialDeriv i h x =
      fderiv ℝ (partialDeriv (fun l : Fin j => i l.succ) h) x (EuclideanSpace.single (i 0) (1 : ℝ)) := by
  have hdiff : Differentiable ℝ (iteratedFDeriv ℝ j h) :=
    hh.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self j)
  have e1 : partialDeriv (fun l : Fin j => i l.succ) h =
      fun y => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l : Fin j => EuclideanSpace.single (i l.succ) (1 : ℝ))) (iteratedFDeriv ℝ j h y) := by
    funext y; rfl
  rw [e1]
  have e2 := ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l : Fin j => EuclideanSpace.single (i l.succ) (1 : ℝ))).hasFDerivAt.comp x
        (hdiff x).hasFDerivAt).fderiv
  have e3 : fderiv ℝ (fun y => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l : Fin j => EuclideanSpace.single (i l.succ) (1 : ℝ))) (iteratedFDeriv ℝ j h y)) x =
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l : Fin j => EuclideanSpace.single (i l.succ) (1 : ℝ))).comp (fderiv ℝ (iteratedFDeriv ℝ j h) x) := e2
  rw [e3]
  unfold partialDeriv
  rw [iteratedFDeriv_succ_apply_left]
  rfl

open ContinuousLinearMap in
theorem s57p_partialDeriv_contDiff {r : ℕ} {h : Euc d → ℝ} (hh : ContDiff ℝ r h) {j : ℕ} (k : ℕ) (hjk : k + j ≤ r)
    (i : Fin j → Fin d) : ContDiff ℝ k (partialDeriv i h) := by
  have e1 : partialDeriv i h = fun y => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l : Fin j => EuclideanSpace.single (i l) (1 : ℝ))) (iteratedFDeriv ℝ j h y) := rfl
  rw [e1]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ _).contDiff.comp
    (hh.iteratedFDeriv_right (by exact_mod_cast hjk))

theorem s57p_partialDeriv_hasCompactSupport {h : Euc d → ℝ} (hc : HasCompactSupport h) {j : ℕ} (i : Fin j → Fin d) :
    HasCompactSupport (partialDeriv i h) := by
  have e1 : partialDeriv i h = (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
        (fun l : Fin j => EuclideanSpace.single (i l) (1 : ℝ))) ∘ (iteratedFDeriv ℝ j h) := rfl
  rw [e1]
  exact (hc.iteratedFDeriv (𝕜 := ℝ) j).comp_left (map_zero _)

open ContinuousLinearMap in
theorem s57p_conv_partialDeriv (ψ : ContDiffBump (0 : Euc d)) {r : ℕ} {h : Euc d → ℝ}
    (hh : ContDiff ℝ r h) (hc : HasCompactSupport h) :
    ∀ j ≤ r, ∀ i : Fin j → Fin d,
      partialDeriv i (ψ.normed volume ⋆[lsmul ℝ ℝ, volume] h) =
        ψ.normed volume ⋆[lsmul ℝ ℝ, volume] (partialDeriv i h) := by
  have hsm : ContDiff ℝ ∞ (ψ.normed volume ⋆[lsmul ℝ ℝ, volume] h) :=
    ψ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ψ.contDiff_normed
      (hh.continuous.locallyIntegrable)
  intro j
  induction j with
  | zero =>
    intro _ i
    have e : ∀ g : Euc d → ℝ, partialDeriv i g = g := by
      intro g; funext x; unfold partialDeriv; simp [iteratedFDeriv_zero_apply]
    rw [e, e]
  | succ j ih =>
    intro hj i
    funext x
    have hjr : j ≤ r := by omega
    have hg1 : ContDiff ℝ 1 (partialDeriv (fun l : Fin j => i l.succ) h) :=
      s57p_partialDeriv_contDiff hh 1 (by omega) _
    have hgc := s57p_partialDeriv_hasCompactSupport hc (fun l : Fin j => i l.succ)
    rw [s57p_partialDeriv_succ (hsm.of_le (by exact_mod_cast le_top)) i x, ih hjr]
    have hd := hgc.hasFDerivAt_convolution_right (lsmul ℝ ℝ) (μ := volume)
      (ψ.integrable_normed (μ := volume)).locallyIntegrable hg1 x
    rw [hd.fderiv, convolution_precompR_apply (lsmul ℝ ℝ) (ψ.integrable_normed (μ := volume)).locallyIntegrable
      (hgc.fderiv ℝ) (hg1.continuous_fderiv one_ne_zero)]
    congr 1
    funext a
    rw [s57p_partialDeriv_succ (hh.of_le (by exact_mod_cast hj)) i a]

open ContinuousLinearMap in
theorem s57p_smooth_approx {r : ℕ} {h : Euc d → ℝ} (hh : ContDiff ℝ r h) (hc : HasCompactSupport h)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : Euc d → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i g x - partialDeriv i h x| ≤ δ := by
  let Idx := Σ j : Fin (r + 1), (Fin (j : ℕ) → Fin d)
  let F : Euc d → (Idx → ℝ) := fun x p => partialDeriv p.2 h x
  have hFc : Continuous F := by
    refine continuous_pi fun p => ?_
    exact (s57p_partialDeriv_contDiff hh 0 (by have := p.1.2; omega) p.2).continuous
  have hFs : HasCompactSupport F := by
    refine HasCompactSupport.intro hc fun x hx => ?_
    funext p
    have : partialDeriv p.2 h x = 0 := by
      by_contra hne
      exact hx ((support_iteratedFDeriv_subset (𝕜 := ℝ) (n := (p.1 : ℕ)) (f := h))
        (show x ∈ Function.support (iteratedFDeriv ℝ (p.1 : ℕ) h) from by
          intro hz; apply hne; unfold partialDeriv; rw [hz]; simp))
    exact this
  have hFu : UniformContinuous F := hFs.uniformContinuous_of_continuous hFc
  obtain ⟨ρ, hρ, hρF⟩ := Metric.uniformContinuous_iff.mp hFu δ hδ
  let ψ : ContDiffBump (0 : Euc d) := ⟨ρ / 2, ρ, half_pos hρ, half_lt_self hρ⟩
  have hmg : ∀ j ≤ r, ∀ i : Fin j → Fin d, AEStronglyMeasurable (partialDeriv i h) volume := fun j hj i =>
    (s57p_partialDeriv_contDiff hh 0 (by omega) i).continuous.aestronglyMeasurable
  refine ⟨ψ.normed volume ⋆[lsmul ℝ ℝ, volume] h,
    ψ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) ψ.contDiff_normed
      (hh.continuous.locallyIntegrable),
    ψ.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hc, ?_⟩
  intro j hj i x
  rw [s57p_conv_partialDeriv ψ hh hc j hj i]
  have := ψ.dist_normed_convolution_le (μ := volume) (g := partialDeriv i h) (x₀ := x) (ε := δ)
    (hmg j hj i) (fun y hy => by
      have h1 : dist (F y) (F x) < δ := hρF (by simpa [ψ] using hy)
      have h2 := dist_le_pi_dist (F y) (F x) ⟨⟨j, by omega⟩, i⟩
      exact (h2.trans h1.le))
  rwa [Real.dist_eq] at this


theorem s57p_cutoff (r : ℕ) : ∃ χ : Euc d → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
    (∀ x, ‖x‖ ≤ 1 → χ x = 1) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i χ y‖ ≤ C := by
  let χ : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, fun x hx => ?_, ?_⟩
  · exact χ.one_of_mem_closedBall (by simpa [χ] using hx)
  · exact χ.hasCompactSupport.exists_bound_iteratedFDeriv χ.contDiff r

theorem s57p_cutoff_prod {r : ℕ} {f : Euc d → ℝ} {B : ℝ} (hf : ContDiff ℝ r f)
    (hB : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    ∃ B₁ : ℝ, ∀ R : ℝ, 1 ≤ R → ∃ h : Euc d → ℝ, ContDiff ℝ r h ∧ HasCompactSupport h ∧
      (∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j h x‖ ≤ B₁) ∧ (∀ x, ‖x‖ < R → h =ᶠ[𝓝 x] f) := by
  obtain ⟨χ, hχs, hχc, hχ1, C, hC0, hC⟩ := s57p_cutoff (d := d) r
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Nat.zero_le _) 0)
  refine ⟨2 ^ r * (C * B), fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  set χR : Euc d → ℝ := fun x => χ (R⁻¹ • x) with hχR
  have hχRs : ContDiff ℝ ∞ χR := hχs.comp (contDiff_const_smul _)
  have hχRc : HasCompactSupport χR := hχc.comp_smul (inv_ne_zero hR0.ne')
  refine ⟨fun x => χR x * f x, (hχRs.of_le (by exact_mod_cast le_top)).mul hf, hχRc.mul_right, ?_, ?_⟩
  · intro j hj x
    have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := χR) (g := f) (N := (r : WithTop ℕ∞))
      (hχRs.of_le (by exact_mod_cast le_top)) hf x (n := j) (by exact_mod_cast hj)
    refine hmul.trans ?_
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χR x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (C * B) := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := by simpa [Nat.lt_succ_iff] using hi
          have h1 : ‖iteratedFDeriv ℝ i χR x‖ ≤ C := by
            have := iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := i) (f := χ) R⁻¹
              (hχs.of_le (by exact_mod_cast le_top))
            rw [hχR, this]
            simp only [norm_smul, norm_pow, norm_inv, Real.norm_eq_abs, abs_of_pos hR0]
            have hRi : (R⁻¹) ^ i ≤ 1 := pow_le_one₀ (inv_nonneg.2 hR0.le) (inv_le_one_of_one_le₀ hR)
            calc R⁻¹ ^ i * ‖iteratedFDeriv ℝ i χ (R⁻¹ • x)‖ ≤ 1 * C :=
                  mul_le_mul hRi (hC i (by omega) _) (norm_nonneg _) zero_le_one
              _ = C := one_mul C
          have h2 : ‖iteratedFDeriv ℝ (j - i) f x‖ ≤ B := hB _ (by omega) x
          have := mul_le_mul h1 h2 (norm_nonneg _) hC0
          calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i χR x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖
              = (j.choose i : ℝ) * (‖iteratedFDeriv ℝ i χR x‖ * ‖iteratedFDeriv ℝ (j - i) f x‖) := by ring
            _ ≤ (j.choose i : ℝ) * (C * B) := mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = (2 ^ j : ℝ) * (C * B) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ r * (C * B) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hC0 hB0)
          exact pow_le_pow_right₀ (by norm_num) hj
  · intro x hx
    have hball : ∀ᶠ y in 𝓝 x, ‖y‖ < R := by
      have : IsOpen {y : Euc d | ‖y‖ < R} := isOpen_lt continuous_norm continuous_const
      exact this.mem_nhds hx
    filter_upwards [hball] with y hy
    have : χR y = 1 := by
      apply hχ1
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR0]
      rw [inv_mul_le_iff₀ hR0]; linarith
    simp [this]


theorem s57p_partialDeriv_sub {r : ℕ} {f g : Euc d → ℝ} (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g)
    {j : ℕ} (hj : j ≤ r) (i : Fin j → Fin d) (x : Euc d) :
    partialDeriv i (fun y => f y - g y) x = partialDeriv i f x - partialDeriv i g x := by
  unfold partialDeriv
  have e : iteratedFDeriv ℝ j (fun y => f y - g y) x = iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j g x :=
    iteratedFDeriv_sub_apply ((hf.of_le (by exact_mod_cast hj)).contDiffAt)
      ((hg.of_le (by exact_mod_cast hj)).contDiffAt)
  rw [e]; rfl

theorem s57p_term_tendsto {P : ℝ} (hP : (d : ℝ) < 2 * P) (F : ℕ → Euc d → ℝ) (G : Euc d → ℝ) (B : ℝ)
    (hmeas : ∀ n, Measurable (F n)) (hb : ∀ n x, |F n x| ≤ B)
    (hlim : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (𝓝 (G x))) :
    Filter.Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (F n x) ^ 2)) Filter.atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (G x) ^ 2))) := by
  have hW := s57pW_integrable (d := d) hP
  have hWc : Continuous (s57pW d P) := by
    unfold s57pW
    refine Continuous.rpow_const ?_ (fun x => Or.inl (s57p_jbracket_pos x).ne')
    unfold jbracket; fun_prop
  refine tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal (B ^ 2 * s57pW d P x)) ?_ ?_ ?_ ?_
  · intro n
    exact ENNReal.measurable_ofReal.comp ((hWc.measurable).mul ((hmeas n).pow_const 2))
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    apply ENNReal.ofReal_le_ofReal
    have h3 : 0 ≤ jbracket x ^ (-2 * P) := (Real.rpow_pos_of_pos (s57p_jbracket_pos x) _).le
    have h2 : (F n x) ^ 2 ≤ B ^ 2 := sq_le_sq' (abs_le.1 (hb n x)).1 (abs_le.1 (hb n x)).2
    calc jbracket x ^ (-2 * P) * (F n x) ^ 2 ≤ jbracket x ^ (-2 * P) * B ^ 2 :=
          mul_le_mul_of_nonneg_left h2 h3
      _ = B ^ 2 * s57pW d P x := by unfold s57pW; ring
  · rw [← ofReal_integral_eq_lintegral_ofReal (hW.const_mul _)
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg B) (s57pW_nonneg P x))]
    exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall fun x => ?_
    apply ENNReal.tendsto_ofReal
    exact (((hlim x).pow 2).const_mul _)


theorem s57p_S_tendsto {P : ℝ} (hP : (d : ℝ) < 2 * P) {r : ℕ} (f : Euc d → ℝ) (g : ℕ → Euc d → ℝ) (B : ℝ)
    (hf : ContDiff ℝ r f) (hg : ∀ n, ContDiff ℝ r (g n))
    (hfb : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i f x| ≤ B)
    (hgb : ∀ n, ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i (g n) x| ≤ B)
    (hlim : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
      Filter.Tendsto (fun n => partialDeriv i (g n) x) Filter.atTop (𝓝 (partialDeriv i f x))) :
    Filter.Tendsto (fun n => s57pS d r P (g n)) Filter.atTop (𝓝 (s57pS d r P f)) ∧
    Filter.Tendsto (fun n => s57pS d r P (fun x => f x - g n x)) Filter.atTop (𝓝 0) := by
  have hcont : ∀ {u : Euc d → ℝ}, ContDiff ℝ r u → ∀ j ≤ r, ∀ i : Fin j → Fin d,
      Measurable (partialDeriv i u) := fun {u} hu j hj i =>
    (s57p_partialDeriv_contDiff hu 0 (by omega) i).continuous.measurable
  constructor
  · unfold s57pS
    refine tendsto_finsetSum _ fun j hj => tendsto_finsetSum _ fun i _ => ?_
    have hj' : j ≤ r := by simpa [Nat.lt_succ_iff] using hj
    exact s57p_term_tendsto hP (fun n => partialDeriv i (g n)) (partialDeriv i f) B
      (fun n => hcont (hg n) j hj' i) (fun n x => hgb n j hj' i x) (hlim j hj' i)
  · have : (0 : ℝ≥0∞) = ∑ j ∈ Finset.range (r + 1), ∑ _i : Fin j → Fin d, (0 : ℝ≥0∞) := by simp
    rw [this]
    unfold s57pS
    refine tendsto_finsetSum _ fun j hj => tendsto_finsetSum _ fun i _ => ?_
    have hj' : j ≤ r := by simpa [Nat.lt_succ_iff] using hj
    have hzero : ∫⁻ x : Euc d, ENNReal.ofReal (jbracket x ^ (-2 * P) * (0 : ℝ) ^ 2) = 0 := by simp
    rw [← hzero]
    have := s57p_term_tendsto hP (fun n x => partialDeriv i f x - partialDeriv i (g n) x) (fun _ => 0)
      (2 * B) (fun n => (hcont hf j hj' i).sub (hcont (hg n) j hj' i))
      (fun n x => by
        have h1 := hfb j hj' i x
        have h2 := hgb n j hj' i x
        calc |partialDeriv i f x - partialDeriv i (g n) x|
            ≤ |partialDeriv i f x| + |partialDeriv i (g n) x| := abs_sub _ _
          _ ≤ 2 * B := by linarith)
      (fun x => by
        have := (tendsto_const_nhds (x := partialDeriv i f x)).sub (hlim j hj' i x)
        simpa using this)
    refine this.congr fun n => ?_
    refine lintegral_congr fun x => ?_
    rw [s57p_partialDeriv_sub hf (hg n) hj' i x]


theorem s57p_E_lt_top_of_bound {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) {g : Euc d → ℝ} {B : ℝ}
    (hB : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i g x| ≤ B) :
    weightedSobolevE r P g < ⊤ := by
  rw [s57p_E_eq]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (lt_of_le_of_lt (s57p_S_le hP hB) ENNReal.ofReal_lt_top).ne

theorem s57p_E_zero {r : ℕ} {P : ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ r g)
    (h0 : weightedSobolevE r P g = 0) : g = 0 := by
  rw [s57p_E_eq] at h0
  have hS : s57pS d r P g = 0 := by
    rcases (ENNReal.rpow_eq_zero_iff).1 h0 with ⟨h, _⟩ | ⟨_, h⟩
    · exact h
    · norm_num at h
  unfold s57pS at hS
  have h1 := (Finset.sum_eq_zero_iff.1 hS) 0 (Finset.mem_range.2 (Nat.succ_pos r))
  have h2 := (Finset.sum_eq_zero_iff.1 h1) (fun l => l.elim0) (Finset.mem_univ _)
  have hmeas : Measurable fun x : Euc d => ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv (fun l : Fin 0 => l.elim0) g x) ^ 2) := by
    have hc : Continuous fun x : Euc d => jbracket x ^ (-2 * P) * (partialDeriv (fun l : Fin 0 => l.elim0) g x) ^ 2 := by
      refine Continuous.mul ?_ ((s57p_partialDeriv_contDiff hg 0 (by omega) _).continuous.pow 2)
      refine Continuous.rpow_const ?_ (fun x => Or.inl (s57p_jbracket_pos x).ne')
      unfold jbracket; fun_prop
    exact ENNReal.measurable_ofReal.comp hc.measurable
  have h3 := (lintegral_eq_zero_iff hmeas).1 h2
  have hc : Continuous g := hg.continuous
  have h4 : g =ᵐ[volume] 0 := by
    filter_upwards [h3] with x hx
    have hx' : ENNReal.ofReal (jbracket x ^ (-2 * P) * (g x) ^ 2) = 0 := by
      simpa [partialDeriv, iteratedFDeriv_zero_apply] using hx
    have := ENNReal.ofReal_eq_zero.1 hx'
    have hpos : 0 < jbracket x ^ (-2 * P) := Real.rpow_pos_of_pos (s57p_jbracket_pos x) _
    have : (g x) ^ 2 ≤ 0 := by
      by_contra hne
      push Not at hne
      exact absurd this (not_le.2 (mul_pos hpos hne))
    simpa using pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
  exact (Continuous.ae_eq_iff_eq volume hc continuous_const).1 h4


theorem s57p_E_zero_fun {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) : weightedSobolevE r P (0 : Euc d → ℝ) < ⊤ :=
  s57p_E_lt_top_of_bound (B := 0) hP (fun j _ i x => by simp [partialDeriv])

theorem s57p_eta_zero {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) {η : (Euc d → ℝ) → ℝ}
    (hη : IsBoundedLinearOnE r P η) : η 0 = 0 := by
  have h := (hη.1 0 0 contDiff_const (s57p_E_zero_fun hP) contDiff_const (s57p_E_zero_fun hP) 0).2
  simpa using h

theorem s57p_le_dualNorm {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) {η : (Euc d → ℝ) → ℝ} (hη : IsBoundedLinearOnE r P η)
    {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (hgE : weightedSobolevE r P g < ⊤) :
    ENNReal.ofReal |η g| ≤ dualNormE r P η * weightedSobolevE r P g := by
  by_cases h0 : weightedSobolevE r P g = 0
  · have := s57p_E_zero (hg.of_le (by exact_mod_cast le_top)) h0
    subst this
    simp [s57p_eta_zero hP hη]
  · have hpos : 0 < weightedSobolevE r P g := pos_iff_ne_zero.2 h0
    have hle : ENNReal.ofReal |η g| / weightedSobolevE r P g ≤ dualNormE r P η := by
      unfold dualNormE
      exact le_iSup_of_le g (le_iSup_of_le ⟨hg, hgc, hpos, hgE⟩ le_rfl)
    calc ENNReal.ofReal |η g| = ENNReal.ofReal |η g| / weightedSobolevE r P g * weightedSobolevE r P g := by
          rw [ENNReal.div_mul_cancel h0 hgE.ne]
      _ ≤ _ := mul_le_mul_left hle _


theorem s57p_dual_bound {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) {η : (Euc d → ℝ) → ℝ}
    (hη : IsBoundedLinearOnE r P η) {f : Euc d → ℝ} (hf : ContDiff ℝ r f) {B : ℝ}
    (hB : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    ENNReal.ofReal |η f| ≤ dualNormE r P η * weightedSobolevE r P f := by
  obtain ⟨hlin, Bη, hBη⟩ := hη
  have hη' : IsBoundedLinearOnE r P η := ⟨hlin, Bη, hBη⟩
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Nat.zero_le _) 0)
  have hcoord : ∀ {u : Euc d → ℝ} {B' : ℝ}, (∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ B') →
      ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i u x| ≤ B' := fun {u B'} hu j hj i x =>
    (s57p_abs_partialDeriv_le i u x).trans (hu j hj x)
  have hfE : weightedSobolevE r P f < ⊤ := s57p_E_lt_top_of_bound hP (hcoord hB)
  -- the approximating sequence
  obtain ⟨B₁, hcut⟩ := s57p_cutoff_prod hf hB
  have hcut' : ∀ n : ℕ, ∃ h : Euc d → ℝ, ContDiff ℝ r h ∧ HasCompactSupport h ∧
      (∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j h x‖ ≤ B₁) ∧ (∀ x, ‖x‖ < (n : ℝ) + 1 → h =ᶠ[𝓝 x] f) :=
    fun n => hcut ((n : ℝ) + 1) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  choose h hh1 hh2 hh3 hh4 using hcut'
  have happ : ∀ n : ℕ, ∃ g : Euc d → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i g x - partialDeriv i (h n) x| ≤ 1 / ((n : ℝ) + 1) :=
    fun n => s57p_smooth_approx (hh1 n) (hh2 n) (by positivity)
  choose g hg1 hg2 hg3 using happ
  have hgr : ∀ n, ContDiff ℝ r (g n) := fun n => (hg1 n).of_le (by exact_mod_cast le_top)
  have hgb : ∀ n, ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i (g n) x| ≤ max B (B₁ + 1) := by
    intro n j hj i x
    have h1 := hg3 n j hj i x
    have h2 : |partialDeriv i (h n) x| ≤ B₁ := (s57p_abs_partialDeriv_le i (h n) x).trans (hh3 n j hj x)
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h4 : |partialDeriv i (g n) x| ≤ |partialDeriv i (g n) x - partialDeriv i (h n) x| + |partialDeriv i (h n) x| := by
      have := abs_add_le (partialDeriv i (g n) x - partialDeriv i (h n) x) (partialDeriv i (h n) x)
      simpa using this
    exact (by linarith : |partialDeriv i (g n) x| ≤ B₁ + 1).trans (le_max_right _ _)
  have hfb : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x, |partialDeriv i f x| ≤ max B (B₁ + 1) :=
    fun j hj i x => (hcoord hB j hj i x).trans (le_max_left _ _)
  have hlim : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∀ x,
      Filter.Tendsto (fun n => partialDeriv i (g n) x) Filter.atTop (𝓝 (partialDeriv i f x)) := by
    intro j hj i x
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖x‖ < (n : ℝ) + 1 := by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    filter_upwards [hev] with n hn
    have heq : partialDeriv i (h n) x = partialDeriv i f x := by
      unfold partialDeriv
      rw [(Filter.EventuallyEq.iteratedFDeriv ℝ (hh4 n x hn) j).self_of_nhds]
    have := hg3 n j hj i x
    rw [heq] at this
    simpa [Real.norm_eq_abs] using this
  obtain ⟨hS1, hS2⟩ := s57p_S_tendsto hP f g (max B (B₁ + 1)) hf hgr hfb hgb hlim
  -- from `S` to `E`
  have hcr : Continuous fun a : ℝ≥0∞ => a ^ (1 / 2 : ℝ) := ENNReal.continuous_rpow_const
  have hE1 : Filter.Tendsto (fun n => weightedSobolevE r P (g n)) Filter.atTop (𝓝 (weightedSobolevE r P f)) :=
    (hcr.tendsto _).comp hS1
  have hE2 : Filter.Tendsto (fun n => weightedSobolevE r P (fun x => f x - g n x)) Filter.atTop (𝓝 0) := by
    have := (hcr.tendsto 0).comp hS2
    rw [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    exact this
  -- the pointwise (in `n`) inequality
  set D := dualNormE r P η with hD
  have hBη' : ∀ u : Euc d → ℝ, ContDiff ℝ r u → weightedSobolevE r P u < ⊤ →
      ENNReal.ofReal |η u| ≤ ENNReal.ofReal (max Bη 0) * weightedSobolevE r P u := by
    intro u hu huE
    calc ENNReal.ofReal |η u| ≤ ENNReal.ofReal (max Bη 0 * (weightedSobolevE r P u).toReal) :=
          ENNReal.ofReal_le_ofReal ((hBη u hu huE).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg))
      _ = ENNReal.ofReal (max Bη 0) * weightedSobolevE r P u := by
          rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_toReal huE.ne]
  have hkey : ∀ n, ENNReal.ofReal |η f| ≤
      D * weightedSobolevE r P (g n) + ENNReal.ofReal (max Bη 0) * weightedSobolevE r P (fun x => f x - g n x) := by
    intro n
    have hgE : weightedSobolevE r P (g n) < ⊤ := s57p_E_lt_top_of_bound hP (fun j hj i x => hgb n j hj i x)
    have hdE : weightedSobolevE r P (fun x => f x - g n x) < ⊤ := by
      refine s57p_E_lt_top_of_bound (B := 2 * max B (B₁ + 1)) hP (fun j hj i x => ?_)
      rw [s57p_partialDeriv_sub hf (hgr n) hj i x]
      have h1 := hfb j hj i x
      have h2 := hgb n j hj i x
      calc |partialDeriv i f x - partialDeriv i (g n) x| ≤ |partialDeriv i f x| + |partialDeriv i (g n) x| :=
            abs_sub _ _
        _ ≤ _ := by linarith
    have hdc : ContDiff ℝ r (fun x => f x - g n x) := hf.sub (hgr n)
    have hsplit : η f = η (g n) + η (fun x => f x - g n x) := by
      have := (hlin (g n) (fun x => f x - g n x) (hgr n) hgE hdc hdE 1).1
      have e : (g n + fun x => f x - g n x) = f := by funext x; simp
      rw [e] at this
      exact this
    have h1 := s57p_le_dualNorm hP hη' (hg1 n) (hg2 n) hgE
    have h2 := hBη' _ hdc hdE
    calc ENNReal.ofReal |η f| = ENNReal.ofReal |η (g n) + η (fun x => f x - g n x)| := by rw [← hsplit]
      _ ≤ ENNReal.ofReal (|η (g n)| + |η (fun x => f x - g n x)|) :=
          ENNReal.ofReal_le_ofReal (abs_add_le _ _)
      _ = ENNReal.ofReal |η (g n)| + ENNReal.ofReal |η (fun x => f x - g n x)| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add h1 h2
  -- the limit
  by_cases hDtop : D = ⊤
  · by_cases hE0 : weightedSobolevE r P f = 0
    · have := s57p_E_zero hf hE0
      subst this
      simp [s57p_eta_zero hP hη']
    · rw [hDtop, ENNReal.top_mul hE0]; exact le_top
  · have hlimit : Filter.Tendsto (fun n => D * weightedSobolevE r P (g n) +
        ENNReal.ofReal (max Bη 0) * weightedSobolevE r P (fun x => f x - g n x)) Filter.atTop
        (𝓝 (D * weightedSobolevE r P f + ENNReal.ofReal (max Bη 0) * 0)) :=
      (ENNReal.Tendsto.const_mul hE1 (Or.inr hDtop)).add
        (ENNReal.Tendsto.const_mul hE2 (Or.inr ENNReal.ofReal_ne_top))
    rw [mul_zero, add_zero] at hlimit
    exact ge_of_tendsto' hlimit hkey


/-- the constant `c_{d,r,P} = (N_{d,r} ∫ ⟨x⟩^{-2P} dx)^{1/2}` -/
def s57pC (d r : ℕ) (P : ℝ) : ℝ := Real.sqrt ((s57pN d r : ℝ) * ∫ x : Euc d, s57pW d P x)

theorem s57pC_nonneg (d r : ℕ) (P : ℝ) : 0 ≤ s57pC d r P := Real.sqrt_nonneg _

theorem s57p_E_le_cb {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) {f : Euc d → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    weightedSobolevE r P f ≤ ENNReal.ofReal (s57pC d r P * B) := by
  have hS := s57p_S_le (r := r) hP (f := f) (B := B)
    (fun j hj i x => (s57p_abs_partialDeriv_le i f x).trans (hB j hj x))
  rw [s57p_E_eq]
  have hW : 0 ≤ ∫ x : Euc d, s57pW d P x := integral_nonneg fun x => s57pW_nonneg P x
  calc (s57pS d r P f) ^ (1 / 2 : ℝ) ≤ (ENNReal.ofReal ((s57pN d r : ℝ) * (B ^ 2 * ∫ x, s57pW d P x))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hS (by norm_num)
    _ = ENNReal.ofReal (((s57pN d r : ℝ) * (B ^ 2 * ∫ x, s57pW d P x)) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (sq_nonneg B) hW)) (by norm_num)
    _ = ENNReal.ofReal (s57pC d r P * B) := by
        congr 1
        unfold s57pC
        rw [← Real.sqrt_eq_rpow, show ((s57pN d r : ℝ) * (B ^ 2 * ∫ x : Euc d, s57pW d P x)) =
          ((s57pN d r : ℝ) * ∫ x : Euc d, s57pW d P x) * B ^ 2 by ring,
          Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) hW), Real.sqrt_sq hB0]

theorem s57p_initial_bound {r : ℕ} {P : ℝ} (hP : (d : ℝ) < 2 * P) {η : (Euc d → ℝ) → ℝ}
    (hη : IsBoundedLinearOnE r P η) {f : Euc d → ℝ} (hf : ContDiff ℝ r f) {B : ℝ}
    (hB : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    ENNReal.ofReal |η f| ≤ dualNormE r P η * ENNReal.ofReal (s57pC d r P * B) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (Nat.zero_le _) 0)
  exact (s57p_dual_bound hP hη hf hB).trans (mul_le_mul' le_rfl (s57p_E_le_cb hP hB0 hB))

end HRS.MS.FixEq
