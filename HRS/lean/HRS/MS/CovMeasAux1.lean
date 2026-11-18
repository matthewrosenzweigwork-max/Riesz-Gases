import HRS.MS.GoFeatTie
import HRS.MS.GenPathAux7
import HRS.MS.FixEqP1Aux1
import HRS.Uniform.Q45Cov
import HRS.Whole.Window

/-!
# S10.1 `r2_covariance_measure` (worker S101B), part 1: plan and `ℓ²`-valued smoothness

Frozen statement: `HRS.Whole.r2_covariance_measure` (`HRS/Whole/Window.lean`, TeX supplement L7740-7767).  Prefix `s101_`, namespace
`HRS.MS.CovMeas`.  The full plan is `S101_PLAN.md` in the scratch directory; this docstring is its record.

## Verdict on the frozen statement

TRUE and non-vacuous (the all-junk world `propagatorW = 0` gives `J = 0`; the proof below is insensitive to it because the base value
of the feature is the diagonal `U^{τ,τ}φ_α`).  No Bochner/`eLpNorm`/`Measure.map`/`tsum` junk is used: `IsR2L1F` carries the norm
continuity of `z^u`, `s57p_dual_bound` (S57P, cutoff + mollification) converts it into `|z f| ≤ dualNormE(z) ‖f‖_E` for `C^r` functions
with bounded derivatives, `R2OrbitSummable` gives `ℓ²`-summable sup bounds (ENNReal tsum `< ⊤`), and the integral of `IsR2JValue` is
a genuine integral (integrable by `∫⁻ dualNormE < ⊤`).

## Route

The torus abstract result `HRS.Uniform.covariance_measure_proof` (`HRS/Uniform/Q45Cov.lean`: stochastic convolution with continuous
version, maximal estimate, `E[Z ⊗ Z]` in the projective tensor square, additivity, continuity, TV bound, linearity in the covariance
density, evaluation formula) is applied to `H = E = 𝒦 = KSpace d m T` with the identity evolution `s56_idEvol` (`s56_idEvol_maxHyp`).
The covariance density is `D_τ(u,v) = 2ν z^τ(∇g^τ_u · ∇g^τ_v)`, `g^τ_u(x) = ⟨Γ_τ(x),u⟩`, with the feature
`Γ_τ(x) = (U^{τ,τ}φ_α(x), 1_{s>τ} ∂_sU^{τ,s}φ_α(x), U^{τ,τ}φ_α(x))_α ∈ 𝒦` (the `𝒦`-feature of S5.2 with the time derivative of the
orbit assumption).  `s56_reconCLM` and `Q45.tensorMap` push the measure to `OscPath` and a bridge lands in the frozen `projTensor`.

Operator trick: for a bounded bilinear form `Bil` on `𝒦` put `F_Bil(x) = Σ_k Bil(∂_kΓ(x), ∂_kΓ(x))`; `D_τ(u,v) = 2ν z^τ(F_{u⊗v})` and the
trace norm of `D_τ` is `≤ 2|ν| dualNormE(z^τ) · C` because `Σ ε_i e_i ⊗ f_i` has norm `≤ 1`.  No Riesz representative of `z^τ`,
Leibniz sum or density lemma is needed.

## Packets and sizes (Lean lines)

* P1 (Aux1, Aux2, ~700): `s101_ell2_contDiff` (this file); extraction of the `ℓ²`-summable sup bounds from `R2OrbitSummable`.
* P2 (Aux3, Aux4, ~900): FTC in `t`, measurability in `s`, the feature `Γ_τ : ℝ^d → 𝒦` of class `C^{r+1}` (`s55f_L2_contDiff`).
* P3 (Aux5, Aux6, ~900): `F_Bil`, `D_τ`, bounded symmetric bilinear forms, trace-norm bound, trace density minus measurability.
* P4 (Aux7, Aux8, ~1000): measurability in `τ` (hypothesis `R2JIntegrandMeas` for the `U×U` pairings, dyadic approximation for the
  diagonal pairings, countable dense class, Borel full-measure set).
* P5 (Aux9, ~450): bridge `ProjTensor2 → projTensor`, push forward by `𝒯`, a.e.-invariance of `J`.
* P6 (Aux10, Aux11, ~800): observation vectors, pairing identities, the four-term sum.
* P7 (Aux12, CovMeasTie, ~700): assembly and the `type_of%` tie.

## This file

`s101_ell2_contDiff`: a family `g_α` of `C^k` functions on `ℝ^d` with `ℓ²`-summable derivative sup bounds `c_α` defines the `C^k` map
`x ↦ ellVec (g_α x) ∈ ℓ²` with `‖D^j‖ ≤ (Σ c_α²)^{1/2}` (the existing `s55f_ell_contDiff` needs `ℓ¹` bounds).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go

variable {d : ℕ}

lemma s101_memℓp_of_bound {c b : MultiIndex d → ℝ} (hb : Summable fun α => b α ^ 2)
    (h : ∀ α, |c α| ≤ b α) : Memℓp c 2 := by
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => ?_) hb
  have := abs_le.1 (h α)
  exact sq_le_sq' this.1 this.2

lemma s101_ellVec_coord {m : ℝ} {c : MultiIndex d → ℝ} (h : Memℓp c 2) (α : MultiIndex d) :
    OscDual.coord (ellVec (d := d) m c) α = c α := by
  have e := s55f_ellVec_eq (d := d) (m := m) h
  unfold OscDual.coord
  rw [e]

lemma s101_norm_ellVec_sq {m : ℝ} {c : MultiIndex d → ℝ} (h : Memℓp c 2) :
    ‖ellVec (d := d) m c‖ ^ 2 = ∑' α, c α ^ 2 := by
  have e := s55f_ellVec_eq (d := d) (m := m) h
  have := lp_two_norm_sq (⟨c, h⟩ : lp (fun _ : MultiIndex d => ℝ) 2)
  show ‖(ellVec (d := d) m c : lp (fun _ : MultiIndex d => ℝ) 2)‖ ^ 2 = _
  rw [e]
  exact this

lemma s101_norm_ellVec_le {m : ℝ} {c b : MultiIndex d → ℝ} (hb : Summable fun α => b α ^ 2)
    (h : ∀ α, |c α| ≤ b α) :
    ‖ellVec (d := d) m c‖ ≤ Real.sqrt (∑' α, b α ^ 2) := by
  have hm := s101_memℓp_of_bound hb h
  have hsq := s101_norm_ellVec_sq (m := m) hm
  have hc : Summable fun α => c α ^ 2 := memℓp_two_iff.1 hm
  have hle : ∑' α, c α ^ 2 ≤ ∑' α, b α ^ 2 := by
    refine hc.tsum_le_tsum (fun α => ?_) hb
    have := abs_le.1 (h α)
    exact sq_le_sq' this.1 this.2
  rw [← Real.sqrt_sq (norm_nonneg _), hsq]
  exact Real.sqrt_le_sqrt hle

lemma s101_ellVec_ext {m : ℝ} {x y : OscDual d m} (h : ∀ α, OscDual.coord x α = OscDual.coord y α) : x = y := by
  refine (Subtype.ext ?_ : (x : lp (fun _ : MultiIndex d => ℝ) 2) = y)
  funext α
  exact h α

lemma s101_ellVec_add {m : ℝ} {c c' : MultiIndex d → ℝ} (h : Memℓp c 2) (h' : Memℓp c' 2) :
    ellVec (d := d) m (fun α => c α + c' α) = ellVec m c + ellVec m c' := by
  have h2 : Memℓp (fun α => c α + c' α) 2 := h.add h'
  refine s101_ellVec_ext fun α => ?_
  rw [s101_ellVec_coord h2]
  show c α + c' α = OscDual.coord (ellVec (d := d) m c) α + OscDual.coord (ellVec (d := d) m c') α
  rw [s101_ellVec_coord h, s101_ellVec_coord h']

lemma s101_ellVec_smul {m : ℝ} {c : MultiIndex d → ℝ} (a : ℝ) (h : Memℓp c 2) :
    ellVec (d := d) m (fun α => a * c α) = a • ellVec m c := by
  have h2 : Memℓp (fun α => a * c α) 2 := by
    have h3 := h.const_smul a
    have e : (a • c) = (fun α => a * c α) := by funext α; simp
    rwa [e] at h3
  refine s101_ellVec_ext fun α => ?_
  rw [s101_ellVec_coord h2]
  show a * c α = a * OscDual.coord (ellVec (d := d) m c) α
  rw [s101_ellVec_coord h]

lemma s101_L_le {L : Euc d →L[ℝ] ℝ} {c : ℝ} (hL : ‖L‖ ≤ c) (h : Euc d) : |L h| ≤ c * ‖h‖ := by
  have := L.le_opNorm h
  rw [Real.norm_eq_abs] at this
  exact this.trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

lemma s101_summable_mul {c : MultiIndex d → ℝ} (hc : Summable fun α => c α ^ 2) (a : ℝ) :
    Summable fun α => (c α * a) ^ 2 := by
  simpa [mul_pow] using hc.mul_right (a ^ 2)

lemma s101_sqrt_tsum_mul {c : MultiIndex d → ℝ} (a : ℝ) :
    Real.sqrt (∑' α, (c α * a) ^ 2) = Real.sqrt (∑' α, c α ^ 2) * |a| := by
  have : ∑' α, (c α * a) ^ 2 = (∑' α, c α ^ 2) * a ^ 2 := by
    rw [← tsum_mul_right]; exact tsum_congr fun α => by ring
  rw [this, Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq_eq_abs]

lemma s101_memℓp_L {L : MultiIndex d → (Euc d →L[ℝ] ℝ)} {c : MultiIndex d → ℝ}
    (hc : Summable fun α => c α ^ 2) (hL : ∀ α, ‖L α‖ ≤ c α) (h : Euc d) :
    Memℓp (fun α => L α h) 2 :=
  s101_memℓp_of_bound (b := fun α => c α * ‖h‖) (s101_summable_mul hc _) fun α => s101_L_le (hL α) h

/-- The `ℓ²`-valued bounded linear map `h ↦ ellVec (L_α h)` of a family with `‖L_α‖ ≤ c_α`. -/
def s101EllCLM (m : ℝ) (L : MultiIndex d → (Euc d →L[ℝ] ℝ)) (c : MultiIndex d → ℝ)
    (hc : Summable fun α => c α ^ 2) (hL : ∀ α, ‖L α‖ ≤ c α) : Euc d →L[ℝ] OscDual d m :=
  LinearMap.mkContinuous
    { toFun := fun h => ellVec (d := d) m (fun α => L α h)
      map_add' := fun h h' => by
        have := s101_ellVec_add (m := m) (s101_memℓp_L hc hL h) (s101_memℓp_L hc hL h')
        simpa [map_add] using this
      map_smul' := fun a h => by
        have := s101_ellVec_smul (m := m) a (s101_memℓp_L hc hL h)
        simpa [map_smul] using this }
    (Real.sqrt (∑' α, c α ^ 2)) (fun h => by
      show ‖ellVec (d := d) m (fun α => L α h)‖ ≤ _
      have := s101_norm_ellVec_le (m := m) (c := fun α => L α h) (b := fun α => c α * ‖h‖)
        (s101_summable_mul hc _) fun α => s101_L_le (hL α) h
      rwa [s101_sqrt_tsum_mul, abs_of_nonneg (norm_nonneg h)] at this)

lemma s101EllCLM_apply (m : ℝ) (L : MultiIndex d → (Euc d →L[ℝ] ℝ)) (c : MultiIndex d → ℝ)
    (hc : Summable fun α => c α ^ 2) (hL : ∀ α, ‖L α‖ ≤ c α) (h : Euc d) :
    s101EllCLM m L c hc hL h = ellVec (d := d) m (fun α => L α h) := rfl

lemma s101_norm_sq_tsum {m : ℝ} (u : OscDual d m) :
    ‖u‖ ^ 2 = ∑' α, (OscDual.coord u α) ^ 2 :=
  lp_two_norm_sq (show lp (fun _ : MultiIndex d => ℝ) 2 from u)

lemma s101_coord_sub {m : ℝ} (u v : OscDual d m) (α : MultiIndex d) :
    OscDual.coord (u - v) α = OscDual.coord u α - OscDual.coord v α := rfl

lemma s101_ell_continuous {m : ℝ} (g : MultiIndex d → Euc d → ℝ) (c : MultiIndex d → ℝ)
    (hc : Summable fun α => c α ^ 2) (hg : ∀ α, Continuous (g α)) (hb : ∀ α x, |g α x| ≤ c α) :
    Continuous fun x => ellVec (d := d) m (fun α => g α x) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hmem : ∀ y, Memℓp (fun α => g α y) 2 := fun y => s101_memℓp_of_bound hc fun α => hb α y
  have hsq : ∀ y, ‖ellVec (d := d) m (fun α => g α y) - ellVec (d := d) m (fun α => g α x)‖ ^ 2 =
      ∑' α, (g α y - g α x) ^ 2 := by
    intro y
    rw [s101_norm_sq_tsum]
    refine tsum_congr fun α => ?_
    rw [s101_coord_sub, s101_ellVec_coord (hmem y), s101_ellVec_coord (hmem x)]
  have ht : Tendsto (fun y => ∑' α, (g α y - g α x) ^ 2) (𝓝 x) (𝓝 (∑' _ : MultiIndex d, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun α => (2 * c α) ^ 2)
      (by simpa [mul_pow] using hc.mul_left 4 |>.congr fun α => by ring) (fun α => ?_)
      (Eventually.of_forall fun y α => ?_)
    · have := (((hg α).tendsto x).sub_const (g α x)).pow 2
      simpa using this
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 := hb α y
      have h2 := hb α x
      have h3 := abs_le.1 h1
      have h4 := abs_le.1 h2
      exact sq_le_sq' (by linarith) (by linarith)
  have ht0 : Tendsto (fun y => ∑' α, (g α y - g α x) ^ 2) (𝓝 x) (𝓝 0) := by simpa using ht
  have hs : Tendsto (fun y => Real.sqrt (∑' α, (g α y - g α x) ^ 2)) (𝓝 x) (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp ht0
  rw [Real.sqrt_zero] at hs
  refine hs.congr fun y => ?_
  rw [← hsq y, Real.sqrt_sq (norm_nonneg _)]

lemma s101_ell_hasFDerivAt {m : ℝ} (g : MultiIndex d → Euc d → ℝ) (c : MultiIndex d → ℝ)
    (hc : Summable fun α => c α ^ 2) (hg : ∀ α, ContDiff ℝ 1 (g α))
    (hb0 : ∀ α x, |g α x| ≤ c α) (hb1 : ∀ α x, ‖fderiv ℝ (g α) x‖ ≤ c α) (x : Euc d) :
    HasFDerivAt (fun y => ellVec (d := d) m (fun α => g α y))
      (s101EllCLM m (fun α => fderiv ℝ (g α) x) c hc (fun α => hb1 α x)) x := by
  rw [hasFDerivAt_iff_tendsto]
  have hmem : ∀ y, Memℓp (fun α => g α y) 2 := fun y => s101_memℓp_of_bound hc fun α => hb0 α y
  have hdiff : ∀ α, Differentiable ℝ (g α) := fun α => (hg α).differentiable one_ne_zero
  have hsq : ∀ y, ‖ellVec (d := d) m (fun α => g α y) - ellVec (d := d) m (fun α => g α x) -
      s101EllCLM m (fun α => fderiv ℝ (g α) x) c hc (fun α => hb1 α x) (y - x)‖ ^ 2 =
      ∑' α, (g α y - g α x - fderiv ℝ (g α) x (y - x)) ^ 2 := by
    intro y
    rw [s101_norm_sq_tsum]
    refine tsum_congr fun α => ?_
    rw [s101_coord_sub, s101_coord_sub, s101_ellVec_coord (hmem y), s101_ellVec_coord (hmem x),
      s101EllCLM_apply, s101_ellVec_coord (s101_memℓp_L hc (fun α => hb1 α x) (y - x))]
  have key : Tendsto (fun y => ∑' α, (‖y - x‖⁻¹ * ‖g α y - g α x - fderiv ℝ (g α) x (y - x)‖) ^ 2)
      (𝓝 x) (𝓝 0) := by
    have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 x)
      (f := fun y α => (‖y - x‖⁻¹ * ‖g α y - g α x - fderiv ℝ (g α) x (y - x)‖) ^ 2)
      (g := fun _ => (0 : ℝ)) (bound := fun α => (2 * c α) ^ 2)
      (by simpa [mul_pow] using hc.mul_left 4 |>.congr fun α => by ring) (fun α => ?_)
      (Eventually.of_forall fun y α => ?_)
    · simpa using this
    · have h1 := hasFDerivAt_iff_tendsto.1 (hdiff α x).hasFDerivAt
      simpa using h1.pow 2
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hyx : y = x
      · subst hyx; simp; positivity
      · have hpos : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hyx)
        have hmv : ‖g α y - g α x‖ ≤ c α * ‖y - x‖ :=
          Convex.norm_image_sub_le_of_norm_fderiv_le (f := g α) (s := Set.univ)
            (fun z _ => (hdiff α) z) (fun z _ => hb1 α z) convex_univ (Set.mem_univ _) (Set.mem_univ _)
        have hL : ‖fderiv ℝ (g α) x (y - x)‖ ≤ c α * ‖y - x‖ :=
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hb1 α x) (norm_nonneg _))
        have hR : ‖g α y - g α x - fderiv ℝ (g α) x (y - x)‖ ≤ 2 * c α * ‖y - x‖ := by
          have := norm_sub_le (g α y - g α x) (fderiv ℝ (g α) x (y - x))
          have e : ‖g α y - g α x‖ = ‖g α y - g α x‖ := rfl
          nlinarith
        have h2 : ‖y - x‖⁻¹ * ‖g α y - g α x - fderiv ℝ (g α) x (y - x)‖ ≤ 2 * c α := by
          rw [inv_mul_le_iff₀ hpos]
          linarith
        exact pow_le_pow_left₀ (by positivity) h2 2
  have hs : Tendsto (fun y => Real.sqrt (∑' α, (‖y - x‖⁻¹ *
      ‖g α y - g α x - fderiv ℝ (g α) x (y - x)‖) ^ 2)) (𝓝 x) (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp key
  rw [Real.sqrt_zero] at hs
  refine hs.congr fun y => ?_
  have h1 : (‖y - x‖⁻¹ * ‖ellVec (d := d) m (fun α => g α y) - ellVec (d := d) m (fun α => g α x) -
      s101EllCLM m (fun α => fderiv ℝ (g α) x) c hc (fun α => hb1 α x) (y - x)‖) ^ 2 =
      ∑' α, (‖y - x‖⁻¹ * ‖g α y - g α x - fderiv ℝ (g α) x (y - x)‖) ^ 2 := by
    rw [mul_pow, hsq y, ← tsum_mul_left]
    refine tsum_congr fun α => ?_
    rw [mul_pow, Real.norm_eq_abs, sq_abs]
  show Real.sqrt _ = ‖y - x‖⁻¹ * _
  rw [← h1, Real.sqrt_sq (by positivity)]

theorem s101_ell2_contDiff {m : ℝ} (k : ℕ) : ∀ (g : MultiIndex d → Euc d → ℝ) (c : MultiIndex d → ℝ),
    (Summable fun α => c α ^ 2) → (∀ α, ContDiff ℝ k (g α)) →
    (∀ α, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (g α) x‖ ≤ c α) →
    ContDiff ℝ k (fun x => ellVec (d := d) m (fun α => g α x)) ∧
    ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) m (fun α => g α x)) x‖ ≤
      Real.sqrt (∑' α, c α ^ 2) := by
  induction k with
  | zero =>
    intro g c hc hg hb
    have hb0 : ∀ α x, |g α x| ≤ c α := fun α x => by
      simpa using hb α 0 le_rfl x
    refine ⟨contDiff_zero.2 (s101_ell_continuous g c hc (fun α => (hg α).continuous) hb0),
      fun j hj x => ?_⟩
    have : j = 0 := by omega
    subst this
    rw [norm_iteratedFDeriv_zero]
    exact s101_norm_ellVec_le hc fun α => hb0 α x
  | succ k ih =>
    intro g c hc hg hb
    have hg1 : ∀ α, ContDiff ℝ 1 (g α) := fun α => (hg α).of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hb0 : ∀ α x, |g α x| ≤ c α := fun α x => by
      simpa using hb α 0 (Nat.zero_le _) x
    have hb1 : ∀ α x, ‖fderiv ℝ (g α) x‖ ≤ c α := fun α x => by
      have := hb α 1 (by omega) x
      rwa [norm_iteratedFDeriv_one] at this
    set Θ : Euc d → (Euc d →L[ℝ] OscDual d m) := fun x =>
      s101EllCLM m (fun α => fderiv ℝ (g α) x) c hc (fun α => hb1 α x) with hΘ
    have hder : ∀ x, HasFDerivAt (fun y => ellVec (d := d) m (fun α => g α y)) (Θ x) x := fun x =>
      s101_ell_hasFDerivAt g c hc hg1 hb0 hb1 x
    have hslice : ∀ h : Euc d, ContDiff ℝ k (fun x => Θ x h) ∧
        ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => Θ x h) x‖ ≤ Real.sqrt (∑' α, c α ^ 2) * ‖h‖ := by
      intro h
      have hFh : ∀ α, ContDiff ℝ k (fun x => fderiv ℝ (g α) x h) := fun α =>
        ((hg α).fderiv_right (m := k) (by push_cast; exact le_rfl)).clm_apply contDiff_const
      have hbh : ∀ α, ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (g α) x h) x‖ ≤ c α * ‖h‖ := by
        intro α j hj x
        have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ (g α)) (c := h) (x := x)
          (N := (k : WithTop ℕ∞)) (n := j)
          (((hg α).fderiv_right (m := k) (by push_cast; exact le_rfl)).contDiffAt) (by exact_mod_cast hj)
        rw [norm_iteratedFDeriv_fderiv] at h1
        calc _ ≤ ‖h‖ * ‖iteratedFDeriv ℝ (j + 1) (g α) x‖ := h1
          _ ≤ ‖h‖ * c α := mul_le_mul_of_nonneg_left (hb α (j + 1) (by omega) x) (norm_nonneg _)
          _ = c α * ‖h‖ := mul_comm _ _
      have := ih (fun α x => fderiv ℝ (g α) x h) (fun α => c α * ‖h‖) (s101_summable_mul hc _) hFh hbh
      refine ⟨this.1, fun j hj x => (this.2 j hj x).trans ?_⟩
      rw [s101_sqrt_tsum_mul, abs_of_nonneg (norm_nonneg h)]
    have hΘcd : ContDiff ℝ k Θ := contDiff_clm_apply_iff.2 fun h => (hslice h).1
    refine ⟨?_, fun j hj x => ?_⟩
    · rw [show ((k + 1 : ℕ) : WithTop ℕ∞) = (k : WithTop ℕ∞) + 1 by push_cast; rfl]
      exact contDiff_succ_iff_hasFDerivAt.2 ⟨Θ, hΘcd, hder⟩
    · rcases j with _ | j
      · rw [norm_iteratedFDeriv_zero]
        exact s101_norm_ellVec_le hc fun α => hb0 α x
      · have hfd : fderiv ℝ (fun y => ellVec (d := d) m (fun α => g α y)) = Θ :=
          funext fun y => (hder y).fderiv
        rw [← norm_iteratedFDeriv_fderiv, hfd]
        have hjk : j ≤ k := by omega
        refine ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _) fun mm => ?_
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
        have hcomp := (ContinuousLinearMap.apply ℝ (OscDual d m) h).iteratedFDeriv_comp_left
          (hΘcd.contDiffAt (x := x)) (i := j) (by exact_mod_cast hjk)
        have e1 : (ContinuousLinearMap.apply ℝ (OscDual d m) h ∘ Θ) = fun y => Θ y h := rfl
        rw [e1] at hcomp
        have e2 : (iteratedFDeriv ℝ j Θ x mm) h = iteratedFDeriv ℝ j (fun y => Θ y h) x mm := by
          rw [hcomp]; rfl
        rw [e2]
        have h3 := (iteratedFDeriv ℝ j (fun y => Θ y h) x).le_opNorm mm
        have h4 := (hslice h).2 j hjk x
        calc ‖iteratedFDeriv ℝ j (fun y => Θ y h) x mm‖
            ≤ ‖iteratedFDeriv ℝ j (fun y => Θ y h) x‖ * ∏ i, ‖mm i‖ := h3
          _ ≤ Real.sqrt (∑' α, c α ^ 2) * ‖h‖ * ∏ i, ‖mm i‖ := mul_le_mul_of_nonneg_right h4 (by positivity)
          _ = (Real.sqrt (∑' α, c α ^ 2) * ∏ i, ‖mm i‖) * ‖h‖ := by ring

end HRS.MS.CovMeas
