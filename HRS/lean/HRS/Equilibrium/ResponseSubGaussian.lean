import HRS.Equilibrium.ResponseVariance

/-!
# HRS.Equilibrium.ResponseSubGaussian (packet Q32d): Lemma 4.19, `V:eq:response-subGaussian`

Relocated proof of `HRS.response_subGaussian` (statement copied verbatim from `Response.lean`,
where its frozen placeholder stays).  Route: the proof sketch at the end of `ResponseVariance.lean`.
Helper names carry the prefix `q32d_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

section Q32dAnalysis

/-- Chernoff upper tail for a probability measure. -/
theorem q32d_chernoff {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Z ω)) μ)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (hx : 0 ≤ x)
    (hmgf : ∀ t : ℝ, 0 ≤ t → t ≤ x / D → ∫ ω, Real.exp (t * Z ω) ∂μ ≤ Real.exp (D * t ^ 2 / 2)) :
    μ {ω | x < Z ω} ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) := by
  have ht0 : 0 ≤ x / D := div_nonneg hx hD.le
  have hmain : μ.real {ω | x ≤ Z ω} ≤ Real.exp (-(x / D) * x) * mgf Z μ (x / D) :=
    measure_ge_le_exp_mul_mgf x ht0 (hint _)
  have hmgf' : mgf Z μ (x / D) ≤ Real.exp (D * (x / D) ^ 2 / 2) := hmgf _ ht0 le_rfl
  have hexp : Real.exp (-(x / D) * x) * Real.exp (D * (x / D) ^ 2 / 2) =
      Real.exp (-x ^ 2 / (2 * D)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  have hle : μ.real {ω | x < Z ω} ≤ Real.exp (-x ^ 2 / (2 * D)) := by
    calc μ.real {ω | x < Z ω} ≤ μ.real {ω | x ≤ Z ω} :=
          measureReal_mono (μ := μ) (s₁ := {ω | x < Z ω}) (s₂ := {ω | x ≤ Z ω})
            (by intro ω hω; exact le_of_lt (show x < Z ω from hω)) (measure_ne_top _ _)
      _ ≤ Real.exp (-(x / D) * x) * mgf Z μ (x / D) := hmain
      _ ≤ Real.exp (-(x / D) * x) * Real.exp (D * (x / D) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hmgf' (Real.exp_pos _).le
      _ = Real.exp (-x ^ 2 / (2 * D)) := hexp
  calc μ {ω | x < Z ω} = ENNReal.ofReal (μ.real {ω | x < Z ω}) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) := ENNReal.ofReal_le_ofReal hle

/-- Quadratic bound on `[0, T]` from a one-sided derivative bound (monotonicity of
`u ↦ D u²/2 - f u`). -/
theorem q32d_quad_nonneg (f f' : ℝ → ℝ) (D T : ℝ) (h0 : f 0 = 0)
    (hf : ∀ u, 0 ≤ u → u ≤ T → HasDerivAt f (f' u) u)
    (hb : ∀ u, 0 ≤ u → u ≤ T → f' u ≤ D * u) (t : ℝ) (ht0 : 0 ≤ t) (htT : t ≤ T) :
    f t ≤ D * t ^ 2 / 2 := by
  have hGd : ∀ u, 0 ≤ u → u ≤ T →
      HasDerivAt (fun u => D * u ^ 2 / 2 - f u) (D * u - f' u) u := by
    intro u h1 h2
    have h := (((hasDerivAt_pow 2 u).const_mul D).div_const 2).sub (hf u h1 h2)
    convert h using 1
    norm_num
    ring
  have hmono : MonotoneOn (fun u => D * u ^ 2 / 2 - f u) (Set.Icc 0 t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t) (f' := fun u => D * u - f' u)
      ?_ ?_ ?_
    · intro u hu
      exact (hGd u hu.1 (le_trans hu.2 htT)).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      exact (hGd u hu.1.le (le_trans hu.2.le htT)).hasDerivWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      have := hb u hu.1.le (le_trans hu.2.le htT)
      show 0 ≤ D * u - f' u
      linarith
  have h := hmono ⟨le_refl 0, ht0⟩ ⟨ht0, le_refl t⟩ ht0
  norm_num [h0] at h
  linarith

/-- Two-sided version: `|f'| ≤ D |u|` on `[-T, T]` gives `f t ≤ D t²/2` for `|t| ≤ T`. -/
theorem q32d_quad_bound (f f' : ℝ → ℝ) (D T : ℝ) (h0 : f 0 = 0)
    (hf : ∀ u, |u| ≤ T → HasDerivAt f (f' u) u)
    (hb : ∀ u, |u| ≤ T → |f' u| ≤ D * |u|) (t : ℝ) (ht : |t| ≤ T) :
    f t ≤ D * t ^ 2 / 2 := by
  rcases le_total 0 t with ht0 | ht0
  · have htT : t ≤ T := le_trans (le_abs_self t) ht
    refine q32d_quad_nonneg f f' D T h0 (fun u h1 h2 => hf u ?_) (fun u h1 h2 => ?_) t ht0 htT
    · rw [abs_of_nonneg h1]; exact h2
    · have h3 := hb u (by rw [abs_of_nonneg h1]; exact h2)
      rw [abs_of_nonneg h1] at h3
      exact le_trans (le_abs_self _) h3
  · have hnt : -t ≤ T := le_trans (neg_le_abs t) ht
    have hg : ∀ u, 0 ≤ u → u ≤ T →
        HasDerivAt (fun u => f (-u)) (f' (-u) * (-1)) u := by
      intro u h1 h2
      have h := (hf (-u) (by rw [abs_neg, abs_of_nonneg h1]; exact h2)).comp u (hasDerivAt_neg u)
      exact h
    have hbg : ∀ u, 0 ≤ u → u ≤ T → f' (-u) * (-1) ≤ D * u := by
      intro u h1 h2
      have h3 := hb (-u) (by rw [abs_neg, abs_of_nonneg h1]; exact h2)
      rw [abs_neg, abs_of_nonneg h1] at h3
      have h4 := neg_le_abs (f' (-u))
      linarith
    have key := q32d_quad_nonneg (fun u => f (-u)) (fun u => f' (-u) * (-1)) D T
      (by simpa using h0) hg hbg (-t) (by linarith) hnt
    simpa using key

theorem q32d_exp_log (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.exp (Real.log x - Real.log y - z) = x / y * Real.exp (-z) := by
  rw [Real.exp_sub, Real.exp_sub, Real.exp_log hx, Real.exp_log hy, Real.exp_neg]
  ring

theorem q32d_alg (r N : ℝ) (hr : 0 < r) (hrN : N = r * r) (t S M θ : ℝ) :
    θ * S + t * (r * ((1 / N) * S - M)) = (θ + t / r) * S + -(t * r * M) := by
  subst hrN
  field_simp
  ring

/-- Log-mgf tail input: `Ψ(t) = log A(θ + t/√N) - log A(θ) - t√N M(θ) ≤ D t²/2` for `|t| ≤ √N`,
when `A' = N M A` and `M' = V` with `|V| ≤ D` on the compact enlargement. -/
theorem q32d_psi (A M V : ℝ → ℝ) (N : ℕ) (hN : 0 < N) (a b D : ℝ)
    (hA : ∀ u, 0 < A u) (hAd : ∀ u, HasDerivAt A ((N : ℝ) * M u * A u) u)
    (hMd : ∀ u, HasDerivAt M (V u) u) (hV : ∀ u, a - 1 ≤ u → u ≤ b + 1 → |V u| ≤ D)
    (θ : ℝ) (hθa : a ≤ θ) (hθb : θ ≤ b) (t : ℝ) (ht : |t| ≤ Real.sqrt (N : ℝ)) :
    Real.log (A (θ + t / Real.sqrt (N : ℝ))) - Real.log (A θ) - t * Real.sqrt (N : ℝ) * M θ ≤
      D * t ^ 2 / 2 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNpos
  have hrN : (N : ℝ) = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := (Real.mul_self_sqrt hNpos.le).symm
  generalize hr_def : Real.sqrt (N : ℝ) = r at hr hrN ht ⊢
  have hlin : ∀ u : ℝ, HasDerivAt (fun u : ℝ => θ + u / r) (1 / r) u := fun u => by
    have h := ((hasDerivAt_id u).div_const r).const_add θ
    simpa using h
  have hcomp : ∀ u : ℝ, HasDerivAt (fun u : ℝ => A (θ + u / r))
      ((N : ℝ) * M (θ + u / r) * A (θ + u / r) * (1 / r)) u := fun u =>
    (hAd (θ + u / r)).comp u (hlin u)
  have hlog : ∀ u : ℝ, HasDerivAt (fun u : ℝ => Real.log (A (θ + u / r)))
      ((N : ℝ) * M (θ + u / r) * (1 / r)) u := fun u => by
    have h := (hcomp u).log (hA _).ne'
    convert h using 1
    field_simp [(hA _).ne']
  have hΨd : ∀ u : ℝ, HasDerivAt
      (fun u : ℝ => Real.log (A (θ + u / r)) - Real.log (A θ) - u * r * M θ)
      ((N : ℝ) * M (θ + u / r) * (1 / r) - r * M θ) u := fun u => by
    have h := ((hlog u).sub_const (Real.log (A θ))).sub
      (((hasDerivAt_id u).mul_const r).mul_const (M θ))
    convert h using 1
    · funext u'
      simp [Pi.sub_apply]
    · simp
  have hfb : ∀ u : ℝ, |u| ≤ r →
      |(N : ℝ) * M (θ + u / r) * (1 / r) - r * M θ| ≤ D * |u| := by
    intro u hu
    have hur : |u / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hr, div_le_one hr]
      exact hu
    obtain ⟨h1, h2⟩ := abs_le.1 hur
    have hMV := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := M) (f' := V)
      (s := Set.Icc (a - 1) (b + 1)) (C := D) (fun x _ => (hMd x).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact hV x hx.1 hx.2) (convex_Icc _ _)
      (x := θ) (y := θ + u / r) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    rw [Real.norm_eq_abs, Real.norm_eq_abs, show θ + u / r - θ = u / r by ring] at hMV
    have hfeq : (N : ℝ) * M (θ + u / r) * (1 / r) - r * M θ = r * (M (θ + u / r) - M θ) := by
      have h3 : (N : ℝ) * M (θ + u / r) * (1 / r) = r * M (θ + u / r) := by
        rw [mul_assoc, hrN]
        field_simp
      rw [h3]
      ring
    rw [hfeq, abs_mul, abs_of_pos hr]
    calc r * |M (θ + u / r) - M θ| ≤ r * (D * |u / r|) := mul_le_mul_of_nonneg_left hMV hr.le
      _ = D * |u| := by
        rw [abs_div, abs_of_pos hr]
        field_simp
  have h0 : (fun u : ℝ => Real.log (A (θ + u / r)) - Real.log (A θ) - u * r * M θ) 0 = 0 := by
    simp
  exact q32d_quad_bound
    (fun u : ℝ => Real.log (A (θ + u / r)) - Real.log (A θ) - u * r * M θ)
    (fun u : ℝ => (N : ℝ) * M (θ + u / r) * (1 / r) - r * M θ) D r h0
    (fun u _ => hΨd u) hfb t ht

theorem q32d_four (e : ℝ) (he : 0 ≤ e) :
    ENNReal.ofReal e + ENNReal.ofReal e + (ENNReal.ofReal e + ENNReal.ofReal e) =
      ENNReal.ofReal (4 * e) := by
  rw [← ENNReal.ofReal_add he he, ← ENNReal.ofReal_add (add_nonneg he he) (add_nonneg he he)]
  congr 1
  ring

/-- Gaussian tails: the two one-sided bounds for `N(0, v)` with `v ≤ D`. -/
theorem q32d_gauss_tail (v : NNReal) (D : ℝ) (hD : 0 < D) (hvD : (v : ℝ) ≤ D) (x : ℝ)
    (hx : 0 ≤ x) :
    gaussianReal 0 v {z | x < z} ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) ∧
      gaussianReal 0 v {z | x < -z} ≤ ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) := by
  have hmgf : ∀ t : ℝ, ∫ z, Real.exp (t * z) ∂(gaussianReal 0 v) ≤ Real.exp (D * t ^ 2 / 2) := by
    intro t
    have h := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) t
    have h2 : ∫ z, Real.exp (t * z) ∂(gaussianReal 0 v) =
        Real.exp (0 * t + (v : ℝ) * t ^ 2 / 2) := h
    rw [h2]
    apply Real.exp_le_exp.2
    have : (v : ℝ) * t ^ 2 ≤ D * t ^ 2 := mul_le_mul_of_nonneg_right hvD (sq_nonneg t)
    linarith
  constructor
  · exact q32d_chernoff (gaussianReal 0 v) (fun z => z)
      (fun t => integrable_exp_mul_gaussianReal t) D hD x hx (fun t _ _ => hmgf t)
  · refine q32d_chernoff (gaussianReal 0 v) (fun z => -z) (fun t => ?_) D hD x hx
      (fun t _ _ => ?_)
    · have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) (-t)
      simpa [mul_neg, neg_mul] using h
    · have h := hmgf (-t)
      simp only [neg_mul, mul_neg, neg_sq] at h ⊢
      exact h

end Q32dAnalysis

section Q32dRate

variable {d : ℕ} {s : ℝ}

theorem q32d_rateY_cont (k : Lattice d) (β θ : ℝ) (N : ℕ) :
    Continuous (rateY d s k β N θ) := by
  unfold rateY
  exact continuous_const.mul ((continuous_const.mul (continuous_finset_sum _ fun i _ =>
    (Torus.continuous_cosMode k).comp (continuous_apply i))).sub continuous_const)

theorem q32d_gibbs_eq (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {β : ℝ} (hβ : 0 < β) {N : ℕ} (k : Lattice d) (θ : ℝ) :
    rateGibbs d s k β θ N =
      (ENNReal.ofReal (∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X))⁻¹ •
        (volume : Measure (Fin N → Torus d)).withDensity
          (fun X => ENNReal.ofReal (Real.exp (θ * respS k X) * respW gm β X)) :=
  resp_rateGibbs_eq (periodicRiesz d s) gm hgm_ae k β θ hβ.ne'

/-- Expectation under the canonical law as a ratio of tilted integrals. -/
theorem q32d_expect (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {β : ℝ} (hβ : 0 < β) {N : ℕ} (k : Lattice d) (θ : ℝ) (f : (Fin N → Torus d) → ℝ) :
    ∫ X, f X ∂(rateGibbs d s k β θ N) =
      (∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X
          ∂(volume : Measure (Fin N → Torus d)))⁻¹ *
        ∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X * f X
          ∂(volume : Measure (Fin N → Torus d)) := by
  have hDm : Measurable (fun X : Fin N → Torus d => Real.exp (θ * respS k X) * respW gm β X) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul
      (respS_continuous k N).measurable)).mul (respW_measurable gm hgm β)
  have hD0 : ∀ X : Fin N → Torus d, 0 ≤ Real.exp (θ * respS k X) * respW gm β X :=
    fun X => (mul_pos (Real.exp_pos _) (respW_pos gm β X)).le
  rw [q32d_gibbs_eq gm hgm hgm_ae hβ k θ]
  exact resp_integral_smul_withDensity _ _ hDm hD0 f

theorem q32d_isProb (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N)
    (k : Lattice d) (θ : ℝ) : IsProbabilityMeasure (rateGibbs d s k β θ N) := by
  have hint : Integrable (fun X : Fin N → Torus d => Real.exp (θ * respS k X) * respW gm β X)
      (volume : Measure (Fin N → Torus d)) := by
    have e : (fun X : Fin N → Torus d => Real.exp (θ * respS k X) * respW gm β X) =
        (fun X => (respS k X ^ 0 * respW gm β X) * Real.exp (θ * respS k X)) :=
      funext fun X => by ring
    rw [e]
    exact resp_integrable_term k gm hgm β hβ hc hgc hN 0 θ
  have hZ : 0 < ∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X
      ∂(volume : Measure (Fin N → Torus d)) := by
    rw [← resp_respA_zero_eq]
    exact resp_respA_zero_pos k gm hgm hβ hc hgc hN θ
  refine ⟨?_⟩
  rw [q32d_gibbs_eq gm hgm hgm_ae hβ k θ, Measure.smul_apply,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, smul_eq_mul]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun X => (mul_pos (Real.exp_pos _) (respW_pos gm β X)).le)]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hZ).ne' ENNReal.ofReal_ne_top

theorem q32d_mean_eq (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N)
    (k : Lattice d) (θ : ℝ) :
    rateMeanN d s k β N θ = respA k gm β N 1 θ / ((N : ℝ) * respA k gm β N 0 θ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := hNr.ne'
  have hDm : Measurable (fun X : Fin N → Torus d => Real.exp (θ * respS k X) * respW gm β X) :=
    (Real.continuous_exp.measurable.comp (measurable_const.mul
      (respS_continuous k N).measurable)).mul (respW_measurable gm hgm β)
  have hDb : ∀ X : Fin N → Torus d,
      |Real.exp (θ * respS k X) * respW gm β X| ≤
        Real.exp (|θ| * N) * Real.exp (β * c * N) := by
    intro X
    rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (respW_pos gm β X)]
    refine mul_le_mul ?_ (respW_bound gm hβ hc hgc hN X) (respW_pos gm β X).le (Real.exp_pos _).le
    apply Real.exp_le_exp.2
    calc θ * respS k X ≤ |θ * respS k X| := le_abs_self _
      _ = |θ| * |respS k X| := abs_mul _ _
      _ ≤ |θ| * N := mul_le_mul_of_nonneg_left (respS_abs_le k X) (abs_nonneg _)
  have hDperm : ∀ τ : Equiv.Perm (Fin N),
      ∀ᵐ X ∂(volume : Measure (Fin N → Torus d)),
        Real.exp (θ * respS k (fun j => X (τ j))) * respW gm β (fun j => X (τ j)) =
          Real.exp (θ * respS k X) * respW gm β X :=
    fun τ => resp_D_perm (periodicRiesz d s) gm (fun x => periodicRiesz_neg x) hgm_ae k β θ τ
  have hsumid := resp_integral_sum_cos k hN
    (fun X => Real.exp (θ * respS k X) * respW gm β X) hDm
    (Real.exp (|θ| * N) * Real.exp (β * c * N)) hDb hDperm
  beta_reduce at hsumid
  have hA1 : respA k gm β N 1 θ = ∫ X, respS k X * (Real.exp (θ * respS k X) * respW gm β X)
      ∂(volume : Measure (Fin N → Torus d)) := by
    unfold respA
    congr 1
    funext X
    ring
  have hcos : ∫ X, Torus.cosMode k (X ⟨0, hN⟩) * (Real.exp (θ * respS k X) * respW gm β X)
      ∂(volume : Measure (Fin N → Torus d)) = respA k gm β N 1 θ / (N : ℝ) := by
    rw [hA1, hsumid]
    field_simp
  have hZ : 0 < respA k gm β N 0 θ := resp_respA_zero_pos k gm hgm hβ hc hgc hN θ
  have hZ' : (∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X
      ∂(volume : Measure (Fin N → Torus d))) ≠ 0 := by
    rw [← resp_respA_zero_eq]
    exact hZ.ne'
  have hexp := q32d_expect gm hgm hgm_ae hβ k θ (fun X => Torus.cosMode k (X ⟨0, hN⟩))
  beta_reduce at hexp
  have hcomm : ∫ X : Fin N → Torus d, Real.exp (θ * respS k X) * respW gm β X *
      Torus.cosMode k (X ⟨0, hN⟩) ∂(volume : Measure (Fin N → Torus d)) =
      ∫ X, Torus.cosMode k (X ⟨0, hN⟩) * (Real.exp (θ * respS k X) * respW gm β X)
        ∂(volume : Measure (Fin N → Torus d)) :=
    integral_congr_ae (Filter.Eventually.of_forall fun X => by ring)
  unfold rateMeanN
  rw [resp_pair_firstMarginal hN _ (Torus.cosMode k) (Torus.continuous_cosMode k), hexp,
    resp_respA_zero_eq, hcomm, hcos]
  field_simp

theorem q32d_mean_abs_le (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N)
    (k : Lattice d) (θ : ℝ) [IsProbabilityMeasure (rateGibbs d s k β θ N)] :
    |rateMeanN d s k β N θ| ≤ 1 := by
  unfold rateMeanN
  rw [resp_pair_firstMarginal hN _ (Torus.cosMode k) (Torus.continuous_cosMode k)]
  have h := norm_integral_le_of_norm_le_const (μ := rateGibbs d s k β θ N) (C := 1)
    (f := fun X : Fin N → Torus d => Torus.cosMode k (X ⟨0, hN⟩))
    (Filter.Eventually.of_forall fun X => Torus.norm_cosMode_le k _)
  simpa using h

theorem q32d_rateY_abs_le (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N)
    (k : Lattice d) (θ : ℝ) [IsProbabilityMeasure (rateGibbs d s k β θ N)]
    (X : Fin N → Torus d) : |rateY d s k β N θ X| ≤ 2 * Real.sqrt N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hS : |(1 / (N : ℝ)) * respS k X| ≤ 1 := by
    have h1 := respS_abs_le k X
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / N)]
    calc 1 / (N : ℝ) * |respS k X| ≤ 1 / N * N := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp
  have hM := q32d_mean_abs_le gm hgm hgm_ae hβ hc hgc hN k θ
  have hY : rateY d s k β N θ X =
      Real.sqrt N * ((1 / (N : ℝ)) * respS k X - rateMeanN d s k β N θ) := rfl
  rw [hY, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have htri : |(1 / (N : ℝ)) * respS k X - rateMeanN d s k β N θ| ≤ 2 := by
    calc |(1 / (N : ℝ)) * respS k X - rateMeanN d s k β N θ|
        ≤ |(1 / (N : ℝ)) * respS k X| + |rateMeanN d s k β N θ| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hS hM
      _ = 2 := by norm_num
  calc Real.sqrt N * |(1 / (N : ℝ)) * respS k X - rateMeanN d s k β N θ| ≤ Real.sqrt N * 2 :=
        mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt N := by ring

theorem q32d_Y_integrable (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N)
    (k : Lattice d) (θ t : ℝ) [IsProbabilityMeasure (rateGibbs d s k β θ N)] :
    Integrable (fun X : Fin N → Torus d => Real.exp (t * rateY d s k β N θ X))
      (rateGibbs d s k β θ N) := by
  refine Integrable.of_bound (C := Real.exp (|t| * (2 * Real.sqrt N))) ?_ ?_
  · exact (Real.continuous_exp.comp (continuous_const.mul
      (q32d_rateY_cont k β θ N))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    calc t * rateY d s k β N θ X ≤ |t * rateY d s k β N θ X| := le_abs_self _
      _ = |t| * |rateY d s k β N θ X| := abs_mul _ _
      _ ≤ |t| * (2 * Real.sqrt N) :=
        mul_le_mul_of_nonneg_left (q32d_rateY_abs_le gm hgm hgm_ae hβ hc hgc hN k θ X)
          (abs_nonneg _)

theorem q32d_mgf_identity (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {β : ℝ} (hβ : 0 < β) {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 0 < N)
    (k : Lattice d) (θ t : ℝ) :
    ∫ X, Real.exp (t * rateY d s k β N θ X) ∂(rateGibbs d s k β θ N) =
      respA k gm β N 0 (θ + t / Real.sqrt N) / respA k gm β N 0 θ *
        Real.exp (-(t * Real.sqrt N * rateMeanN d s k β N θ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNr
  have hrN : (N : ℝ) = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) :=
    (Real.mul_self_sqrt hNr.le).symm
  rw [q32d_expect gm hgm hgm_ae hβ k θ (fun X => Real.exp (t * rateY d s k β N θ X))]
  beta_reduce
  have hpt : ∀ X : Fin N → Torus d,
      Real.exp (θ * respS k X) * respW gm β X * Real.exp (t * rateY d s k β N θ X) =
        Real.exp (-(t * Real.sqrt N * rateMeanN d s k β N θ)) *
          (Real.exp ((θ + t / Real.sqrt N) * respS k X) * respW gm β X) := by
    intro X
    have key : θ * respS k X + t * rateY d s k β N θ X =
        (θ + t / Real.sqrt N) * respS k X + -(t * Real.sqrt N * rateMeanN d s k β N θ) :=
      q32d_alg (Real.sqrt N) (N : ℝ) hr hrN t (respS k X) (rateMeanN d s k β N θ) θ
    calc Real.exp (θ * respS k X) * respW gm β X * Real.exp (t * rateY d s k β N θ X)
        = Real.exp (θ * respS k X + t * rateY d s k β N θ X) * respW gm β X := by
          rw [Real.exp_add]; ring
      _ = Real.exp ((θ + t / Real.sqrt N) * respS k X +
            -(t * Real.sqrt N * rateMeanN d s k β N θ)) * respW gm β X := by rw [key]
      _ = _ := by rw [Real.exp_add]; ring
  have hint : ∫ X : Fin N → Torus d,
      Real.exp (θ * respS k X) * respW gm β X * Real.exp (t * rateY d s k β N θ X)
        ∂(volume : Measure (Fin N → Torus d)) =
      Real.exp (-(t * Real.sqrt N * rateMeanN d s k β N θ)) *
        ∫ X : Fin N → Torus d, Real.exp ((θ + t / Real.sqrt N) * respS k X) * respW gm β X
          ∂(volume : Measure (Fin N → Torus d)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hint, resp_respA_zero_eq, resp_respA_zero_eq]
  ring

theorem q32d_mgf_bound (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) (gm : Torus d → ℝ) (hgm : Measurable gm)
    (hgm_ae : ∀ᵐ x ∂(volume : Measure (Torus d)), gm x = periodicRiesz d s x)
    {c : ℝ} (hc : 0 ≤ c) (hgc : ∀ x, -c ≤ gm x) {N : ℕ} (hN : 2 ≤ N) (a b D : ℝ)
    (hV : ∀ u, a - 1 ≤ u → u ≤ b + 1 → |rateVarN d s k β N u| ≤ D) (θ : ℝ) (hθa : a ≤ θ)
    (hθb : θ ≤ b) (t : ℝ) (ht : |t| ≤ Real.sqrt N) :
    ∫ X, Real.exp (t * rateY d s k β N θ X) ∂(rateGibbs d s k β θ N) ≤
      Real.exp (D * t ^ 2 / 2) := by
  have hN0 : 0 < N := by omega
  have hHa : ∀ u, 0 < respA k gm β N 0 u := fun u =>
    resp_respA_zero_pos k gm hgm hβ hc hgc hN0 u
  have hNr : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN0
    exact this.ne'
  have hAd : ∀ u, HasDerivAt (fun t => respA k gm β N 0 t)
      ((N : ℝ) * rateMeanN d s k β N u * respA k gm β N 0 u) u := by
    intro u
    have h := resp_respA_hasDerivAt k gm hgm hβ hc hgc hN0 0 u
    have e : respA k gm β N (0 + 1) u = (N : ℝ) * rateMeanN d s k β N u * respA k gm β N 0 u := by
      rw [zero_add, q32d_mean_eq gm hgm hgm_ae hβ hc hgc hN0 k u]
      have := (hHa u).ne'
      field_simp
    rw [e] at h
    exact h
  have hMd : ∀ u, HasDerivAt (rateMeanN d s k β N) (rateVarN d s k β N u) u :=
    fun u => (finite_response_rates hd hs hsd β hβ k hk N hN).2.2.1 u
  have hpsi := q32d_psi (fun u => respA k gm β N 0 u) (rateMeanN d s k β N)
    (rateVarN d s k β N) N hN0 a b D hHa hAd hMd hV θ hθa hθb t ht
  rw [q32d_mgf_identity gm hgm hgm_ae hβ hc hgc hN0 k θ t,
    ← q32d_exp_log _ _ _ (hHa _) (hHa _)]
  exact Real.exp_le_exp.2 hpsi

end Q32dRate

section Rates

variable {d : ℕ}
variable {s : ℝ}

/-- Lemma 4.19, `V:eq:response-subGaussian` (source lines 5227-5233): for every compact
interval `I = [a, b]` there is `D_I ≥ 2` with
`P_{N,θ}(|Y_{N,θ}| > x) + P(|G_θ| > x) ≤ 4 e^{-x²/(2D_I)}` for `x ≥ 0`, `N ≥ 2`, `θ ∈ I`, where
`G_θ ∼ N(0, C_{β,μ_θ}(φ,φ))`. -/
theorem response_subGaussian_proof (hd : 2 ≤ d) (hs : (d : ℝ) / 2 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (a b : ℝ) :
    ∃ D : ℝ, 2 ≤ D ∧ ∀ x : ℝ, 0 ≤ x → ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc a b,
      rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|} +
          gaussianReal 0 (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
            (Torus.cosMode k) (Torus.cosMode k)).toNNReal {z | x < |z|} ≤
        ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) := by
  have hs0 : 0 < s := by
    have h1 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨gm, hgm, c, hc, hgc, hgm_ae⟩ := resp_good_kernel hd hs0 hsd
  obtain ⟨C, hC⟩ := rateVarN_uniform_bound hd hs hsd β hβ k hk (a - 1) (b + 1)
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = max 2 (max C 1) := ⟨_, rfl⟩
  have hD2 : (2 : ℝ) ≤ D := by rw [hDdef]; exact le_max_left _ _
  have hDC : C ≤ D := by rw [hDdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hDdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hDpos : 0 < D := by linarith
  refine ⟨D, hD2, fun x hx N hN θ hθ => ?_⟩
  have hN0 : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  haveI := q32d_isProb gm hgm hgm_ae hβ hc hgc hN0 k θ
  have hVb : ∀ u, a - 1 ≤ u → u ≤ b + 1 → |rateVarN d s k β N u| ≤ D := by
    intro u h1 h2
    have hnn : 0 ≤ rateVarN d s k β N u := by
      unfold rateVarN
      exact integral_nonneg fun X => sq_nonneg _
    rw [abs_of_nonneg hnn]
    exact le_trans (hC N hN u ⟨h1, h2⟩) hDC
  have hYint : ∀ t : ℝ, Integrable (fun X : Fin N → Torus d => Real.exp (t * rateY d s k β N θ X))
      (rateGibbs d s k β θ N) := fun t =>
    q32d_Y_integrable gm hgm hgm_ae hβ hc hgc hN0 k θ t
  have hYneg : ∀ t : ℝ, Integrable (fun X : Fin N → Torus d => Real.exp (t * -rateY d s k β N θ X))
      (rateGibbs d s k β θ N) := fun t =>
    (hYint (-t)).congr (Filter.Eventually.of_forall fun X => by
      congr 1
      ring)
  have hYt : ∀ t : ℝ, |t| ≤ Real.sqrt N →
      ∫ X, Real.exp (t * rateY d s k β N θ X) ∂(rateGibbs d s k β θ N) ≤
        Real.exp (D * t ^ 2 / 2) := fun t ht =>
    q32d_mgf_bound hd hs hsd hβ k hk gm hgm hgm_ae hc hgc hN a b D hVb θ hθ.1 hθ.2 t ht
  have hxD : x ≤ 2 * Real.sqrt N → x / D ≤ Real.sqrt N := fun hx2 => by
    rw [div_le_iff₀ hDpos]
    nlinarith [Real.sqrt_nonneg (N : ℝ)]
  have hYpart : rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|} ≤
      ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) + ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) := by
    by_cases hx2 : x ≤ 2 * Real.sqrt N
    · have hpos := q32d_chernoff (rateGibbs d s k β θ N) (fun X => rateY d s k β N θ X)
        (fun t => hYint t) D hDpos x hx (fun t ht0 htx => hYt t (by
          rw [abs_of_nonneg ht0]
          exact le_trans htx (hxD hx2)))
      have hneg := q32d_chernoff (rateGibbs d s k β θ N) (fun X => -rateY d s k β N θ X)
        (fun t => hYneg t) D hDpos x hx (fun t ht0 htx => by
          beta_reduce
          have h := hYt (-t) (by
            rw [abs_neg, abs_of_nonneg ht0]
            exact le_trans htx (hxD hx2))
          simp only [neg_mul, mul_neg, neg_sq] at h ⊢
          exact h)
      calc rateGibbs d s k β θ N {X | x < |rateY d s k β N θ X|}
          ≤ rateGibbs d s k β θ N ({X | x < rateY d s k β N θ X} ∪
              {X | x < -rateY d s k β N θ X}) :=
            measure_mono (fun X (hX : x < |rateY d s k β N θ X|) =>
              (lt_abs.1 hX : x < rateY d s k β N θ X ∨ x < -rateY d s k β N θ X))
        _ ≤ _ := (measure_union_le _ _).trans (add_le_add hpos hneg)
    · have hempty : {X | x < |rateY d s k β N θ X|} = ∅ := by
        ext X
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        have h := q32d_rateY_abs_le gm hgm hgm_ae hβ hc hgc hN0 k θ X
        push_neg at hx2
        linarith
      rw [hempty, measure_empty]
      exact zero_le
  have hsusc := susceptibilityCov_cosMode_le_one hd hs hsd β hβ k hk ρ hρ θ
  have hvD : (((susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
      (Torus.cosMode k) (Torus.cosMode k)).toNNReal : NNReal) : ℝ) ≤ D := by
    rw [Real.coe_toNNReal']
    exact max_le (le_trans hsusc hD1) hDpos.le
  obtain ⟨g1, g2⟩ := q32d_gauss_tail _ D hDpos hvD x hx
  have hGpart : gaussianReal 0 (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
      (Torus.cosMode k) (Torus.cosMode k)).toNNReal {z | x < |z|} ≤
      ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) + ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) := by
    calc _ ≤ gaussianReal 0 (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
          (Torus.cosMode k) (Torus.cosMode k)).toNNReal
          ({z | x < z} ∪ {z | x < -z}) := measure_mono (fun z (hz : x < |z|) => (lt_abs.1 hz : x < z ∨ x < -z))
      _ ≤ _ := (measure_union_le _ _).trans (add_le_add g1 g2)
  calc _ ≤ (ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) + ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))))
        + (ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D))) + ENNReal.ofReal (Real.exp (-x ^ 2 / (2 * D)))) :=
        add_le_add hYpart hGpart
    _ = ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D))) :=
        q32d_four _ (Real.exp_pos _).le

end Rates

example := (@response_subGaussian_proof : type_of% @HRS.response_subGaussian)

end HRS

end
