import HRS.Uniform.Q12P7

/-!
# Q12, Peyre part 8: weak closeness against `C²` functions implies convergence against `C⁰`
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_C2b_exists {Φ : Euc d → ℝ} (hp : Torus.Per Φ) (hΦ : ContDiff ℝ 2 Φ) :
    ∃ B : ℝ, C2b B Φ := by
  have hΦ1 : ContDiff ℝ 1 (fderiv ℝ Φ) := hΦ.fderiv_right (by norm_num)
  have hper1 : Torus.Per (fun y => ‖fderiv ℝ Φ y‖) := fun y n => by
    show ‖fderiv ℝ Φ (y + Lattice.toEuc n)‖ = ‖fderiv ℝ Φ y‖
    rw [q12_per_fderiv hp]
  have hper1' : Torus.Per (fderiv ℝ Φ) := fun y n => q12_per_fderiv hp y n
  have hper2 : Torus.Per (fun y => ‖fderiv ℝ (fderiv ℝ Φ) y‖) := fun y n => by
    show ‖fderiv ℝ (fderiv ℝ Φ) (y + Lattice.toEuc n)‖ = ‖fderiv ℝ (fderiv ℝ Φ) y‖
    rw [q12_per_fderiv hper1']
  obtain ⟨B₀, h₀⟩ := Torus.Per.bound hp hΦ.continuous
  obtain ⟨B₁, h₁⟩ := Torus.Per.bound hper1 (hΦ.continuous_fderiv (by norm_num)).norm
  obtain ⟨B₂, h₂⟩ := Torus.Per.bound hper2 (hΦ1.continuous_fderiv one_ne_zero).norm
  refine ⟨max B₀ (max B₁ B₂), hΦ, fun y => ⟨?_, ?_, ?_⟩⟩
  · exact (h₀ y).trans (le_max_left _ _)
  · have := h₁ y
    exact (le_abs_self _).trans (this.trans ((le_max_left _ _).trans (le_max_right _ _)))
  · have := h₂ y
    exact (le_abs_self _).trans (this.trans ((le_max_right _ _).trans (le_max_right _ _)))

lemma q12_contDiff_dot (k : Lattice d) : ContDiff ℝ 2 fun y : Euc d => Lattice.dot k y := by
  unfold Lattice.dot
  exact ContDiff.sum fun i _ => contDiff_const.mul
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff)

lemma q12_contDiff_lift_mode (k : Lattice d) :
    ContDiff ℝ 2 fun y : Euc d => Torus.mode k (Torus.mk y) := by
  have e : (fun y : Euc d => Torus.mode k (Torus.mk y)) =
      fun y => Complex.exp (((2 * Real.pi * Lattice.dot k y : ℝ) : ℂ) * Complex.I) := by
    funext y; exact Torus.mode_mk k y
  rw [e]
  refine Complex.contDiff_exp.comp (ContDiff.mul ?_ contDiff_const)
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (q12_contDiff_dot k))

lemma q12_contDiff_span {p : C(Torus d, ℂ)}
    (hp : p ∈ Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d)))) :
    ContDiff ℝ 2 fun y : Euc d => p (Torus.mk y) := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact q12_contDiff_lift_mode k
  | zero => exact contDiff_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact contDiff_const.mul hx

/-- Continuous functions on the torus are uniformly approximated by `C²` functions. -/
lemma q12_approx_C2 (φ : Torus d → ℝ) (hφ : Continuous φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ : Torus d → ℝ, ContDiff ℝ 2 (fun y : Euc d => Ψ (Torus.mk y)) ∧ Continuous Ψ ∧
      ∀ x, |φ x - Ψ x| ≤ ε := by
  let f : C(Torus d, ℂ) := ⟨fun x => (φ x : ℂ), Complex.continuous_ofReal.comp hφ⟩
  have hf : f ∈ (Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d)))).topologicalClosure := by
    rw [UnitAddTorus.span_mFourier_closure_eq_top]; trivial
  have hf' : f ∈ closure ((Submodule.span ℂ (Set.range (UnitAddTorus.mFourier (d := Fin d))) :
      Submodule ℂ C(Torus d, ℂ)) : Set C(Torus d, ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hf
  obtain ⟨p, hp, hdist⟩ := Metric.mem_closure_iff.1 hf' ε hε
  have hdx := (ContinuousMap.dist_lt_iff hε).1 hdist
  refine ⟨fun x => (p x).re, ?_, ?_, fun x => ?_⟩
  · exact Complex.reCLM.contDiff.comp (q12_contDiff_span hp)
  · exact Complex.continuous_re.comp p.continuous
  · have := hdx x
    rw [Complex.dist_eq] at this
    have h2 : |φ x - (p x).re| = |((f x - p x).re)| := by
      simp [f]
    rw [h2]
    exact (Complex.abs_re_le_norm _).trans this.le

/-- Weak closeness against `C²` functions, with errors tending to `0`, gives convergence of
integrals of all continuous functions. -/
lemma q12_tendsto_of_weakClose {ν : ℕ → Measure (Torus d)} [∀ n, IsProbabilityMeasure (ν n)]
    {μ1 : Measure (Torus d)} [IsProbabilityMeasure μ1] {b : ℕ → ℝ} (hb : Tendsto b atTop (𝓝 0))
    (hw : ∀ n, WeakClose (ν n) μ1 (b n)) (φ : Torus d → ℝ) (hφ : Continuous φ) :
    Tendsto (fun n => ∫ x, φ x ∂(ν n)) atTop (𝓝 (∫ x, φ x ∂μ1)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨Ψ, hΨ2, hΨc, hΨ⟩ := q12_approx_C2 φ hφ (show 0 < ε / 4 by positivity)
  set Φ : Euc d → ℝ := fun y => Ψ (Torus.mk y) with hΦ
  have hΦp : Torus.Per Φ := fun y n => by
    show Ψ (Torus.mk (y + Lattice.toEuc n)) = Ψ (Torus.mk y)
    rw [Torus.mk_add, Torus.mk_toEuc, add_zero]
  obtain ⟨B, hB⟩ := q12_C2b_exists hΦp hΨ2
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB.2 0).1
  have hIw : ∀ (m : Measure (Torus d)), Iw m Φ = ∫ x, Ψ x ∂m := fun m => by
    unfold Iw
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show Ψ (Torus.mk (Torus.rep x)) = Ψ x
    rw [Torus.mk_rep]
  have hbB : Tendsto (fun n => b n * B) atTop (𝓝 0) := by simpa using hb.mul_const B
  rw [Metric.tendsto_atTop] at hbB
  obtain ⟨N, hN⟩ := hbB (ε / 4) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hint : ∀ (m : Measure (Torus d)) [IsProbabilityMeasure m] (f : Torus d → ℝ), Continuous f →
      Integrable f m := fun m _ f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hdiff : ∀ (m : Measure (Torus d)) [IsProbabilityMeasure m],
      |∫ x, φ x ∂m - ∫ x, Ψ x ∂m| ≤ ε / 4 := fun m _ => by
    rw [← integral_sub (hint m _ hφ) (hint m _ hΨc)]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε / 4) (Filter.Eventually.of_forall fun x => ?_)).trans ?_
    · rw [Real.norm_eq_abs]; exact hΨ x
    · simp
  have h1 := hdiff (ν n)
  have h2 := hdiff μ1
  have h3 := hw n Φ B hΦp hB
  rw [hIw, hIw] at h3
  have h4 := hN n hn
  rw [Real.dist_eq, sub_zero] at h4
  rw [Real.dist_eq]
  have h5 : |∫ x, φ x ∂(ν n) - ∫ x, φ x ∂μ1| ≤
      |∫ x, φ x ∂(ν n) - ∫ x, Ψ x ∂(ν n)| + |∫ x, Ψ x ∂(ν n) - ∫ x, Ψ x ∂μ1| +
        |∫ x, φ x ∂μ1 - ∫ x, Ψ x ∂μ1| := by
    have : ∫ x, φ x ∂(ν n) - ∫ x, φ x ∂μ1 =
        (∫ x, φ x ∂(ν n) - ∫ x, Ψ x ∂(ν n)) + (∫ x, Ψ x ∂(ν n) - ∫ x, Ψ x ∂μ1) -
          (∫ x, φ x ∂μ1 - ∫ x, Ψ x ∂μ1) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    gcongr
    exact abs_add_le _ _
  have : |∫ x, Ψ x ∂(ν n) - ∫ x, Ψ x ∂μ1| ≤ ε / 4 := h3.trans ((le_abs_self _).trans h4.le)
  linarith

end HRS.Uniform.Q12
