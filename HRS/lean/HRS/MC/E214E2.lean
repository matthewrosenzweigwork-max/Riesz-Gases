import HRS.MC.E214E1

/-!
# E214E2: the entries of the joint covariance of the two noise convolutions

For the block density `blockDens m q ρ ρ'` evaluated on the pull-backs `inl2 u`, `inr2 v` (`u`, `v` the pull-back
vectors of the dual evolutions): the four entries are the integrands of `crossNoiseCov`
(`e214e_entry_ll`, `_lr`, `_rl`, `_rr`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214E

open HRS HRS.Sec7 HRS.Uniform HRS.Uniform.Q14 HRS.GF HRS.T25P HRS.AdjK HRS.MC.E213N HRS.MC.E214D

variable {d : ℕ}

theorem blockDens_inl_inl_eq (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {ρ' : ℝ → Torus d → ℝ}
    (hρ'c : ∀ σ : ℝ, 0 ≤ σ → Continuous (ρ' σ)) {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ}
    (hq : 0 ≤ q) (σ : ℝ) (u v : NegSobolev d m) :
    blockDens m q ρ ρ' σ (inl2 m u) (inl2 m v) = noiseDens m q ρ σ u v := by
  have := congrArg (fun B => B u v) (formComp_fst_blockDens hd htr hρ'c hm hq σ)
  simpa only [Kot.formComp_apply, adjoint_fstL] using this

theorem blockDens_inr_inr_eq (hd : 2 ≤ d) {ρ : ℝ → Torus d → ℝ}
    (hρc : ∀ σ : ℝ, 0 ≤ σ → Continuous (ρ σ)) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) (σ : ℝ) (u v : NegSobolev d m) :
    blockDens m q ρ ρ' σ (inr2 m u) (inr2 m v) = noiseDens m q ρ' σ u v := by
  have := congrArg (fun B => B u v) (formComp_snd_blockDens hd hρc htr' hm hq σ)
  simpa only [Kot.formComp_apply, adjoint_sndL] using this

theorem blockForm_symm {γ : ℝ} (hγ : (d : ℝ) / 2 + 2 < γ) {q : ℝ} {a b : Torus d → ℝ}
    (ha : Continuous a) (hb : Continuous b) (z w : H2 d γ) :
    blockForm γ q a b z w = blockForm γ q a b w z := by
  rw [blockForm_apply hγ ha hb, blockForm_apply hγ ha hb]
  exact Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)

theorem blockDens_symm (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (σ : ℝ) (z w : H2 d m) :
    blockDens m q ρ ρ' σ z w = blockDens m q ρ ρ' σ w z := by
  obtain ⟨h1, h2, h3⟩ := traj_facts hd htr
  obtain ⟨h1', h2', h3'⟩ := traj_facts hd htr'
  by_cases hσ : 0 ≤ σ
  · simp only [blockDens, if_pos hσ]
    exact blockForm_symm hm (h2 σ hσ) (h2' σ hσ) z w
  · simp [blockDens, hσ]

/-- Diagonal entry (first field). -/
theorem entry_ll (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {ρ' : ℝ → Torus d → ℝ}
    (hρ'c : ∀ σ : ℝ, 0 ≤ σ → Continuous (ρ' σ)) {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {T : ℝ} (hT : 0 < T)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    {K : ℝ} (hK : 0 ≤ K) (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖Vev t r‖ ≤ K)
    {q : ℝ} (hq : 0 ≤ q) {ta tb σ : ℝ} (hta : ta ∈ Icc 0 T) (htb : tb ∈ Icc 0 T)
    (hσ : σ ∈ Icc 0 (min ta tb)) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    blockDens m q ρ ρ' σ (inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) ta σ (gfb4_ell m φ)))
        (inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) tb σ (gfb4_ell m ψ))) =
      2 * q * ∫ x, inner ℝ (Torus.grad (propagator htr.dyn ρ σ ta φ) x)
        (Torus.grad (propagator htr.dyn ρ σ tb ψ) x) * Real.sqrt (ρ σ x * ρ σ x) := by
  have hσT : σ ∈ Icc 0 T := ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans hta.2)⟩
  rw [blockDens_inl_inl_eq hd htr hρ'c hm hq]
  have e : noiseDens m q ρ σ = covDensT m q T ρ σ := (HRS.MC.E213K.e213k_covDensT_eq m q T ρ hσT).symm
  rw [e, t25p_cov_eq hd htr hm hT hdual hK hKb hq hta htb hσ hφ hψ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [Real.sqrt_mul_self (((traj_facts hd htr).1 σ hσ.1).nonneg x)]

/-- Diagonal entry (second field). -/
theorem entry_rr (hd : 2 ≤ d) {ρ : ℝ → Torus d → ℝ}
    (hρc : ∀ σ : ℝ, 0 ≤ σ → Continuous (ρ σ)) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {T : ℝ} (hT : 0 < T)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr'.dyn ρ' m Vev)
    {K : ℝ} (hK : 0 ≤ K) (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ‖Vev t r‖ ≤ K)
    {q : ℝ} (hq : 0 ≤ q) {ta tb σ : ℝ} (hta : ta ∈ Icc 0 T) (htb : tb ∈ Icc 0 T)
    (hσ : σ ∈ Icc 0 (min ta tb)) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) :
    blockDens m q ρ ρ' σ (inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) ta σ (gfb4_ell m φ)))
        (inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) tb σ (gfb4_ell m ψ))) =
      2 * q * ∫ x, inner ℝ (Torus.grad (propagator htr'.dyn ρ' σ ta φ) x)
        (Torus.grad (propagator htr'.dyn ρ' σ tb ψ) x) * Real.sqrt (ρ' σ x * ρ' σ x) := by
  have hσT : σ ∈ Icc 0 T := ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans hta.2)⟩
  rw [blockDens_inr_inr_eq hd hρc htr' hm hq]
  have e : noiseDens m q ρ' σ = covDensT m q T ρ' σ := (HRS.MC.E213K.e213k_covDensT_eq m q T ρ' hσT).symm
  rw [e, t25p_cov_eq hd htr' hm hT hdual hK hKb hq hta htb hσ hφ hψ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [Real.sqrt_mul_self (((traj_facts hd htr').1 σ hσ.1).nonneg x)]

/-- Off-diagonal entry, transposed: `blockDens (inr2 u) (inl2 v)`. -/
theorem entry_rl (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m)
    {Vev Vev' : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution htr.dyn ρ m Vev) (hdual' : IsDualEvolution htr'.dyn ρ' m Vev')
    {K : ℝ} (hK : 0 ≤ K) {q : ℝ} (hq : 0 ≤ q) {ta tb σ : ℝ} (hσ : σ ∈ Icc 0 (min ta tb))
    (hKa : ‖Vev tb σ‖ ≤ K) (hKb : ‖Vev' ta σ‖ ≤ K) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) :
    blockDens m q ρ ρ' σ (inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev') ta σ (gfb4_ell m φ)))
        (inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) tb σ (gfb4_ell m ψ))) =
      2 * q * ∫ x, inner ℝ (Torus.grad (propagator htr'.dyn ρ' σ ta φ) x)
        (Torus.grad (propagator htr.dyn ρ σ tb ψ) x) * Real.sqrt (ρ' σ x * ρ σ x) := by
  rw [blockDens_symm hd htr htr' hm, e214d_cross_cov hd htr htr' hm hdual hdual' hK hq
    (by rwa [min_comm]) hKa hKb hψ hφ]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only []
  rw [real_inner_comm, mul_comm (ρ σ x)]

end HRS.MC.E214E

end
