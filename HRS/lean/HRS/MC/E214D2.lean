import HRS.MC.E214D1
import HRS.MC.E213A
import HRS.MC.E213N2
import HRS.Main.T25PAux11

/-!
# E214D2: feasibility prototype of P1, part 2: the pair of noises, the cross covariance, the target statement

* `adjoint_fstL`, `adjoint_sndL`, `isHM_pair_fst/snd`: the two components of the block Gaussian martingale are
  `E_m`-valued Gaussian martingales with the covariation densities `noiseDens m q ρ`, `noiseDens m q ρ'` (the
  `mart` fields of `E213N.IsGlobalNoise` for the two single fields).
* `e214d_exists_pair_noise`: ONE continuous Gaussian Hilbert martingale on `E_m × E_m` with the block density.
* `e214d_cross_cov`: the off-diagonal entry of the block density evaluated on the pull-backs of two dual evolutions
  is the integrand of `crossNoiseCov`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214D

open HRS HRS.Uniform HRS.Uniform.Q14 HRS.Uniform.Q54c HRS.GF HRS.T25P HRS.AdjK HRS.MC.E213N

variable {d : ℕ}

/-! ### The component martingales -/

theorem adjoint_fstL (γ : ℝ) (x : NegSobolev d γ) :
    ContinuousLinearMap.adjoint (WithLp.fstL 2 ℝ (NegSobolev d γ) (NegSobolev d γ)) x = inl2 γ x := by
  refine ext_inner_right ℝ fun z => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [inl2, WithLp.prod_inner_apply]

theorem adjoint_sndL (γ : ℝ) (x : NegSobolev d γ) :
    ContinuousLinearMap.adjoint (WithLp.sndL 2 ℝ (NegSobolev d γ) (NegSobolev d γ)) x = inr2 γ x := by
  refine ext_inner_right ℝ fun z => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [inr2, WithLp.prod_inner_apply]

/-- Facts on a smooth positive trajectory used for the block density. -/
theorem traj_facts (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) :
    (∀ σ : ℝ, 0 ≤ σ → IsProbDensity (ρ σ)) ∧ (∀ σ : ℝ, 0 ≤ σ → Continuous (ρ σ)) ∧
      Measurable fun p : ℝ × Torus d => if 0 ≤ p.1 then ρ p.1 p.2 else 0 := by
  have hd1 : 1 ≤ d := by omega
  have hprob : ∀ σ : ℝ, 0 ≤ σ → IsProbDensity (ρ σ) := fun σ hσ =>
    (HRS.Q40b.q40b_meanField hd1 htr (T := σ + 1) (by linarith)).density σ ⟨hσ, by linarith⟩
  have hjc : ∀ T : ℝ, ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) :=
    fun T => HRS.Q40b.q40b_jointCont hd1 htr T
  refine ⟨hprob, fun σ hσ => ?_, ?_⟩
  · have := (hjc (σ + 1)).comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨⟨hσ, by linarith⟩, Set.mem_univ _⟩)
    exact this
  · have hcont : ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Ici 0 ×ˢ Set.univ) := by
      intro p hp
      obtain ⟨n, hn⟩ := exists_nat_gt p.1
      have hmem : Set.Icc (0 : ℝ) n ×ˢ (Set.univ : Set (Torus d)) ∈ nhdsWithin p (Set.Ici 0 ×ˢ Set.univ) := by
        have h1 : Set.Iic (n : ℝ) ×ˢ (Set.univ : Set (Torus d)) ∈ nhds p := by
          refine prod_mem_nhds (Iic_mem_nhds hn) Filter.univ_mem
        have h2 : Set.Icc (0 : ℝ) n ×ˢ (Set.univ : Set (Torus d)) =
            (Set.Ici 0 ×ˢ Set.univ) ∩ (Set.Iic (n : ℝ) ×ˢ Set.univ) := by
          ext q
          simp only [Set.mem_prod, Set.mem_Icc, Set.mem_Ici, Set.mem_Iic, Set.mem_inter_iff, Set.mem_univ, and_true]
        rw [h2]
        exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds h1)
      exact (hjc n p ⟨⟨hp.1, hn.le⟩, Set.mem_univ _⟩).mono_of_mem_nhdsWithin hmem
    have hpw : (fun p : ℝ × Torus d => if 0 ≤ p.1 then ρ p.1 p.2 else 0) =
        (Set.Ici 0 ×ˢ (Set.univ : Set (Torus d))).piecewise (fun p => ρ p.1 p.2) (fun _ => 0) := by
      funext p
      by_cases h : 0 ≤ p.1 <;> simp [Set.piecewise, h]
    rw [hpw]
    exact ContinuousOn.measurable_piecewise hcont continuousOn_const
      (measurableSet_Ici.prod MeasurableSet.univ)

/-- ONE continuous Gaussian Hilbert martingale on `E_m × E_m` whose covariation on every window is the block
density of two smooth positive trajectories. -/
theorem e214d_exists_pair_noise (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ℱ : Filtration ℝ mΩ) (G : ℝ → Ω → H2 d m),
      (∀ ω, Continuous fun τ => G τ ω) ∧ (∀ ω, G 0 ω = 0) ∧
      ∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S G (fun r _ => blockDens m q ρ ρ' r) := by
  obtain ⟨h1, h2, h3⟩ := traj_facts hd htr
  obtain ⟨h1', h2', h3'⟩ := traj_facts hd htr'
  exact HRS.MC.E213K.exists_gaussian_martingale_top (H := H2 d m) (blockDens m q ρ ρ')
    (isDetCovDensity_blockDens hm hq h1 h2 h1' h2' h3 h3')

/-- The first component of the block density is the single-field noise density of `ρ`. -/
theorem formComp_fst_blockDens (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {ρ' : ℝ → Torus d → ℝ}
    (hρ'c : ∀ σ : ℝ, 0 ≤ σ → Continuous (ρ' σ)) {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ}
    (hq : 0 ≤ q) (r : ℝ) :
    Kot.formComp (ContinuousLinearMap.adjoint (WithLp.fstL 2 ℝ (NegSobolev d m) (NegSobolev d m)))
      (blockDens m q ρ ρ' r) = noiseDens m q ρ r := by
  obtain ⟨h1, h2, h3⟩ := traj_facts hd htr
  refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
  simp only [Kot.formComp_apply, adjoint_fstL, blockDens, noiseDens]
  by_cases hr : 0 ≤ r
  · simp only [if_pos hr]
    exact blockForm_inl_inl hm hq (h2 r hr) (h1 r hr).nonneg (hρ'c r hr) x y
  · simp [hr]

/-- The second component of the block density is the single-field noise density of `ρ'`. -/
theorem formComp_snd_blockDens (hd : 2 ≤ d) {ρ : ℝ → Torus d → ℝ}
    (hρc : ∀ σ : ℝ, 0 ≤ σ → Continuous (ρ σ)) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) (r : ℝ) :
    Kot.formComp (ContinuousLinearMap.adjoint (WithLp.sndL 2 ℝ (NegSobolev d m) (NegSobolev d m)))
      (blockDens m q ρ ρ' r) = noiseDens m q ρ' r := by
  obtain ⟨h1, h2, h3⟩ := traj_facts hd htr'
  refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
  simp only [Kot.formComp_apply, adjoint_sndL, blockDens, noiseDens]
  by_cases hr : 0 ≤ r
  · simp only [if_pos hr]
    exact blockForm_inr_inr hm hq (hρc r hr) (h2 r hr) (h1 r hr).nonneg x y
  · simp [hr]

/-- The two components of the block martingale are Gaussian martingales of the two single fields
(driven by the same noise): the `mart` fields of `IsGlobalNoise` for `ρ` and `ρ'`. -/
theorem e214d_pair_components (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {q : ℝ} (hq : 0 ≤ q) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ℱ : Filtration ℝ mΩ) (G : ℝ → Ω → H2 d m),
      (∀ ω, Continuous fun τ => G τ ω) ∧ (∀ ω, G 0 ω = 0) ∧
      (∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S G (fun r _ => blockDens m q ρ ρ' r)) ∧
      (∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => (G τ ω).fst)
        (fun r _ => noiseDens m q ρ r)) ∧
      (∀ S : ℝ, 0 ≤ S → IsHilbertMartingaleWithCovariation P ℱ S (fun τ ω => (G τ ω).snd)
        (fun r _ => noiseDens m q ρ' r)) := by
  obtain ⟨Ω, mΩ, P, hP, ℱ, G, hc, hz, hG⟩ := e214d_exists_pair_noise hd htr htr' hm hq
  obtain ⟨h1, h2, h3⟩ := traj_facts hd htr
  obtain ⟨h1', h2', h3'⟩ := traj_facts hd htr'
  have hdet := isDetCovDensity_blockDens hm hq h1 h2 h1' h2' h3 h3'
  refine ⟨Ω, mΩ, P, hP, ℱ, G, hc, hz, hG, fun S hS => ?_, fun S hS => ?_⟩
  · have := isHM_map_clm (hdet S hS) (hG S hS) (WithLp.fstL 2 ℝ (NegSobolev d m) (NegSobolev d m))
    simp only [formComp_fst_blockDens hd htr h2' hm hq] at this
    exact this
  · have := isHM_map_clm (hdet S hS) (hG S hS) (WithLp.sndL 2 ℝ (NegSobolev d m) (NegSobolev d m))
    simp only [formComp_snd_blockDens hd h2 htr' hm hq] at this
    exact this

/-! ### The cross covariance -/

/-- The off-diagonal entry of the block density, on the pull-backs of two dual evolutions along the two
trajectories, is the integrand of `crossNoiseCov`:
`2q ∫ ∇U^{σ,ta}φ · ∇Ū^{σ,tb}ψ √(ρ^σ ρ'^σ) dx`. -/
theorem e214d_cross_cov (hd : 2 ≤ d) {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {s' β' : ℝ} {V' ρ₀' : Torus d → ℝ}
    {ρ' : ℝ → Torus d → ℝ} (htr' : IsSmoothPositiveTrajectory d s' β' V' ρ₀' ρ') {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m)
    {Vev Vev' : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution htr.dyn ρ m Vev) (hdual' : IsDualEvolution htr'.dyn ρ' m Vev')
    {K : ℝ} (hK : 0 ≤ K) {q : ℝ} (hq : 0 ≤ q) {ta tb σ : ℝ} (hσ : σ ∈ Set.Icc 0 (min ta tb))
    (hKa : ‖Vev ta σ‖ ≤ K) (hKb : ‖Vev' tb σ‖ ≤ K) {φ ψ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (hψ : Torus.IsSmooth ψ) :
    blockDens m q ρ ρ' σ
        (inl2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev) ta σ (gfb4_ell m φ)))
        (inr2 m (pullbackVec (HRS.Uniform.Comp28.plainData Vev') tb σ (gfb4_ell m ψ))) =
      2 * q * ∫ x, inner ℝ (Torus.grad (propagator htr.dyn ρ σ ta φ) x)
        (Torus.grad (propagator htr'.dyn ρ' σ tb ψ) x) * Real.sqrt (ρ σ x * ρ' σ x) := by
  obtain ⟨h1, h2, h3⟩ := traj_facts hd htr
  obtain ⟨h1', h2', h3'⟩ := traj_facts hd htr'
  have hσ0 : 0 ≤ σ := hσ.1
  have hσa : σ ≤ ta := hσ.2.trans (min_le_left _ _)
  have hσb : σ ≤ tb := hσ.2.trans (min_le_right _ _)
  simp only [blockDens, if_pos hσ0]
  rw [t25p_pullback_eq_lpFun hd htr hdual hK hσ0 hσa hKa hφ,
    t25p_pullback_eq_lpFun hd htr' hdual' hK hσ0 hσb hKb hψ,
    blockForm_inl_inr hm hq (h2 σ hσ0) (h1 σ hσ0).nonneg (h2' σ hσ0) (h1' σ hσ0).nonneg]
  have hk : Continuous fun t => Real.sqrt (ρ σ t * ρ' σ t) := ((h2 σ hσ0).mul (h2' σ hσ0)).sqrt
  have hprop : ∀ {s₁ β₁ : ℝ} {V₁ ρ₀₁ : Torus d → ℝ} {ρ₁ : ℝ → Torus d → ℝ}
      (htr₁ : IsSmoothPositiveTrajectory d s₁ β₁ V₁ ρ₀₁ ρ₁)
      {Vev₁ : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual₁ : IsDualEvolution htr₁.dyn ρ₁ m Vev₁)
      {t₁ : ℝ} (hσt : σ ≤ t₁) (hK₁ : ‖Vev₁ t₁ σ‖ ≤ K) {φ₁ : Torus d → ℝ} (hφ₁ : Torus.IsSmooth φ₁),
      MemSobolev m (propagator htr₁.dyn ρ₁ σ t₁ φ₁) ∧ Continuous (propagator htr₁.dyn ρ₁ σ t₁ φ₁) ∧
        Torus.IsCk 1 (propagator htr₁.dyn ρ₁ σ t₁ φ₁) := by
    intro s₁ β₁ V₁ ρ₀₁ ρ₁ htr₁ Vev₁ hdual₁ t₁ hσt hK₁ φ₁ hφ₁
    have hck := adjkd_propagator_ck2 htr₁.dyn ρ₁ hσ0 hσt φ₁
    exact ⟨t25p_memSobolev_propagator hd htr₁ hdual₁ hK hσ0 hσt hK₁ hφ₁,
      Torus.continuous_of_continuous_lift hck.continuous, ContDiff.of_le hck (by norm_num)⟩
  obtain ⟨ha1, ha2, ha3⟩ := hprop htr hdual hσa hKa hφ
  obtain ⟨hb1, hb2, hb3⟩ := hprop htr' hdual' hσb hKb hψ
  exact covForm_lpFun hm hq hk (fun x => Real.sqrt_nonneg _) ha1 ha2 ha3 hb1 hb2 hb3

end HRS.MC.E214D

end
