import HRS.Sections.Sec5
import HRS.Stochastic.DualityProof
import HRS.Equilibrium.QuadraticVariance
import HRS.Energy.Commutator.AbsConv
import HRS.Energy.PressureProof

/-!
# Packet Q40b, part 3: the commutator forcing

* `q40b_fluc_eq_neg`: for `M = -I`, `flucInteraction D ψ X ρ = -F_N^{h_{∇ψ}}(X, ρ)`
  (`modulatedEnergy` of `commKernel`), for every configuration (Lemma 3.1 pointwise form);
* `q40b_grad_lip`, `q40b_unif_D2`: Lipschitz constant of `∇U^{r,t}φ`, uniform in `r ∈ [0,t]`;
* `q40b_hdom`: `|commKernel| ≤ A L (periodicRiesz + c*)` for an `L`-Lipschitz field;
* `q40b_forcing_L1`: Proposition 5.5 (`perturbed_pressure`) applied to `h = commKernel`:
  `E_ν[N |F_N^h|] ≤ C (H(ν|Q) + Nδ_N)`, uniform over the smooth positive background family.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ} {s : ℝ}



theorem q40b_modEnergy_neg (h : Torus d → Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) :
    modulatedEnergy (fun x y => -h x y) X μ = -modulatedEnergy h X μ := by
  unfold modulatedEnergy
  simp only [Finset.sum_neg_distrib, integral_neg, mul_neg, neg_sub_left]
  ring

theorem q40b_interKernel_self (D : DynData d) (ψ : Torus d → ℝ) (x : Torus d) :
    interKernel D ψ x x = 0 := by simp [interKernel]

theorem q40b_fluc_eq_modEnergy (hd : 1 ≤ d) {D : DynData d} {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {B : ℝ} (hB : ∀ x, ρ x ≤ B)
    (hN : 0 < N) (X : Config d N) :
    flucInteraction D ψ X ρ = modulatedEnergy (interKernel D ψ) X (withDensityReal ρ) := by
  have hNn : (N : ℝ) ≠ 0 := by positivity
  have h1 := interactionPairing_empirical (D := D) (ψ := ψ) hN X
  have h2 : interactionPairing D ψ (empirical X) (withDensityReal ρ) =
      (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, ∫ y, interKernel D ψ (X i) y ∂(withDensityReal ρ)) := by
    show (1 / 2 : ℝ) * ∫ x, ∫ y, interKernel D ψ x y ∂(withDensityReal ρ) ∂(empirical X) = _
    congr 1
    exact pair_empirical hN X (fun x => ∫ y, interKernel D ψ x y ∂(withDensityReal ρ))
  have h3 : interactionPairing D ψ (withDensityReal ρ) (empirical X) =
      (1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, ∫ y, interKernel D ψ (X i) y ∂(withDensityReal ρ)) := by
    show (1 / 2 : ℝ) * ∫ x, ∫ y, interKernel D ψ x y ∂(empirical X) ∂(withDensityReal ρ) = _
    congr 1
    have e1 : ∀ x, ∫ y, interKernel D ψ x y ∂(empirical X) = (N : ℝ)⁻¹ * ∑ j, interKernel D ψ x (X j) :=
      fun x => pair_empirical hN X (fun y => interKernel D ψ x y)
    simp_rw [e1]
    have hint : ∀ j, Integrable (fun x => interKernel D ψ x (X j)) (withDensityReal ρ) := fun j =>
      (integrable_interKernel hd hψ hB (X j)).congr
        (Filter.Eventually.of_forall fun x => (interKernel_symm D ψ (X j) x).symm)
    rw [integral_const_mul, integral_finset_sum Finset.univ (fun j _ => hint j)]
    have hs : ∑ j, ∫ x, interKernel D ψ x (X j) ∂(withDensityReal ρ) =
        ∑ i, ∫ y, interKernel D ψ (X i) y ∂(withDensityReal ρ) :=
      Finset.sum_congr rfl fun j _ =>
        integral_congr_ae (Filter.Eventually.of_forall fun x => interKernel_symm D ψ (X j) x)
    rw [hs]
  have h4 : interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ) =
      (1 / 2 : ℝ) * ∫ x, ∫ y, interKernel D ψ x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) := rfl
  unfold flucInteraction modulatedEnergy
  rw [h1, h2, h3, h4]
  have hdiag : ∀ i : Fin N, ∑ j, interKernel D ψ (X i) (X j) =
      ∑ j ∈ Finset.univ.erase i, interKernel D ψ (X i) (X j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), q40b_interKernel_self, zero_add]
  simp_rw [hdiag]
  rw [← Finset.mul_sum]
  field_simp
  ring


theorem q40b_interKernel_eq_neg (D : DynData d) (hM : D.M = -1) (ψ : Torus d → ℝ) :
    interKernel D ψ = fun x y => -commKernel (periodicRieszGrad d D.s) (Torus.grad ψ) x y := by
  funext x y
  unfold interKernel commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, if_false, hM, PDE.MFAux.matVec_negOne, inner_neg_right]

theorem q40b_fluc_eq_neg (hd : 1 ≤ d) {D : DynData d} (hM : D.M = -1) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {B : ℝ} (hB : ∀ x, ρ x ≤ B)
    (hN : 0 < N) (X : Config d N) :
    flucInteraction D ψ X ρ =
      -modulatedEnergy (commKernel (periodicRieszGrad d D.s) (Torus.grad ψ)) X (withDensityReal ρ) := by
  rw [q40b_fluc_eq_modEnergy hd hψ hρ hB hN X, q40b_interKernel_eq_neg D hM ψ, q40b_modEnergy_neg]




theorem q40b_grad_lip {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) {M : ℝ}
    (hM : ∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift f) y‖ ≤ M) :
    IsLipschitzVF M (Torus.grad f) := by
  intro x y
  have hf1 : Torus.IsCk 1 f := PDE.ClassicalAux.isCk_of_le (by exact_mod_cast (by norm_num : (1 : ℕ) ≤ 2)) hf
  have hlift : ContDiff ℝ 2 (Torus.lift f) := hf
  set z : Euc d := KernelGrad.centeredRep (x - y) with hz
  set Y' : Euc d := Torus.rep y with hY'
  set X' : Euc d := Y' + z with hX'
  have hmkY : Torus.mk Y' = y := Torus.mk_rep y
  have hmkX : Torus.mk X' = x := by
    rw [hX', Torus.mk_add, hmkY, hz, KernelGrad.mk_centeredRep]; abel
  have hnorm : ‖X' - Y'‖ = KernelGrad.tdist x y := by
    rw [hX']; simp [hz, KernelGrad.tdist]
  have h1 : ∀ w : Euc d, DifferentiableAt ℝ (fderiv ℝ (Torus.lift f)) w := fun w =>
    (hlift.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) w
  have h2 : ∀ w ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (fderiv ℝ (Torus.lift f)) w‖ ≤ M := by
    intro w _
    have := hM w
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Torus.lift f) (x := w) (n := 1),
      norm_iteratedFDeriv_one] at this
    exact this
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ (Torus.lift f))
    (s := Set.univ) (fun w _ => h1 w) h2 convex_univ (Set.mem_univ Y') (Set.mem_univ X')
  have hgx : Torus.grad f x = gradient (Torus.lift f) X' := by
    rw [← hmkX]; exact Torus.grad_mk f hf1 X'
  have hgy : Torus.grad f y = gradient (Torus.lift f) Y' := by
    rw [← hmkY]; exact Torus.grad_mk f hf1 Y'
  rw [hgx, hgy]
  unfold gradient
  rw [← map_sub, LinearIsometryEquiv.norm_map]
  rw [← hnorm]
  exact hmv


theorem q40b_norm_rep_le (x : Torus d) : ‖Torus.rep x‖ ≤ d := by
  have h01 : ∀ i, 0 ≤ Torus.rep x i ∧ Torus.rep x i ≤ 1 := by
    intro i
    have := (AddCircle.equivIco (1 : ℝ) 0 (x i)).2
    simp only [Torus.rep]
    exact ⟨by simpa using this.1, by have := this.2; simp at this; linarith⟩
  have hsq : ‖Torus.rep x‖ ^ 2 ≤ d := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖Torus.rep x i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs, sq_abs]
          have := h01 i
          nlinarith
      _ = d := by simp
  by_cases hd : d = 0
  · subst hd
    have : ‖Torus.rep x‖ ^ 2 ≤ 0 := by simpa using hsq
    have h0 : ‖Torus.rep x‖ = 0 := by nlinarith [norm_nonneg (Torus.rep x)]
    simp [h0]
  · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd
    nlinarith [norm_nonneg (Torus.rep x)]

/-- A classical adjoint solution has uniformly bounded second derivatives on `[0,t]`. -/
theorem q40b_unif_D2 {D : DynData d} {ρ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {F : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution D ρ t φ F) :
    ∃ M : ℝ, ∀ r ∈ Set.Icc 0 t, ∀ y : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift (F r)) y‖ ≤ M := by
  have hc := hF.cont_c2 2 le_rfl
  have hcn : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d =>
      ‖iteratedFDeriv ℝ 2 (Torus.lift (F p.1)) p.2‖ := hc.norm
  have hK : IsCompact ((Set.univ : Set (Set.Icc (0 : ℝ) t)) ×ˢ Metric.closedBall (0 : Euc d) (d : ℝ)) :=
    isCompact_univ.prod (isCompact_closedBall _ _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcn.continuousOn
  refine ⟨M, fun r hr y => ?_⟩
  obtain ⟨n, hn⟩ := Torus.rep_mk y
  have e : iteratedFDeriv ℝ 2 (Torus.lift (F r)) (Torus.rep (Torus.mk y)) =
      iteratedFDeriv ℝ 2 (Torus.lift (F r)) y := by
    rw [hn]; exact Torus.iteratedFDeriv_lift_periodic (F r) 2 y n
  have hmem : ((⟨r, hr⟩ : Set.Icc (0 : ℝ) t), Torus.rep (Torus.mk y)) ∈
      (Set.univ : Set (Set.Icc (0 : ℝ) t)) ×ˢ Metric.closedBall (0 : Euc d) (d : ℝ) := by
    refine ⟨Set.mem_univ _, ?_⟩
    rw [mem_closedBall_zero_iff]; exact q40b_norm_rep_le _
  have := hM _ hmem
  simp only [Real.norm_eq_abs, abs_norm] at this
  rw [e] at this
  exact this





theorem q40b_tdist_eq_eucDist (x y : Torus d) : KernelGrad.tdist x y = Torus.eucDist (x - y) 0 := by
  obtain ⟨w, hw, hw'⟩ := KernelGrad.exists_mk_box (x - y)
  rw [KernelGrad.tdist_eq_sub_zero, ← hw, KernelGrad.tdist_mk hw', PairCorrAux.eucDist_mk_zero' hw']

theorem q40b_hdom (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ cstar A : ℝ, 0 ≤ A ∧ (∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cstar) ∧
      0 ≤ periodicRiesz d s 0 + cstar ∧
      ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L → IsLipschitzVF L v → ∀ x y : Torus d,
        |commKernel (periodicRieszGrad d s) v x y| ≤ (A * L) * (periodicRiesz d s (x - y) + cstar) := by
  obtain ⟨C₀, hC₀, hC⟩ := Commutator.commKernel_bound (d := d) (s := s) (by omega) hs0 hsd
  obtain ⟨Bg, hBg⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0 hsd
  obtain ⟨Cenv, hCenv⟩ := Quad.periodicRiesz_lower_env (d := d) (s := s) hd hs0 hsd
  set cstar : ℝ := max (Bg + 1) (max Cenv |periodicRiesz d s 0|) with hcstar
  have hc1 : Bg + 1 ≤ cstar := le_max_left _ _
  have hc2 : Cenv ≤ cstar := (le_max_left _ _).trans (le_max_right _ _)
  have hc3 : |periodicRiesz d s 0| ≤ cstar := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨cstar, 2 * C₀, by positivity, fun z _ => by linarith [hBg z], ?_, ?_⟩
  · have := neg_abs_le (periodicRiesz d s 0); linarith
  · intro L v hL hv x y
    by_cases hxy : x = y
    · subst hxy
      simp only [commKernel, if_true, abs_zero]
      have h0 : 0 ≤ periodicRiesz d s (x - x) + cstar := by
        rw [sub_self]; have := neg_abs_le (periodicRiesz d s 0); linarith
      positivity
    · have h1 := hC L v hL hv x y hxy
      have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
      have h2 := hCenv (x - y) hz
      have h3 : KernelGrad.tdist x y ^ (-s) + 1 ≤ 2 * Quad.envT s (x - y) := by
        have hone := Quad.one_le_envT (d := d) (s := s) (x - y)
        by_cases hs : s = 0
        · subst hs
          simp only [neg_zero, Real.rpow_zero]
          linarith
        · have hE : Quad.envT s (x - y) = Torus.eucDist (x - y) 0 ^ (-s) + 1 := by
            unfold Quad.envT singEnvelope
            simp only [hs, if_false]; ring
          rw [q40b_tdist_eq_eucDist, hE]
          rw [hE] at hone
          linarith
      calc |commKernel (periodicRieszGrad d s) v x y|
          ≤ C₀ * L * (KernelGrad.tdist x y ^ (-s) + 1) := h1
        _ ≤ C₀ * L * (2 * Quad.envT s (x - y)) := by gcongr
        _ ≤ C₀ * L * (2 * (periodicRiesz d s (x - y) + cstar)) := by
          gcongr
          linarith
        _ = (2 * C₀ * L) * (periodicRiesz d s (x - y) + cstar) := by ring


theorem q40b_commKernel_symm (hsd : s < d) (v : Torus d → Euc d) (x y : Torus d) :
    commKernel (periodicRieszGrad d s) v y x = commKernel (periodicRieszGrad d s) v x y := by
  unfold commKernel
  by_cases hxy : x = y
  · subst hxy; simp
  · have hyx : y ≠ x := Ne.symm hxy
    simp only [hxy, hyx, if_false]
    have : y - x = -(x - y) := by abel
    rw [this, KernelGrad.periodicRieszGrad_neg_of_lt hsd, inner_neg_right, ← inner_neg_left, neg_sub]

theorem q40b_commKernel_meas (hsd : s < d) {v : Torus d → Euc d} (hv : Continuous v) :
    Measurable (Function.uncurry fun x y : Torus d => commKernel (periodicRieszGrad d s) v x y) := by
  unfold commKernel
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  refine Measurable.inner ?_ ?_
  · exact (hv.measurable.comp measurable_fst).sub (hv.measurable.comp measurable_snd)
  · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd)

theorem q40b_forcing_L1 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {c₀ : ℝ} (hc₀ : 0 < c₀) (Λ : ℕ → ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsSmooth ρ → (∀ x, c₀ ≤ ρ x) →
      (∀ k : ℕ, Torus.cbNorm k ρ ≤ Λ k) → ∀ v : Torus d → Euc d, IsLipschitzVF L v →
      ∀ N : ℕ, 2 ≤ N → ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
        relEntropy ν (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) < ⊤ →
        ∫⁻ X, ENNReal.ofReal (N * |modulatedEnergy (commKernel (periodicRieszGrad d s) v) X
            (withDensityReal ρ)|) ∂ν ≤
          ENNReal.ofReal C * (relEntropy ν (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) +
            ENNReal.ofReal (N * deltaN d s N)) := by
  obtain ⟨cstar, A, hA, hw, h0, hdom⟩ := q40b_hdom hd hs0 hsd
  obtain ⟨θ₀, θ₁, C, hθ₀, hθ₁, H⟩ := perturbed_pressure (by omega) s hs0 hsd cstar hw β β hβ c₀ hc₀ Λ
    (A * L)
  refine ⟨C, fun ρ hρ hρs hρl hρΛ v hv N hN ν hν hKL => ?_⟩
  have hvc : Continuous v := Commutator.IsLipschitzVF.continuous hL hv
  have := (H ρ hρ hρs hρl hρΛ (commKernel (periodicRieszGrad d s) v)
    (q40b_commKernel_meas hsd hvc) (fun x y => (q40b_commKernel_symm hsd v x y).symm)
    (fun x y => hdom L v hL hv x y) N hN β ⟨le_rfl, le_rfl⟩).2.2 ν hν hKL
  exact this


end HRS.Q40b
