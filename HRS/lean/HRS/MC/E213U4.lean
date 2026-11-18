import HRS.MC.E213Defs
import HRS.MC.E213R5
import HRS.MD.EQGaussWindow
import HRS.Main.A33Aux2
import HRS.MC.E213N3
import HRS.MC.E213H
import HRS.MC.S7UCZ2

/-!
# Packet e213u4 (Theorem 2.13, Wave 1 W1-D): future Gaussians and canonical Gaussian data

* `exists_futureGaussians_proof` (from `E213R.e213r_exists_future`),
* `isFutureGaussian_unique_proof` (centred Gaussians determined by their covariance on point evaluations),
* `exists_gaussData_proof`, `wick_unique_proof`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U4

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ}

section FutureGaussians

variable {S : PreparedData d} {β₀ m : ℝ}

theorem exists_futureGaussians_proof (hE : EdgeworthHyp S β₀ m) (H : ℝ) (hH : 0 < H) :
    ∃ γ : ℝ → Measure (PathSpace d m H), ∀ u ∈ Set.Icc (0 : ℝ) H,
      IsFutureGaussian (regime S β₀ hE).D (regime S β₀ hE).ρ m H u (γ u) ∧ IsProbabilityMeasure (γ u) := by
  obtain ⟨γ, hγ⟩ := HRS.MC.E213R.e213r_exists_future (regime S β₀ hE) m hE.m_gt H hH
  refine ⟨γ, fun u hu => ⟨hγ u hu, ?_⟩⟩
  have := (hγ u hu).1.1
  infer_instance

end FutureGaussians

section GaussUnique

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- Two centred Gaussian measures with the same second moments of the coordinates of a continuous linear map
`L : E → ℝ^p` have the same push-forward under `L`. -/
theorem u4_map_eq_of_cov {p : ℕ} {γ₁ γ₂ : Measure E} (h₁ : IsCenteredGaussian γ₁) (h₂ : IsCenteredGaussian γ₂)
    (L : E →L[ℝ] EuclideanSpace ℝ (Fin p))
    (hcov : ∀ i j, ∫ z, L z i * L z j ∂γ₁ = ∫ z, L z i * L z j ∂γ₂) :
    γ₁.map L = γ₂.map L := by
  have := h₁.1
  have := h₂.1
  have key : ∀ (γ : Measure E), IsCenteredGaussian γ → ∀ L1 L2 : StrongDual ℝ (EuclideanSpace ℝ (Fin p)),
      covarianceBilinDual (γ.map L) L1 L2 = ∑ i, ∑ j, L1 (EuclideanSpace.single i 1) * L2 (EuclideanSpace.single j 1) *
        ∫ z, L z i * L z j ∂γ := by
    intro γ hγ L1 L2
    have := hγ.1
    have hLm : Measurable L := L.continuous.measurable
    have hmean : ∀ L1 : StrongDual ℝ (EuclideanSpace ℝ (Fin p)), (γ.map L)[L1] = 0 := by
      intro L1
      rw [integral_map hLm.aemeasurable L1.continuous.aestronglyMeasurable]
      exact hγ.2 (L1.comp L)
    rw [covarianceBilinDual_apply IsGaussian.memLp_two_id, hmean L1, hmean L2]
    simp only [sub_zero]
    rw [integral_map hLm.aemeasurable (by fun_prop)]
    have hrep : ∀ (L1 : StrongDual ℝ (EuclideanSpace ℝ (Fin p))) (z : E),
        L1 (L z) = ∑ i, L z i * L1 (EuclideanSpace.single i 1) := by
      intro L1 z
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin p) ℝ).sum_repr (L z)]
      simp [map_sum, map_smul, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
    have hint : ∀ i j, Integrable (fun z => L z i * L z j) γ := by
      intro i j
      have hi := IsGaussian.memLp_dual γ ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp L) 2
        (by simp)
      have hj := IsGaussian.memLp_dual γ ((EuclideanSpace.proj j : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp L) 2
        (by simp)
      exact hi.integrable_mul hj
    have hint' : ∀ (c : ℝ) i j, Integrable (fun z => c * (L z i * L z j)) γ := fun c i j =>
      (hint i j).const_mul c
    simp_rw [hrep]
    simp_rw [Finset.sum_mul_sum]
    have e1 : ∀ i j, ∫ z, L z i * L1 (EuclideanSpace.single i 1) * (L z j * L2 (EuclideanSpace.single j 1)) ∂γ =
        L1 (EuclideanSpace.single i 1) * L2 (EuclideanSpace.single j 1) * ∫ z, L z i * L z j ∂γ := by
      intro i j
      rw [← integral_const_mul]
      congr 1
      funext z
      ring
    have e2 : ∀ i j, Integrable (fun z => L z i * L1 (EuclideanSpace.single i 1) *
        (L z j * L2 (EuclideanSpace.single j 1))) γ := by
      intro i j
      refine (hint' (L1 (EuclideanSpace.single i 1) * L2 (EuclideanSpace.single j 1)) i j).congr
        (Eventually.of_forall fun z => ?_)
      simp only
      ring
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => e2 i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => e2 i j)]
    exact Finset.sum_congr rfl fun j _ => e1 i j
  have : IsGaussian (γ₁.map L) := inferInstance
  have : IsGaussian (γ₂.map L) := inferInstance
  have hmean : ∀ (γ : Measure E), IsCenteredGaussian γ → (γ.map L)[id] = 0 := by
    intro γ hγ
    have := hγ.1
    have hLm : Measurable L := L.continuous.measurable
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun L1 => ?_
    have := IsGaussian.integral_dual (μ := γ.map L) L1
    have h0 : (γ.map L)[L1] = 0 := by
      rw [integral_map hLm.aemeasurable L1.continuous.aestronglyMeasurable]
      exact hγ.2 (L1.comp L)
    rw [h0] at this
    simpa using this.symm
  refine IsGaussian.ext_covarianceBilinDual ((hmean γ₁ h₁).trans (hmean γ₂ h₂).symm) ?_
  ext L1 L2
  rw [key γ₁ h₁, key γ₂ h₂]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hcov i j]

end GaussUnique

section FutureUnique

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u4_pathAt_coe {m T : ℝ} (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) :
    pathAt w (t : ℝ) = PathSpace.at' w t := by
  unfold pathAt
  rw [dif_pos t.2]

theorem isFutureGaussian_unique_proof (hE : EdgeworthHyp S β₀ m) (H u : ℝ) (hH : 0 < H)
    {γ₁ γ₂ : Measure (PathSpace d m H)} (h₁ : IsFutureGaussian (regime S β₀ hE).D (regime S β₀ hE).ρ m H u γ₁)
    (h₂ : IsFutureGaussian (regime S β₀ hE).D (regime S β₀ hE).ρ m H u γ₂) : γ₁ = γ₂ := by
  have := h₁.1.1
  have := h₂.1.1
  refine HRS.MD.EQGaussWindow.eqgw_ext_of_fidi γ₁ γ₂ fun p ts φ hφ => ?_
  choose ℓ hℓ using fun a : Fin p =>
    pathObservation_bounded m H (ts a) (φ a) (HRS.A33.a33_memSob m (hφ a))
  let L : PathSpace d m H →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin p => ℝ)).symm : (Fin p → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin p)).comp
      (ContinuousLinearMap.pi fun a => ℓ a)
  have hL : ∀ w a, L w a = NegSobolev.eval (PathSpace.at' w (ts a)) (φ a) := by
    intro w a
    exact (hℓ a).1 w
  have hG : HRS.MD.EQGaussWindow.eqgwG (m := m) ts φ = fun w => L w := by
    funext w
    ext a
    exact (hL w a).symm
  rw [hG]
  refine u4_map_eq_of_cov h₁.1 h₂.1 L fun i j => ?_
  simp only [hL, ← u4_pathAt_coe]
  rw [h₁.2 (ts i) (ts j) (φ i) (φ j) (hφ i) (hφ j) (ts i).2 (ts j).2,
    h₂.2 (ts i) (ts j) (φ i) (φ j) (hφ i) (hφ j) (ts i).2 (ts j).2]

end FutureUnique

section Wick

theorem u4_negSobolev_ext {r : ℝ} {F G : NegSobolev d r} (h : ∀ k, NegSobolev.fourierCoeff F k = NegSobolev.fourierCoeff G k) :
    F = G := by
  have h1 : ∀ k, NegSobolev.coord F k = NegSobolev.coord G k := by
    intro k
    have hp : Lattice.jp k.1 ^ r ≠ 0 := (Real.rpow_pos_of_pos (Torus.jp_pos _) _).ne'
    have := h k
    unfold NegSobolev.fourierCoeff at this
    exact mul_left_cancel₀ hp this
  have : (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) = (show lp (fun _ : NonzeroLattice d => ℝ) 2 from G) :=
    lp.ext (funext h1)
  exact this

theorem u4_ennreal_add_sq_le (x y : ℝ≥0∞) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow x y (p := 2) (by norm_num)
  have e : (2 : ℝ) - 1 = 1 := by norm_num
  rw [e, ENNReal.rpow_one] at h
  simpa [ENNReal.rpow_two] using h

theorem u4_measurable_fourierCoeff {Ω : Type} [MeasurableSpace Ω] {r : ℝ} {η : Ω → NegSobolev d r}
    (hη : Measurable η) (k : NonzeroLattice d) : Measurable fun ω => NegSobolev.fourierCoeff (η ω) k := by
  have : (fun ω => NegSobolev.fourierCoeff (η ω) k) = fun ω => NegSobolev.eval (η ω) (Torus.realMode k) :=
    funext fun ω => (HRS.MD.EQGaussWindow.eqgw_eval_realMode (η ω) k).symm
  rw [this]
  exact (HRS.MD.EQGaussWindow.eqgw_eval_continuous
    (HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k)).measurable.comp hη

theorem u4_halfWick_unique {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hη : Measurable η) (μ : Measure (Torus d)) (h : Torus d → Torus d → ℝ)
    (Q Q' : Ω → ℝ) (hQ : Measurable Q) (hQ' : Measurable Q')
    (h1 : IsHalfWick P η μ h Q) (h2 : IsHalfWick P η μ h Q') : Q =ᵐ[P] Q' := by
  set A : Finset (NonzeroLattice d) → Ω → ℝ := fun S ω => (1 / 2) * ∑ k ∈ S, ∑ l ∈ S,
      wickCoeff μ h k l * (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
        ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P) with hA
  have hAm : ∀ S, Measurable (A S) := by
    intro S
    refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun l _ => ?_) _
    exact Measurable.const_mul (((u4_measurable_fourierCoeff hη k).mul (u4_measurable_fourierCoeff hη l)).sub_const _) _
  have hle : ∀ S, ∫⁻ ω, ‖Q ω - Q' ω‖ₑ ^ 2 ∂P ≤
      2 * (∫⁻ ω, ‖Q ω - A S ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖Q' ω - A S ω‖ₑ ^ 2 ∂P) := by
    intro S
    have m1 : Measurable fun ω => ‖Q ω - A S ω‖ₑ ^ 2 := (hQ.sub (hAm S)).enorm.pow_const 2
    rw [← lintegral_add_left m1, ← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun ω => ?_
    have h3 : ‖Q ω - Q' ω‖ₑ ≤ ‖Q ω - A S ω‖ₑ + ‖Q' ω - A S ω‖ₑ := by
      calc ‖Q ω - Q' ω‖ₑ = ‖(Q ω - A S ω) - (Q' ω - A S ω)‖ₑ := by congr 1; ring
        _ ≤ ‖Q ω - A S ω‖ₑ + ‖Q' ω - A S ω‖ₑ := enorm_sub_le
    exact (pow_le_pow_left' h3 2).trans (u4_ennreal_add_sq_le _ _)
  have hlim : Tendsto (fun S : Finset (NonzeroLattice d) =>
      2 * (∫⁻ ω, ‖Q ω - A S ω‖ₑ ^ 2 ∂P + ∫⁻ ω, ‖Q' ω - A S ω‖ₑ ^ 2 ∂P)) atTop (𝓝 (2 * (0 + 0))) :=
    ENNReal.Tendsto.const_mul (h1.add h2) (Or.inr (by simp))
  have h0 : ∫⁻ ω, ‖Q ω - Q' ω‖ₑ ^ 2 ∂P ≤ 0 := by
    simpa using ge_of_tendsto' hlim hle
  have h00 : ∫⁻ ω, ‖Q ω - Q' ω‖ₑ ^ 2 ∂P = 0 := nonpos_iff_eq_zero.1 h0
  have m2 : Measurable fun ω => ‖Q ω - Q' ω‖ₑ ^ 2 := (hQ.sub hQ').enorm.pow_const 2
  have h00 := (lintegral_eq_zero_iff m2).1 h00
  filter_upwards [h00] with ω hω
  have : ‖Q ω - Q' ω‖ₑ = 0 := by simpa using hω
  exact sub_eq_zero.1 (by simpa using this)

theorem wick_unique_proof (s : ℝ) {Ω₀ : Type} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀) [IsProbabilityMeasure P₀]
    {r : ℝ} (η : ℝ → Ω₀ → NegSobolev d r) (ρ : ℝ → Torus d → ℝ) (B B' : ℝ → Ω₀ → NegSobolev d r)
    (hη : ∀ t, Measurable (η t))
    (hBm : Measurable (Function.uncurry B)) (hBm' : Measurable (Function.uncurry B'))
    (hB : ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      IsWickQuadraticField s P₀ (fun ω => η t ω) (withDensityReal (ρ t)) (B t))
    (hB' : ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))),
      IsWickQuadraticField s P₀ (fun ω => η t ω) (withDensityReal (ρ t)) (B' t)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), B t =ᵐ[P₀] B' t := by
  filter_upwards [hB, hB'] with t ht ht'
  have hBt : Measurable (B t) := hBm.comp (measurable_prodMk_left (x := t))
  have hBt' : Measurable (B' t) := hBm'.comp (measurable_prodMk_left (x := t))
  have hk : ∀ k : NonzeroLattice d, ∀ᵐ ω ∂P₀,
      NegSobolev.eval (B t ω) (Torus.realMode k) = NegSobolev.eval (B' t ω) (Torus.realMode k) := by
    intro k
    have hc := (HRS.MD.EQGaussWindow.eqgw_eval_continuous (m := r)
      (HRS.MD.EQGaussWindow.eqgw_isSmooth_realMode k)).measurable
    exact u4_halfWick_unique P₀ (fun ω => η t ω) (hη t) _ _ _ _ (hc.comp hBt) (hc.comp hBt') (ht k) (ht' k)
  filter_upwards [ae_all_iff.2 hk] with ω hω
  refine u4_negSobolev_ext fun k => ?_
  rw [← HRS.MD.EQGaussWindow.eqgw_eval_realMode, ← HRS.MD.EQGaussWindow.eqgw_eval_realMode]
  exact hω k

end Wick

section GaussDataExists

variable {S : PreparedData d} {β₀ m : ℝ}

/-- For every `N` a probability space with a prepared realisation of the `N`-particle system (a dummy one for `N = 0`). -/
theorem u4_exists_realizations (R : Regime d) (N : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      1 ≤ N → PreparedRealization R.D P
        (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X := by
  by_cases hN : 1 ≤ N
  · obtain ⟨Ω, mΩ, P, hP, X₀, W, X, h⟩ := HRS.MC.E213H.e213h_exists_prepared_realization R N hN
    exact ⟨Ω, mΩ, P, hP, X₀, W, X, fun _ => h⟩
  · refine ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => Classical.arbitrary _,
      fun _ _ => 0, fun _ _ => Classical.arbitrary _, fun h => absurd h hN⟩

theorem exists_gaussData_proof (hE : EdgeworthHyp S β₀ m) : Nonempty (GaussData S β₀ hE) := by
  set R := regime S β₀ hE with hR
  choose Ω mΩ P hP X₀ W X hreal using u4_exists_realizations R
  obtain ⟨Ω', mΩ', P', hP', η, hη⟩ :=
    HRS.MC.E213N.e213n_exists_gaussianLimitField R (rLvl d) rfl
  obtain ⟨-, B, hBm, hBw, hBL⟩ :=
    HRS.MC.Sec7.S7UCZ.s7_UC_uniform_chaos_proof R (rLvl d) rfl P X₀ W X hreal P' η hη
  refine ⟨{ Ω₀ := Ω'
            mΩ₀ := mΩ'
            P₀ := P'
            probP₀ := hP'
            η := η
            B := B
            limit := hη
            B_meas := hBm
            B_wick := hBw
            B_L2 := ?_ }⟩
  intro Rw hRw a ha
  exact (hBL Rw hRw 1 le_rfl).1 a ha

end GaussDataExists

end HRS.MC.E213U4
