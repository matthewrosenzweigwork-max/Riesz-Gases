import HRS.MS.S81G_Couple
import HRS.MS.S81R_Gap
import HRS.MS.S81R_Mk

/-!
# S81R, packet R9: identification of the regularised strong solutions with the Pois flow of the rescaled system

* `s81r_setup`: the filtration/noise/regularised solutions `Ys M` of `s81g_couple`, exported with their data;
* `s81r_lipDrift`: `z ↦ -q z + B z` is globally Lipschitz for `B ∈ C_b¹`;
* `s81r_transport`: the image under `Φ = √β enc` of a pathwise solution of the configuration SDE (drift `sb1DriftM`)
  is a pathwise solution of the Pois equation `dz = (-a z + ∇G(z)) dt + √2 dw` (noise reindexed by `finProdFinEquiv`);
* `s81r_ident_flow`: by pathwise uniqueness `Φ(y_t) = flowMap a (∇G) w' t (Φ y₀)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf HRS.MS.PoisFlow
  HRS.MS.Gap HRS.MS.S81G
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S81R

variable {d N : ℕ}

theorem s81r_lipDrift {m : ℕ} {q Mb : ℝ} (hq : 0 ≤ q) {B : Euc m → Euc m} (hB : Whole.HasCbBound 1 Mb B) :
    IsLipschitzDrift (fun (_ : ℝ) (z : Euc m) => -q • z + B z) where
  cont := ((continuous_snd.const_smul (-q)).add (hB.1.continuous.comp continuous_snd)).continuousOn
  lip _ := ⟨(q + |Mb|).toNNReal, fun t _ => LipschitzWith.of_dist_le_mul fun z z' => by
    show dist (-q • z + B z) (-q • z' + B z') ≤ _
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    have e : (-q • z + B z) - (-q • z' + B z') = -q • (z - z') + (B z - B z') := by module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖-q • (z - z')‖ = q * ‖z - z'‖ := by
      rw [norm_smul, norm_neg, Real.norm_of_nonneg hq]
    have h2 := pf_lip_of_cb le_rfl hB z z'
    have h3 : Mb * ‖z - z'‖ ≤ |Mb| * ‖z - z'‖ :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    nlinarith⟩

/-- image of a pathwise configuration solution under `Φ` -/
theorem s81r_transport {s a β : ℝ} (hβ : 0 < β) {k : Euc d → ℝ} (G : Euc (N * d) → ℝ)
    (hG : ∀ y, -a • y + gradient G y = Real.sqrt β • s81r_encFun
      (sb1DriftM (Whole.quadraticGradientDyn d s a β) k N (s81r_Psi β d N y)))
    {w : ℝ≥0 → (Fin N × Fin d) → ℝ} {y₀ : Whole.EucConfig d N} {y : ℝ → Whole.EucConfig d N}
    (hy : IsPathSolution (fun _ => sb1DriftM (Whole.quadraticGradientDyn d s a β) k N)
      (p4r_sigma d N (Whole.quadraticGradientDyn d s a β).invβ) w y₀ ⊤ y) :
    IsPathSolution (fun _ z => -a • z + gradient G z) (pfSigma (N * d))
      (fun t k' => w t (finProdFinEquiv.symm k')) (s81r_Phi β d N y₀) ⊤
      (fun t => s81r_Phi β d N (y t)) := by
  have hdrift : ∀ z : Whole.EucConfig d N,
      -a • s81r_Phi β d N z + gradient G (s81r_Phi β d N z) =
        s81r_Phi β d N (sb1DriftM (Whole.quadraticGradientDyn d s a β) k N z) := by
    intro z
    rw [hG (s81r_Phi β d N z), s81r_Psi_Phi hβ z, s81r_Phi_apply]
  refine ⟨by show s81r_Phi β d N (y 0) = _; rw [hy.1], fun t ht _ => ?_⟩
  obtain ⟨hc, hi, he⟩ := hy.2 t ht (WithTop.coe_lt_top t)
  have hfun : (fun r => -a • s81r_Phi β d N (y r) + gradient G (s81r_Phi β d N (y r))) =
      fun r => s81r_Phi β d N (sb1DriftM (Whole.quadraticGradientDyn d s a β) k N (y r)) :=
    funext fun r => hdrift (y r)
  refine ⟨(s81r_Phi β d N).continuous.comp_continuousOn hc, ?_, ?_⟩
  · show MeasureTheory.IntegrableOn
      (fun r => -a • s81r_Phi β d N (y r) + gradient G (s81r_Phi β d N (y r))) (Set.Icc 0 t)
    rw [hfun]
    exact (s81r_Phi β d N).integrable_comp hi
  · have e1 : ∫ r in Set.Icc 0 t, (-a • s81r_Phi β d N (y r) + gradient G (s81r_Phi β d N (y r))) =
        s81r_Phi β d N (∫ r in Set.Icc 0 t, sb1DriftM (Whole.quadraticGradientDyn d s a β) k N (y r)) := by
      rw [hfun]
      exact (s81r_Phi β d N).integral_comp_comm hi
    have e2 : ∑ k' : Fin (N * d), w (Real.toNNReal t) (finProdFinEquiv.symm k') •
        pfSigma (N * d) k' =
        s81r_Phi β d N (∑ p : Fin N × Fin d, w (Real.toNNReal t) p •
          p4r_sigma d N (Whole.quadraticGradientDyn d s a β).invβ p) := by
      rw [map_sum, ← Equiv.sum_comp (finProdFinEquiv : Fin N × Fin d ≃ Fin (N * d))]
      refine Finset.sum_congr rfl fun p _ => ?_
      obtain ⟨i, j⟩ := p
      have hσ : s81r_Phi β d N (p4r_sigma d N (Whole.quadraticGradientDyn d s a β).invβ (i, j)) =
          pfSigma (N * d) (finProdFinEquiv (i, j)) := s81r_Phi_sigma hβ i j
      rw [map_smul, hσ, Equiv.symm_apply_apply]
    show s81r_Phi β d N (y t) = s81r_Phi β d N y₀ +
      (∫ r in Set.Icc 0 t, (-a • s81r_Phi β d N (y r) + gradient G (s81r_Phi β d N (y r)))) +
      ∑ k' : Fin (N * d), w (Real.toNNReal t) (finProdFinEquiv.symm k') • pfSigma (N * d) k'
    rw [e1, e2, he, map_add, map_add]

/-- pathwise uniqueness: `Φ(y_t)` is the Pois flow of the rescaled system -/
theorem s81r_ident_flow {s a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {k : Euc d → ℝ}
    (ρ G : Euc (N * d) → ℝ) (hR : GapRef (N * d) ρ a (gradient G))
    (hG : ∀ y, -a • y + gradient G y = Real.sqrt β • s81r_encFun
      (sb1DriftM (Whole.quadraticGradientDyn d s a β) k N (s81r_Psi β d N y)))
    {w : ℝ≥0 → (Fin N × Fin d) → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0)
    {y₀ : Whole.EucConfig d N} {y : ℝ → Whole.EucConfig d N}
    (hy : IsPathSolution (fun _ => sb1DriftM (Whole.quadraticGradientDyn d s a β) k N)
      (p4r_sigma d N (Whole.quadraticGradientDyn d s a β).invβ) w y₀ ⊤ y) :
    ∀ t : ℝ, 0 ≤ t → s81r_Phi β d N (y t) =
      flowMap a (gradient G) (fun u k' => w u (finProdFinEquiv.symm k')) t (s81r_Phi β d N y₀) := by
  obtain ⟨Mb1, hMb1⟩ := hR.cb 1
  obtain ⟨Mb2, hMb2⟩ := hR.cb 2
  have hz := s81r_transport hβ G hG hy
  have hwc' : Continuous (fun u k' => w u (finProdFinEquiv.symm k')) :=
    continuous_pi fun k' => (continuous_apply (finProdFinEquiv.symm k')).comp hwc
  have hw0' : (fun u k' => w u (finProdFinEquiv.symm k')) 0 = 0 := by
    funext k'
    simp [hw0]
  have H : PfHyp a Mb2 2 (gradient G) (fun u k' => w u (finProdFinEquiv.symm k')) :=
    ⟨ha.le, by norm_num, hMb2, hwc', hw0'⟩
  have hfl := pf_flowMap_isPathSolution H (s81r_Phi β d N y₀)
  intro t ht
  exact ode_additive_unique Set.univ isOpen_univ (fun _ z => -a • z + gradient G z)
    (s81r_lipDrift ha.le hMb1).toLoc (pfSigma (N * d)) (fun u k' => w u (finProdFinEquiv.symm k'))
    hwc' (s81r_Phi β d N y₀) hz hfl (fun _ _ _ => trivial) (fun _ _ _ => trivial) t ht
    (by rw [min_self]; exact WithTop.coe_lt_top _)

/-- the filtration, noise and regularised solutions of `s81g_couple`, with their data -/
theorem s81r_setup (D : Whole.WholeDyn d) (hM : D.M = -1) (hs0 : 0 ≤ D.s) {B : ℝ}
    (P : Sb1Pot D.V B) {T : ℝ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hW : IsVectorBrownian Pm W)
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D T X₀ W X)
    (hind : IndepFun X₀ (fun ζ t => W t ζ) Pm) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
      (Ys : ℕ → ℝ → Ω → Whole.EucConfig d N),
      IsBrownianFiltration Pm ℱ W' ∧ (∀ t : ℝ, Measurable[ℱ t] (X 0)) ∧
      (∀ (M : ℕ) (τ : ℝ), Measurable (Ys M τ)) ∧
      (∀ M : ℕ, ∀ᵐ ζ ∂Pm, IsPathSolution (fun _ => sb1DriftM D (sb1kM d D.s M) N)
        (p4r_sigma d N D.invβ) (fun t => W' t ζ) (X 0 ζ) ⊤ (fun t => Ys M t ζ)) ∧
      (∀ T' : ℝ, 0 < T' → Whole.IsWholeStrongSolution Pm D T' X₀ W X →
        ∀ᵐ ζ ∂Pm, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T' → Ys M (t : ℝ) ζ = X t ζ) := by
  have hind' : IndepFun (X 0) (fun ζ t => W t ζ) Pm :=
    hind.congr (hX.init.mono fun ζ h => h.symm) Filter.EventuallyEq.rfl
  obtain ⟨W', hW'm, hcoords, hBF, hX0⟩ :=
    exists_isBrownianFiltration_of_isVectorBrownian Pm W hW (X 0) (hX.adapted 0) hind'
  set ℱ := generatedFiltration Pm (X 0) (hX.adapted 0) W' hW'm with hℱ
  have hW' : IsBrownianFiltration Pm (p4r_shiftFil ℱ) W' := p4r_shiftFil_brownian hBF
  have hY0 : ∀ t : ℝ, Measurable[p4r_shiftFil ℱ t] (X 0) := fun t => hX0 (max t 0)
  have hex : ∀ M : ℕ, ∃ Ys : ℝ → Ω → Whole.EucConfig d N,
      IsAdditiveSDESolution Pm (p4r_shiftFil ℱ) W' (fun _ => sb1DriftM D (sb1kM d D.s M) N)
        (p4r_sigma d N D.invβ) (X 0) (fun _ => ⊤) Ys := fun M =>
    exists_sde_solution_global_exists hW' _
      (sb1_driftM_isLip D (sb1kM_isKernel D.s hs0 M) P N) _ hY0
  choose Ys hYs using hex
  refine ⟨ℱ, W', Ys, hBF, hX0, fun M τ => ((hYs M).adapted τ).mono ((p4r_shiftFil ℱ).le _) le_rfl,
    fun M => (hYs M).isPathSolution, fun T' hT' hX' => ?_⟩
  exact s81g_ident D hM P hT' hX' hBF hcoords (fun M => sb1kM_isKernel D.s hs0 M) hYs

end HRS.MS.S81R
