import HRS.MC.CepH2Sde2
import HRS.MC.CepH2Aux31

/-!
# CEPH2, S1b: the folded laws of a chamber solution solve the weak Fokker-Planck equation
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_gen_bound {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0}
    (hK : LipschitzWith K (gradient U)) (θ : ℝ) {g : Ch N → ℝ} (hg : H2Test g) :
    ∃ C : ℝ, ∀ z, |h2_gen θ U g z| ≤ C := by
  obtain ⟨a, b, ha, hb, hab⟩ := h2_grad_growth hUper hK
  obtain ⟨C, hC⟩ := hg.bdd
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0).1
  refine ⟨|θ| * (N * C) + max a b * C, fun z => ?_⟩
  obtain ⟨-, h1, h2⟩ := hC z
  unfold h2_gen
  have hlap : |h2_lap g z| ≤ N * C := by
    unfold h2_lap
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum (g := fun _ => C) fun k _ => ?_) (by simp)
    rw [← Real.norm_eq_abs]
    refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
    simp only [EuclideanSpace.norm_single, norm_one, mul_one]
    exact h2
  have hin : |inner ℝ (gradient U z) (gradient g z)| ≤ max a b * C := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [h2_norm_gradient (U := g) z]
    have hr := norm_nonneg (h2_perp z)
    have hn := norm_nonneg (fderiv ℝ g z)
    calc ‖gradient U z‖ * ‖fderiv ℝ g z‖ ≤ (max a b * (1 + ‖h2_perp z‖)) * ‖fderiv ℝ g z‖ := by
          refine mul_le_mul_of_nonneg_right ((hab z).trans ?_) hn
          nlinarith [le_max_left a b, le_max_right a b, mul_le_mul_of_nonneg_right (le_max_left a b) hr,
            mul_le_mul_of_nonneg_right (le_max_right a b) hr]
      _ = max a b * (‖fderiv ℝ g z‖ * (1 + ‖h2_perp z‖)) := by ring
      _ ≤ max a b * C := mul_le_mul_of_nonneg_left h1 (le_max_of_le_left ha)
  calc |θ * h2_lap g z - inner ℝ (gradient U z) (gradient g z)|
      ≤ |θ * h2_lap g z| + |inner ℝ (gradient U z) (gradient g z)| := abs_sub _ _
    _ ≤ |θ| * (N * C) + max a b * C := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hlap (abs_nonneg _)) hin

theorem h2_fderiv_periodic_gen {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : Ch N → G}
    (hper : ∀ x, F (x + cep_diag N) = F x) (x : Ch N) : fderiv ℝ F (x + cep_diag N) = fderiv ℝ F x := by
  have : (fun y => F (y + cep_diag N)) = F := funext hper
  rw [← fderiv_comp_add_right, this]

theorem h2_gen_periodic {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) (θ : ℝ) {g : Ch N → ℝ}
    (hper : ∀ z, g (z + cep_diag N) = g z) (z : Ch N) :
    h2_gen θ U g (z + cep_diag N) = h2_gen θ U g z := by
  unfold h2_gen h2_lap
  rw [h2_gradient_periodic hUper, h2_gradient_periodic hper,
    h2_fderiv_periodic_gen (h2_fderiv_periodic hper)]

theorem h2_continuous_gen {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (θ : ℝ) {g : Ch N → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (h2_gen θ U g) := by
  unfold h2_gen h2_lap
  have h1 : Continuous (fderiv ℝ (fderiv ℝ g)) := by
    have : ContDiff ℝ 1 (fderiv ℝ g) := hg.fderiv_right (m := 1) (by norm_num)
    exact this.continuous_fderiv (by simp)
  refine Continuous.sub (continuous_const.mul (continuous_finset_sum _ fun k _ => ?_)) ?_
  · exact (h1.clm_apply continuous_const).clm_apply continuous_const
  · exact (h2_continuous_gradient (hU.of_le (by norm_num))).inner (h2_continuous_gradient (hg.of_le (by norm_num)))

theorem h2_drift_eq {U : Ch N → ℝ} (θ : ℝ) (hθ : 0 < θ) (g : Ch N → ℝ) (z : Ch N) :
    fderiv ℝ g z (-(gradient U z)) + (1 / 2) * ∑ k : Fin N, fderiv ℝ (fderiv ℝ g) z
      (Real.sqrt (2 * θ) • h2_e k) (Real.sqrt (2 * θ) • h2_e k) = h2_gen θ U g z := by
  unfold h2_gen h2_lap
  have hs : Real.sqrt (2 * θ) * Real.sqrt (2 * θ) = 2 * θ := Real.mul_self_sqrt (by linarith)
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have h1 : ∀ k : Fin N, Real.sqrt (2 * θ) * (Real.sqrt (2 * θ) * fderiv ℝ (fderiv ℝ g) z (h2_e k) (h2_e k)) =
      2 * θ * fderiv ℝ (fderiv ℝ g) z (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
    intro k
    rw [← mul_assoc, hs]; rfl
  simp only [h1, ← Finset.mul_sum]
  rw [map_neg, h2_fderiv_eq_inner, real_inner_comm]
  ring

theorem h2_sum_single (a : Fin N → ℝ) :
    ∑ k, a k • (EuclideanSpace.single k (1 : ℝ) : Ch N) = WithLp.toLp 2 a := by
  ext j
  simp [EuclideanSpace.single_apply, Pi.single_apply, Finset.sum_apply]

section
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem h2_measurable_reduce : Measurable (cep_reduce : Ch N → Ch N) := by
  unfold cep_reduce
  have h0 : Measurable fun z : Ch N => z 0 := (EuclideanSpace.proj (0 : Fin N)).continuous.measurable
  have hf : Measurable fun z : Ch N => ((⌊z 0⌋ : ℤ) : ℝ) :=
    (measurable_from_top (f := fun n : ℤ => (n : ℝ))).comp (Int.measurable_floor.comp h0)
  exact measurable_id.sub (hf.smul_const _)

/-- **S1b (Dynkin / weak Fokker-Planck)**. -/
theorem cepH2_weakFP_of_sde_proof [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z)
    {K : ℝ≥0} (hK : LipschitzWith K (gradient U)) {θ : ℝ} (hθ : 0 < θ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) {Z : ℝ → Ω → Ch N}
    (hZ : cep_IsChamberSolution P ℱ W' π (Real.sqrt (2 * θ)) (fun z => -(gradient U z)) z₀ Z) :
    H2WeakFP θ U (fun t => P.map fun ω => cep_reduce (Z t ω)) := by
  classical
  set ℱ' := h2_shift ℱ with hℱ'
  set Wt : ℝ≥0 → Ω → Fin N → ℝ := fun t ω k => W' t ω (π ω k, 0) with hWt
  have hWb : IsBrownianFiltration P ℱ' Wt := h2_shift_isBrownian (cepH2_noise_brownian_proof hW' hπ)
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hB : Continuous (fun z : Ch N => -(gradient U z)) := (h2_continuous_gradient hU1).neg
  set σ : Fin N → Ch N := fun k => Real.sqrt (2 * θ) • h2_e k with hσ
  have hZ0m : ∀ t : ℝ, Measurable[ℱ' t] (Z 0) := fun t =>
    (hZ.2.1 0 le_rfl).mono (ℱ.mono (le_max_right t 0)) le_rfl
  have hZad : ∀ t : ℝ, 0 ≤ t → Measurable[ℱ' t] (Z t) := fun t ht => by
    rw [h2_shift_eq ℱ ht]; exact hZ.2.1 t ht
  have hZc : ∀ ω, Continuous fun t => Z t ω := hZ.1
  have hnoise : ∀ (t : ℝ) (ω : Ω), ∑ k, (Wt (Real.toNNReal t) ω k - Wt 0 ω k) • σ k =
      Real.sqrt (2 * θ) • cep_noise π W' t ω := by
    intro t ω
    have h0 : Wt 0 ω = 0 := by funext k; simp [hWt, hW'.zero]
    simp only [h0, Pi.zero_apply, sub_zero, hσ, smul_comm _ (Real.sqrt (2 * θ)), ← Finset.smul_sum]
    congr 1
    exact h2_sum_single _
  have hzeq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Z t ω = Z 0 ω + (∫ s in Icc (0 : ℝ) t, -(gradient U (Z s ω))) +
      ∑ k, (Wt (Real.toNNReal t) ω k - Wt 0 ω k) • σ k := by
    filter_upwards [hZ.2.2] with ω hω t ht
    have h0 := hω 0 le_rfl
    have hn0 : cep_noise π W' 0 ω = 0 := by
      ext k; simp [cep_noise, hW'.zero]
    rw [intervalIntegral.integral_same, hn0, smul_zero, add_zero, add_zero] at h0
    have h0' : Z 0 ω = z₀ ω := h0
    rw [hnoise, h0', hω t ht, intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
  have hZprog : IsProgressive ℱ' (fun s ω => Z (max s 0) ω) :=
    b15d2_isProgressive_clampPath hZ0m hZad (fun ω => (hZc ω).continuousOn)
  have hZm : Measurable (fun p : ℝ × Ω => Z (max p.1 0) p.2) := measurable_of_progressive hZprog
  have hZmeas : ∀ t : ℝ, 0 ≤ t → Measurable (Z t) := fun t ht => (hZ.2.1 t ht).mono (ℱ.le t) le_rfl
  intro g hg t ht
  have hgs : ContDiff ℝ 2 g := hg.smooth
  obtain ⟨C, hCg⟩ := hg.bdd
  have hCgrad : ∀ y, ‖fderiv ℝ g y‖ ≤ C := fun y => by
    have := (hCg y).2.1
    nlinarith [norm_nonneg (fderiv ℝ g y), norm_nonneg (h2_perp y)]
  obtain ⟨M, hMint, hM0, hMae⟩ := h2_dynkin hWb hB hZ0m hZad hZc hzeq hgs hCgrad t ht
  obtain ⟨Cg, hCgen⟩ := h2_gen_bound hUper hK θ hg
  have hgcont := hgs.continuous
  have hgenc := h2_continuous_gen hU θ hgs
  -- the Fubini integrand
  set F : ℝ × Ω → ℝ := fun p => h2_gen θ U g (Z (max p.1 0) p.2) with hF
  have hFm : Measurable F := hgenc.measurable.comp hZm
  haveI : IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hFint : Integrable F ((volume.restrict (Icc (0 : ℝ) t)).prod P) :=
    Integrable.of_bound hFm.aestronglyMeasurable Cg (ae_of_all _ fun p => by
      rw [Real.norm_eq_abs]; exact hCgen _)
  have hpt : ∀ s ∈ Icc (0 : ℝ) t, ∀ ω, F (s, ω) = h2_gen θ U g (Z s ω) := by
    intro s hs ω; simp only [hF, max_eq_left hs.1]
  have hIint : Integrable (fun ω => ∫ s in Icc (0 : ℝ) t, F (s, ω)) P := hFint.integral_prod_right
  have hIeq : ∀ ω, ∫ s in Icc (0 : ℝ) t, F (s, ω) = ∫ s in Icc (0 : ℝ) t, h2_gen θ U g (Z s ω) := fun ω =>
    setIntegral_congr_fun measurableSet_Icc fun s hs => hpt s hs ω
  -- the expectation identity
  have hgZ : ∀ u : ℝ, 0 ≤ u → Integrable (fun ω => g (Z u ω)) P := fun u hu =>
    Integrable.of_bound (hgcont.measurable.comp (hZmeas u hu)).aestronglyMeasurable |C| (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact (hCg _).1.trans (le_abs_self C))
  have e1 : ∫ ω, g (Z t ω) ∂P = ∫ ω, g (Z 0 ω) ∂P + ∫ ω, (∫ s in Icc (0 : ℝ) t, F (s, ω)) ∂P := by
    have hae : ∀ᵐ ω ∂P, g (Z t ω) = g (Z 0 ω) + (∫ s in Icc (0 : ℝ) t, F (s, ω)) + M ω := by
      filter_upwards [hMae] with ω hω
      rw [hω, hIeq ω]
      congr 2
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      exact h2_drift_eq θ hθ g (Z s ω)
    rw [integral_congr_ae hae]
    have h1 : ∫ ω, ((g (Z 0 ω) + ∫ s in Icc (0 : ℝ) t, F (s, ω)) + M ω) ∂P =
        ∫ ω, (g (Z 0 ω) + ∫ s in Icc (0 : ℝ) t, F (s, ω)) ∂P + ∫ ω, M ω ∂P :=
      integral_add ((hgZ 0 le_rfl).add hIint) hMint
    have h2 : ∫ ω, (g (Z 0 ω) + ∫ s in Icc (0 : ℝ) t, F (s, ω)) ∂P =
        ∫ ω, g (Z 0 ω) ∂P + ∫ ω, (∫ s in Icc (0 : ℝ) t, F (s, ω)) ∂P :=
      integral_add (hgZ 0 le_rfl) hIint
    rw [h1, h2, hM0, add_zero]
  have e2 : ∫ ω, (∫ s in Icc (0 : ℝ) t, F (s, ω)) ∂P = ∫ s in Icc (0 : ℝ) t, ∫ ω, F (s, ω) ∂P :=
    (integral_integral_swap (f := fun (s : ℝ) (ω : Ω) => F (s, ω)) (by exact hFint)).symm
  have hlaw : ∀ u : ℝ, 0 ≤ u → ∀ f : Ch N → ℝ, Continuous f → (∀ z, f (z + cep_diag N) = f z) →
      ∫ z, f z ∂(P.map fun ω => cep_reduce (Z u ω)) = ∫ ω, f (Z u ω) ∂P := by
    intro u hu f hf hper
    rw [integral_map (φ := fun ω => cep_reduce (Z u ω)) (h2_measurable_reduce.comp (hZmeas u hu)).aemeasurable
      hf.aestronglyMeasurable]
    exact integral_congr_ae (ae_of_all _ fun ω => h2_periodic_reduce hper (Z u ω))
  rw [hlaw t ht g hgcont hg.periodic, hlaw 0 le_rfl g hgcont hg.periodic, e1, e2]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [hlaw s hs.1 _ hgenc (h2_gen_periodic hUper θ hg.periodic)]
  exact integral_congr_ae (ae_of_all _ fun ω => hpt s hs ω)

theorem h2_law_integral [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {Z : ℝ → Ω → Ch N}
    (hZm : ∀ t : ℝ, 0 ≤ t → Measurable[ℱ t] (Z t)) {u : ℝ} (hu : 0 ≤ u) {f : Ch N → ℝ}
    (hf : Continuous f) (hper : ∀ z, f (z + cep_diag N) = f z) :
    ∫ z, f z ∂(P.map fun ω => cep_reduce (Z u ω)) = ∫ ω, f (Z u ω) ∂P := by
  have hm : Measurable (Z u) := (hZm u hu).mono (ℱ.le u) le_rfl
  rw [integral_map (φ := fun ω => cep_reduce (Z u ω)) (h2_measurable_reduce.comp hm).aemeasurable
    hf.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun ω => h2_periodic_reduce hper (Z u ω))

/-- Narrow continuity (on `[0,T]`) of the folded laws of a continuous adapted process. -/
theorem cepH2_narrow_of_paths [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {Z : ℝ → Ω → Ch N}
    (hZm : ∀ t : ℝ, 0 ≤ t → Measurable[ℱ t] (Z t)) (hZc : ∀ ω, Continuous fun t => Z t ω) (T : ℝ)
    {g : Ch N → ℝ} (hg : Continuous g) (hper : ∀ z, g (z + cep_diag N) = g z) (hb : ∃ C : ℝ, ∀ z, |g z| ≤ C) :
    ContinuousOn (fun t => ∫ z, g z ∂(P.map fun ω => cep_reduce (Z t ω))) (Icc 0 T) := by
  obtain ⟨C, hC⟩ := hb
  have h := continuousOn_of_dominated (μ := P) (s := Icc (0 : ℝ) T) (F := fun (t : ℝ) (ω : Ω) => g (Z t ω))
    (bound := fun _ => |C|)
    (fun t ht => (hg.measurable.comp ((hZm t ht.1).mono (ℱ.le t) le_rfl)).aestronglyMeasurable)
    (fun t ht => ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact (hC _).trans (le_abs_self C))
    (integrable_const _) (ae_of_all _ fun ω => (hg.comp (hZc ω)).continuousOn)
  exact h.congr fun t ht => h2_law_integral hZm ht.1 hg hper

end

end HRS.MC.CepH2
