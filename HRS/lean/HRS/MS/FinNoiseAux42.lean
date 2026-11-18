import HRS.MS.FinNoiseAux41
import HRS.MS.FinNoiseAux35
import HRS.MS.SuppU6
import HRS.MS.Poinc

/-!
# S8.6 `finite_noise`: the chart system of the critical model (Pro FR06, FR08 data) (S86b)

`s86_charts_system`: for the critical quadratic model (`ρ₀` the unique thermal density) there are countably many charts
`(U_j, ψ_j)` with partition of unity `χ_j` (`∑ χ_j² = 1`), chart densities between `lo_j` and `hi_j ≤ Kr lo_j`
(`Q`-chart images of `ρ₀ dx|_{U_j}`), and for every time `t ∈ [0,H]` and gradient component `i` a bounded operator
`R_{ji} : ℓ²(ℤ^d) → 𝒦_H` with `χ_j Γ_{t,i} = 1_{U_j} R_{ji} b ∘ ψ_j` and `∑_{j,i} ‖R_{ji}‖² ≤ SR`.
The atlas is the one of `adapted_charts_proof` for the Gaussian comparison constants of `ρ₀` (S3.4); the reconstruction
operators come from the localised Fourier synthesis `s86_localized` with the weighted bounds of S8.5.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.MS.FinNoise

open HRS HRS.Whole HRS.Uniform

variable {d : ℕ}

theorem s86_clm_inj (A : Euc d →L[ℝ] Euc d) (h : LinearMap.det (A : Euc d →ₗ[ℝ] Euc d) ≠ 0) :
    Function.Injective A := by
  intro u v huv
  set e := A.toContinuousLinearEquivOfDetNeZero h
  have heA : ∀ w, e w = A w := fun w =>
    congrArg (fun f : Euc d →L[ℝ] Euc d => f w) (ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero A h)
  exact e.injective (by rw [heA, heA]; exact huv)

theorem s86_locC_nonneg (d r : ℕ) (CA CΓ P : ℝ) (Cχ : ℕ → ℝ) : 0 ≤ s86_locC d r CA CΓ P Cχ := by
  unfold s86_locC
  exact Finset.sum_nonneg fun l _ => by positivity

set_option maxHeartbeats 1600000 in
theorem s86_charts_system (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (Hz : ℝ) (hHz : 0 < Hz) :
    ∃ (J : Type) (_ : Countable J) (U : J → Set (Euc d)) (ψ : J → Euc d → Torus d)
      (χ : J → Euc d → ℝ) (lo hi : J → ℝ) (Kr SR : ℝ),
      (∀ j, MeasurableSet (U j)) ∧ (∀ j, Measurable (ψ j)) ∧ (∀ j, Measurable (χ j)) ∧
      (∀ x, HasSum (fun j => χ j x ^ 2) 1) ∧ (∀ j, 0 < lo j) ∧ 0 ≤ Kr ∧ (∀ j, hi j ≤ Kr * lo j) ∧
      (∀ j, ENNReal.ofReal (lo j) • (volume : Measure (Torus d)) ≤
        ((HRS.Whole.withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)).restrict (U j)).map (ψ j)) ∧
      (∀ j, ((HRS.Whole.withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)).restrict (U j)).map (ψ j) ≤
        ENNReal.ofReal (hi j) • (volume : Measure (Torus d))) ∧ 0 ≤ SR ∧
      ∀ t ∈ Set.Icc (0 : ℝ) Hz, ∃ R : J → Fin d → FeatureSpace d →L[ℝ] KSpace d m Hz,
        (∀ j (i : Fin d) x, χ j x • gradFeature (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) m Hz i t x =
          (U j).indicator (fun x => R j i (chartFeature (d := d) (d + 2) (ψ j x))) x) ∧
        Summable (fun p : J × Fin d => ‖R p.1 p.2‖ ^ 2) ∧ ∑' p : J × Fin d, ‖R p.1 p.2‖ ^ 2 ≤ SR := by
  classical
  set s : ℝ := (d : ℝ) / 2 with hs
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by simp only [hs]; linarith
  have hsd : s < (d : ℝ) := by simp only [hs]; linarith
  set ρ₀ : Euc d → ℝ := thermalDensity d s a β with hρ₀
  have hρ₀eq : IsThermalEquilibrium d s a β ρ₀ :=
    (HRS.MS.S85.s85_thermal_eq hd hs0 hsd ha hβ (ρ := ρ₀) (by
      obtain ⟨⟨ρ0, hρ0, -⟩, -, -⟩ := HRS.MS.Thm.thermalDensity_spec_proof hd hs0 hsd a β ha hβ
      exact (HRS.MS.S85.s85_thermal_eq hd hs0 hsd ha hβ hρ0).2)).2
  have hρ₀meas : Measurable ρ₀ := hρ₀eq.1.1.measurable
  -- Gaussian comparison
  obtain ⟨cg, hcg, Cg, hgb, -⟩ := HRS.MS.Poinc.euc_thermal_gaussian_bounds_proof hd hs0 hsd a β ha hβ
  set G0 : ℝ := (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) with hG0
  have hG0pos : 0 < G0 := by
    have : 0 < β * a / (2 * Real.pi) := by positivity
    exact Real.rpow_pos_of_pos this _
  have hexp : ∀ x : Euc d, Real.exp (-(β * a) * ‖x‖ ^ 2 / 2) = Real.exp (-β * a * ‖x‖ ^ 2 / 2) := by
    intro x; congr 1; ring
  have hgauss : ∀ x : Euc d, (cg * G0) * Real.exp (-(β * a) * ‖x‖ ^ 2 / 2) ≤ ρ₀ x ∧
      ρ₀ x ≤ (Cg * G0) * Real.exp (-(β * a) * ‖x‖ ^ 2 / 2) := by
    intro x
    obtain ⟨h1, h2⟩ := hgb x
    simp only [gaussianComparison] at h1 h2
    rw [hexp]
    constructor
    · calc cg * G0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2) = cg * (G0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) := by ring
        _ ≤ ρ₀ x := h1
    · calc ρ₀ x ≤ Cg * (G0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2)) := h2
        _ = Cg * G0 * Real.exp (-β * a * ‖x‖ ^ 2 / 2) := by ring
  have hρ₀pos : ∀ x, 0 < ρ₀ x := fun x =>
    lt_of_lt_of_le (by have := Real.exp_pos (-(β * a) * ‖x‖ ^ 2 / 2); positivity) (hgauss x).1
  -- the atlas
  obtain ⟨ι, hιc, xc, A, χ, hχ, hsq, ⟨CA, hCA⟩, ⟨cdet, Cdet, hcdet, hdet⟩, hder, ⟨K0, hK0⟩,
    ⟨c₁, C₁, hc₁, hdens⟩, hsumj⟩ := adapted_charts_proof hd (β * a) (cg * G0) (Cg * G0)
    (by positivity) (by positivity) ρ₀ hgauss
  choose Cχ hCχ using hder
  have hdetj : ∀ j, LinearMap.det (A j : Euc d →ₗ[ℝ] Euc d) ≠ 0 := by
    intro j h
    have h1 := (hdet j).1.trans_eq (by rw [h, abs_zero])
    have : 0 < cdet * jbracket (xc j) ^ (-1 : ℝ) := mul_pos hcdet (Real.rpow_pos_of_pos (by
      unfold jbracket; positivity) _)
    linarith
  -- features
  obtain ⟨CΓ, hCΓ⟩ := HRS.MS.S85.feature_decay_proof hd a β ha hβ m hm Hz hHz
  obtain ⟨-, hrest⟩ := hCΓ ρ₀ hρ₀eq
  obtain ⟨ιb, hιb, bK, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := KSpace d m Hz)
  haveI := hιb
  -- constants
  set p : ℝ := (d : ℝ) / 2 + 2 with hp
  set Pc : ℝ := (1 + CA * d) ^ p with hPc
  set Cc : ℝ := s86_locC d (d + 2) CA CΓ Pc Cχ with hCc
  have hCc0 : 0 ≤ Cc := s86_locC_nonneg _ _ _ _ _ _
  have hsumj' : Summable fun j => jbracket (xc j) ^ (-(2 * p)) :=
    hsumj p (by simp only [hp]; linarith)
  set SJ : ℝ := ∑' j, jbracket (xc j) ^ (-(2 * p)) with hSJ
  have hSJ0 : 0 ≤ SJ := tsum_nonneg fun j => Real.rpow_nonneg (by
    unfold jbracket; positivity) _
  -- chart images
  set α : ι → ℝ := fun j => ρ₀ (xc j) * |LinearMap.det (A j : Euc d →ₗ[ℝ] Euc d)| with hα
  have hαpos : ∀ j, 0 < α j := fun j => mul_pos (hρ₀pos _) (abs_pos.2 (hdetj j))
  have hdensj : ∀ j, ∃ (U : Set (Euc d)) (ψ : Euc d → Torus d), MeasurableSet U ∧ Measurable ψ ∧
      U = (fun u => xc j + A j u) '' s86_cube0 d ∧ (∀ u, ψ (xc j + A j u) = Torus.mk u) ∧
      ENNReal.ofReal (c₁ * α j) • (volume : Measure (Torus d)) ≤
        ((HRS.Whole.withDensityReal ρ₀).restrict U).map ψ ∧
      ((HRS.Whole.withDensityReal ρ₀).restrict U).map ψ ≤
        ENNReal.ofReal (C₁ * α j) • (volume : Measure (Torus d)) := by
    intro j
    refine s86_chart_density ρ₀ hρ₀meas (xc j) (A j) (hdetj j) (c₁ * α j) (C₁ * α j) ?_ ?_
    · intro u hu
      exact (hdens j u (s86_cube0_sub_closed hu)).1
    · intro u hu
      exact (hdens j u (s86_cube0_sub_closed hu)).2
  choose U ψ hUm hψm hUeq hψF hlo hle using hdensj
  -- tsupport inside the chart image
  have hχzero : ∀ j x, x ∉ U j → χ j x = 0 := by
    intro j x hx
    by_contra hne
    have hxs : x ∈ tsupport (χ j) := subset_tsupport _ hne
    obtain ⟨u, hu, rfl⟩ := (hχ j).2 hxs
    exact hx (by rw [hUeq j]; exact ⟨u, s86_interior_sub_cube0 (s86_interior_cube hu), rfl⟩)
  refine ⟨ι, hιc, U, ψ, χ, fun j => c₁ * α j, fun j => C₁ * α j, max (C₁ / c₁) 0, d * Cc * SJ,
    hUm, hψm, ?_, ?_, fun j => mul_pos hc₁ (hαpos j), le_max_right _ _, ?_, hlo, hle, ?_, ?_⟩
  · intro j
    exact (hχ j).1.continuous.measurable
  · intro x
    exact (hsq x).1.hasSum_iff.2 (hsq x).2
  · intro j
    show C₁ * α j ≤ max (C₁ / c₁) 0 * (c₁ * α j)
    have : C₁ * α j = (C₁ / c₁) * (c₁ * α j) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_pos hc₁ (hαpos j)).le
  · positivity
  · intro t ht
    have hR : ∀ j (i : Fin d), ∃ R : FeatureSpace d →L[ℝ] KSpace d m Hz,
        (∀ u : Euc d, (∀ k, |u k| ≤ 1 / 2) →
          R (chartFeature (d := d) (d + 2) (Torus.mk u)) =
            χ j (xc j + A j u) • gradFeature (critCoeff d a β ρ₀) m Hz i t (xc j + A j u)) ∧
        ‖R‖ ^ 2 ≤ Cc * jbracket (xc j) ^ (-(2 * p)) := by
      intro j i
      obtain ⟨h1, h2, h3⟩ := hrest i t ht
      obtain ⟨R, hR1, hR2⟩ := s86_localized (d + 2) (by omega) p (by simp only [hp]; positivity) bK
        (fun x => gradFeature (critCoeff d a β ρ₀) m Hz i t x) h2 CΓ
        (fun l hl x => h3 x l hl) CA Cχ (xc j) (A j) (s86_clm_inj _ (hdetj j)) (hCA j) (χ j)
        ((hχ j).1.of_le (WithTop.coe_le_coe.2 le_top)) (hχ j).2 (fun l hl u => hCχ l j u)
      exact ⟨R, hR1, hR2⟩
    choose R hR1 hR2 using hR
    refine ⟨R, ?_, ?_, ?_⟩
    · intro j i x
      by_cases hx : x ∈ U j
      · rw [Set.indicator_of_mem hx]
        rw [hUeq j] at hx
        obtain ⟨u, hu, rfl⟩ := hx
        rw [hψF j u]
        exact (hR1 j i u (s86_cube0_sub_closed hu)).symm
      · rw [Set.indicator_of_notMem hx, hχzero j x hx, zero_smul]
    · have hbd : ∀ q : ι × Fin d, ‖R q.1 q.2‖ ^ 2 ≤ Cc * jbracket (xc q.1) ^ (-(2 * p)) :=
        fun q => hR2 q.1 q.2
      have hg : Summable fun q : ι × Fin d => Cc * jbracket (xc q.1) ^ (-(2 * p)) := by
        rw [summable_prod_of_nonneg (fun q => mul_nonneg hCc0 (Real.rpow_nonneg (by
          unfold jbracket; positivity) _))]
        refine ⟨fun x => Summable.of_finite, ?_⟩
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact (hsumj'.mul_left Cc).mul_left (d : ℝ)
      exact Summable.of_nonneg_of_le (fun q => sq_nonneg _) hbd hg
    · have hbd : ∀ q : ι × Fin d, ‖R q.1 q.2‖ ^ 2 ≤ Cc * jbracket (xc q.1) ^ (-(2 * p)) :=
        fun q => hR2 q.1 q.2
      have hg : Summable fun q : ι × Fin d => Cc * jbracket (xc q.1) ^ (-(2 * p)) := by
        rw [summable_prod_of_nonneg (fun q => mul_nonneg hCc0 (Real.rpow_nonneg (by
          unfold jbracket; positivity) _))]
        refine ⟨fun x => Summable.of_finite, ?_⟩
        simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact (hsumj'.mul_left Cc).mul_left (d : ℝ)
      have hsm : Summable fun q : ι × Fin d => ‖R q.1 q.2‖ ^ 2 :=
        Summable.of_nonneg_of_le (fun q => sq_nonneg _) hbd hg
      calc ∑' q : ι × Fin d, ‖R q.1 q.2‖ ^ 2 ≤ ∑' q : ι × Fin d, Cc * jbracket (xc q.1) ^ (-(2 * p)) :=
            hsm.tsum_le_tsum hbd hg
        _ = d * Cc * SJ := by
            rw [s86_tsum_prod_fin _ hg]
            simp only [tsum_mul_left, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rw [hSJ]; ring

end HRS.MS.FinNoise
