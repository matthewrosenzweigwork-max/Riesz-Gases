import HRS.MS.WsStatAux31

/-!
# S21 packet K-1: scaling lemmas for the `beta < 1` normalisation

The stationary setup has `sigma = sqrt (N beta)`, `q = 1` (`sigmaScale = min kappa sqrt(N/invbeta)`), while the frozen statement is for
`zeta = sqrt N (mu_N - m_N) = beta^{-1/2} Xi`.  This file collects: the values of `sigma`, `q` (`s21_sigma_eq`), the window of a scaled
process (`s21_wpo_smul`), `zetaPathW = beta^{-1/2} s21XiPath` (`s21_zeta_eq`), scaling of Gaussian laws without positivity
(`s21_gauss_smul_ne`), linearity of `noiseCovW` in `q`, and a.s. equality of continuous modifications (`s21_X_eq_ae`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc)

variable {d : ℕ}

theorem s21_sigma_eq (b : WholeBounds d) (S : WholeSetup b) {β : ℝ} (hβ : 0 < β)
    (hinv : ∀ N, S.invβ N = β⁻¹) {N : ℕ} (hN : 1 ≤ N) (hκ : S.κ N = Real.sqrt ((N : ℝ) * β)) :
    S.σ N = Real.sqrt ((N : ℝ) * β) ∧ S.q N = 1 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hinv0 : β⁻¹ ≠ 0 := inv_ne_zero hβ.ne'
  have hdiv : (N : ℝ) / β⁻¹ = N * β := by field_simp
  have hσ' : sigmaScale N (S.κ N) β⁻¹ = Real.sqrt ((N : ℝ) * β) := by
    unfold sigmaScale
    rw [if_neg hinv0, hdiv, hκ, min_self]
  have hσ : S.σ N = Real.sqrt ((N : ℝ) * β) := by
    unfold WholeSetup.σ
    rw [hinv N]
    exact hσ'
  refine ⟨hσ, ?_⟩
  unfold WholeSetup.q qScale
  rw [hinv N, if_neg hinv0, hσ', Real.sq_sqrt (by positivity)]
  field_simp

open Classical in
theorem s21_dite_smul {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : X → E) (c : ℝ) (hc : c ≠ 0) :
    (if h : Continuous (fun x => c • f x) then (⟨fun x => c • f x, h⟩ : C(X, E)) else 0) =
      c • (if h : Continuous f then (⟨f, h⟩ : C(X, E)) else 0) := by
  by_cases h : Continuous f
  · have h2 : Continuous (fun x => c • f x) := h.const_smul c
    rw [dif_pos h2, dif_pos h]
    rfl
  · have h2 : ¬ Continuous (fun x => c • f x) := fun h' => h ((continuous_const_smul_iff₀ hc).1 h')
    rw [dif_neg h2, dif_neg h, smul_zero]

theorem s21_wpo_smul {m T : ℝ} (c : ℝ) (hc : c ≠ 0) (f : ℝ → OscDual d m) :
    windowPathOf m T 0 (fun t => c • f t) = c • windowPathOf m T 0 f := by
  unfold windowPathOf
  exact s21_dite_smul (X := Set.Icc (0 : ℝ) T) (E := OscDual d m) (fun t => f (0 + (t : ℝ))) c hc

theorem s21_gauss_smul_ne {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) {c : ℝ} (hc : c ≠ 0) :
    (multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S).map (fun z => c • z) =
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) ((c ^ 2) • S) := by
  by_cases hS : S.PosSemidef
  · exact s21_gauss_smul hS c
  · have hS' : ¬ ((c ^ 2) • S).PosSemidef := by
      intro h
      apply hS
      have := h.smul (inv_nonneg.2 (sq_nonneg c))
      rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 hc), one_smul] at this
    rw [multivariateGaussian_of_not_posSemidef _ hS, multivariateGaussian_of_not_posSemidef _ hS']
    exact (Measure.map_dirac' (f := fun z : EuclideanSpace ℝ (Fin p) => c • z) (measurable_id.const_smul c) 0).trans (by simp)

theorem s21_noiseCovW_q (C : WholeCoeff d) (q t t' : ℝ) (φ ψ : Euc d → ℝ) :
    noiseCovW C q t t' φ ψ = q * noiseCovW C 1 t t' φ ψ := by
  unfold noiseCovW
  ring

theorem s21_X_eq_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (X X' : ℝ≥0 → Ω → EucConfig d N) (hmod : ∀ t : ℝ≥0, (t : ℝ) ≤ T → X' t =ᵐ[P] X t)
    (hc : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ζ i)
    (hc' : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t : ℝ≥0 => X' t ζ i) :
    ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ζ = X' t ζ := by
  haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  set s : ℕ → Set.Icc (0 : ℝ) T := TopologicalSpace.denseSeq (Set.Icc (0 : ℝ) T) with hsdef
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hn : ∀ n : ℕ, ∀ᵐ ζ ∂P, X (Real.toNNReal (s n)) ζ = X' (Real.toNNReal (s n)) ζ := fun n => by
    have := hmod (Real.toNNReal (s n)) (by rw [Real.coe_toNNReal _ (s n).2.1]; exact (s n).2.2)
    filter_upwards [this] with ζ hζ using hζ.symm
  filter_upwards [ae_all_iff.2 hn, hc, hc'] with ζ h1 h2 h3 t ht
  have hX : Continuous fun u : Set.Icc (0 : ℝ) T => X (Real.toNNReal u) ζ :=
    (continuous_pi h2).comp (continuous_real_toNNReal.comp continuous_subtype_val)
  have hX' : Continuous fun u : Set.Icc (0 : ℝ) T => X' (Real.toNNReal u) ζ :=
    (continuous_pi h3).comp (continuous_real_toNNReal.comp continuous_subtype_val)
  have heq : (fun u : Set.Icc (0 : ℝ) T => X (Real.toNNReal u) ζ) =
      fun u : Set.Icc (0 : ℝ) T => X' (Real.toNNReal u) ζ :=
    hs.equalizer hX hX' (funext fun n => h1 n)
  have := congrFun heq ⟨(t : ℝ), t.2, ht⟩
  simpa using this

theorem s21_zeta_eq (b : WholeBounds d) (S : WholeSetup b) {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) {β : ℝ} (hβ : 0 < β)
    (hσ : S.σ N = Real.sqrt (N : ℝ) * Real.sqrt β)
    (hstat : ∀ t ∈ Set.Icc (0 : ℝ) b.T, P.map (X (Real.toNNReal t)) = P.map (X 0)) (hN : 0 < N) (ζ : Ω) :
    zetaPathW b.m b.T 0 P X ζ =
      (Real.sqrt β)⁻¹ • s21XiPath S X (HRS.Whole.meanEmpirical (P.map (X 0))) ζ := by
  unfold zetaPathW s21XiPath
  rw [← s21_wpo_smul (Real.sqrt β)⁻¹ (inv_ne_zero (Real.sqrt_pos.2 hβ).ne')]
  refine s56_wpo_congr fun t ht => ?_
  have hsb : (0 : ℝ) < Real.sqrt β := Real.sqrt_pos.2 hβ
  have hsN : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  unfold zetaB s21Xi
  rw [hstat t ht, hσ, smul_smul]
  congr 1
  field_simp

end HRS.MS.S21
