import HRS.MS.CovMeasAux24

/-!
# S10.1 (worker S101B), part 25: the value of the push-forward measure on two observations is the `IsR2JValue` integral

`s101_Jx_eval`: for `φ_a, φ_b` finite combinations of the `φ_α`, `t_a,t_b ∈ [0,T]` and `l_i(w) = (w(t_i))(φ_i)`,
`Jx D' I (l₁⊗l₂) = 2ν ∫_{I∩[0,t_a∧t_b]} z^r(∇U^{r,t_a}φ_a · ∇U^{r,t_b}φ_b) dr`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.CovMeas

open HRS HRS.Whole HRS.MS.Go HRS.MS.FixEq HRS.Uniform HRS.Uniform.Q45 HRS.MS.GenPath HRS.MS.U9
open Classical

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ}

lemma s101_abs_le_tn {A : S101Bil d m T}
    (hA : BddAbove (Set.range fun p : HRS.OrthonormalPairs (KSpace d m T) => ∑ i, |A (p.1.2.1 i) (p.1.2.2 i)|))
    (u v : KSpace d m T) : |A u v| ≤ HRS.traceNormForm A * (‖u‖ * ‖v‖) := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hv : v = 0
  · simp [hv]
  have hu' : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  have hv' : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  set e : KSpace d m T := ‖u‖⁻¹ • u with he
  set f : KSpace d m T := ‖v‖⁻¹ • v with hf
  have he1 : ‖e‖ = 1 := by rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hu']
  have hf1 : ‖f‖ = 1 := by rw [hf, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv']
  let p : HRS.OrthonormalPairs (KSpace d m T) :=
    ⟨⟨1, (fun _ => e, fun _ => f)⟩, ⟨orthonormal_subsingleton_iff.2 (fun _ => he1),
      orthonormal_subsingleton_iff.2 (fun _ => hf1)⟩⟩
  have h1 : ∑ i : Fin 1, |A e f| ≤ HRS.traceNormForm A := le_ciSup hA p
  simp only [Finset.univ_unique, Finset.sum_singleton] at h1
  have h2 : A u v = ‖u‖ * ‖v‖ * A e f := by
    rw [he, hf]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  rw [h2, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u‖ * ‖v‖)]
  calc ‖u‖ * ‖v‖ * |A e f| ≤ ‖u‖ * ‖v‖ * HRS.traceNormForm A :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

lemma s101_Dm_entry_integrable (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) (htr : S101Tr C m T z)
    (u v : KSpace d m T) : IntegrableOn (fun τ => s101Dm C m T z τ u v) (Icc (0 : ℝ) T) := by
  have hTD := s101_Dm_isTraceDensity A hT htr
  have hint : IntegrableOn (fun τ => HRS.traceNormForm (s101Dm C m T z τ)) (Icc 0 T) := hTD.2.2.2
  refine Integrable.mono' (hint.mul_const (‖u‖ * ‖v‖))
    (s101_Dm_entries_meas A hT u v).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
  rw [Real.norm_eq_abs]
  exact s101_abs_le_tn (s101_Dm_bdd A hT hτ) u v

lemma s101_Dm_cases (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) (τ : ℝ) :
    s101Dm C m T z τ = s101D C m T z τ ∨ s101Dm C m T z τ = 0 := by
  obtain ⟨G, hG, hDm⟩ := s101_Dm_spec A hT
  rw [hDm]
  by_cases h : τ ∈ G
  · left; simp [h]
  · right; simp [h]

variable (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ T → ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ, IsR2DualCombo m φ →
    IsR2DualCombo m ψ → propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)

include hlin in
lemma s101_Dm_Pc_zero (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (htτ : t ≤ τ) (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ)
    (v : KSpace d m T) : s101Dm C m T z τ (s101Pc m T t S a) v = 0 := by
  obtain ⟨c, hD⟩ := s101_data_of_horb A.hd A.horb
  have hD0 : s101D C m T z τ (s101Pc m T t S a) v = 0 := by
    have := s101_D_congr_left A hτ (u := s101Pc m T t S a) (u' := 0) (fun x => by
      rw [s101g_Pc hlin hD hτ ht S a x, if_neg (not_lt.2 htτ), inner_zero_right]) v
    rw [this]; simp
  rcases s101_Dm_cases A hT τ with h | h
  · rw [h]; exact hD0
  · rw [h]; rfl

include hlin in
lemma s101_Dm_Pc_zero' (A : S101Adm C m T r Pw z) (hT : 0 ≤ T) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (htτ : t ≤ τ) (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ)
    (v : KSpace d m T) : s101Dm C m T z τ v (s101Pc m T t S a) = 0 := by
  obtain ⟨c, hD⟩ := s101_data_of_horb A.hd A.horb
  have hD0 : s101D C m T z τ v (s101Pc m T t S a) = 0 := by
    rw [s101_D_symm A hτ]
    have := s101_D_congr_left A hτ (u := s101Pc m T t S a) (u' := 0) (fun x => by
      rw [s101g_Pc hlin hD hτ ht S a x, if_neg (not_lt.2 htτ), inner_zero_right]) v
    rw [this]; simp
  rcases s101_Dm_cases A hT τ with h | h
  · rw [h]; exact hD0
  · rw [h]; rfl

end HRS.MS.CovMeas
