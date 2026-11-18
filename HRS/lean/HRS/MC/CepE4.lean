import HRS.MC.CepE4Aux6

/-!
# Packet CEPE4: uniform `L¹` a priori bound on the singular force (`cep_E4_L1_bound`)

`HRS.MC.CepE4.cep_E4_L1_bound_proof` has the statement of `HRS.MC.Cepa.cep_E4_L1_bound`.
Route (the repaired one): Lyapunov function `V(z) = ½|z - ρ|²`, `ρ_k = k/N`.  On the alcove
`⟨x - ρ, ∇Φ(x)⟩ ≥ -K₁` and `∑_k |∂_kΦ(x)| ≤ 8N ⟨x - ρ, ∇Φ(x)⟩ + K₂` (`CepE4Aux1`), and for the Yosida
approximation `⟨z - ρ, G_n z⟩ = ⟨J_n z - ρ, ∇Φ(J_n z)⟩ + |G_n z|²/n`.  The expectation of Itô's formula for `V(Z^n)`
(`CepE4Aux4`, proved by elementary means from the independence of the noise increments) plus Grönwall for
`E V(Z^n_t)` give the bound (`CepE4Aux6`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE4

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- Pointwise properties of the Yosida force `G_n z = n (z - J_n z)`. -/
theorem e4_yosida_pointwise {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J) {n : ℝ}
    (hn : 0 < n) (z : Ch N) :
    -(2 * Real.pi * a * (N : ℝ) ^ 2) ≤ inner ℝ (z - e4_rho N) (n • (z - J n z)) ∧
    ∑ k, |(n • (z - J n z)) k| ≤ 8 * N * inner ℝ (z - e4_rho N) (n • (z - J n z)) +
      16 * Real.pi * N * a * (N : ℝ) ^ 2 := by
  have hf := hJ.force n z hn
  have hmem := hJ.mem n z hn
  obtain ⟨h1, h2⟩ := e4_pointwise ha hmem
  rw [← hf] at h1 h2
  have hz : z - e4_rho N = (J n z - e4_rho N) + n⁻¹ • (n • (z - J n z)) := by
    rw [smul_smul, inv_mul_cancel₀ hn.ne', one_smul]
    abel
  have hinner : inner ℝ (z - e4_rho N) (n • (z - J n z)) =
      inner ℝ (J n z - e4_rho N) (n • (z - J n z)) + n⁻¹ * ‖n • (z - J n z)‖ ^ 2 := by
    rw [hz, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hnn : 0 ≤ n⁻¹ * ‖n • (z - J n z)‖ ^ 2 := by positivity
  constructor
  · rw [hinner]; linarith
  · have hN : (0 : ℝ) ≤ 8 * N := by positivity
    rw [hinner]
    nlinarith

theorem e4_lip_growth {f : Ch N → Ch N} {K : ℝ≥0} (hf : LipschitzWith K f) (z : Ch N) :
    ‖f z‖ ≤ ‖f 0‖ + (K : ℝ) * ‖z‖ := by
  have h := hf.dist_le_mul z 0
  rw [dist_eq_norm, dist_eq_norm, sub_zero] at h
  have := norm_le_insert' (f z) (f 0)
  have h2 : ‖f z‖ ≤ ‖f z - f 0‖ + ‖f 0‖ := by
    have := norm_le_norm_add_norm_sub' (f z) (f 0)
    linarith
  linarith

theorem e4_F_pointwise {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (ρ z : Ch N) :
    inner ℝ (z - ρ) (F z) ≤ (1 / 2) * ‖F ρ‖ ^ 2 + (1 + 2 * (L : ℝ)) * ((1 / 2) * ‖z - ρ‖ ^ 2) := by
  have h := hF.dist_le_mul z ρ
  rw [dist_eq_norm, dist_eq_norm] at h
  have h1 : ‖F z‖ ≤ ‖F ρ‖ + L * ‖z - ρ‖ := by
    have := norm_le_norm_add_norm_sub' (F z) (F ρ)
    linarith
  have h2 := real_inner_le_norm (z - ρ) (F z)
  have h3 : ‖z - ρ‖ * ‖F z‖ ≤ ‖z - ρ‖ * (‖F ρ‖ + L * ‖z - ρ‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  have hL : (0 : ℝ) ≤ L := L.2
  nlinarith [sq_nonneg (‖z - ρ‖ - ‖F ρ‖), norm_nonneg (z - ρ), norm_nonneg (F ρ)]

theorem cep_E4_L1_bound_proof [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {π : Ω → Equiv.Perm (Fin N)} (hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ})
    {a : ℝ} (ha : 0 < a) {J : ℝ → Ch N → Ch N} (hJ : cep_Yosida a N J)
    {F : Ch N → Ch N} {L : ℝ≥0} (hF : LipschitzWith L F) (σ' : ℝ)
    {z₀ : Ω → Ch N} (hz₀ : Measurable[ℱ 0] z₀) (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R)
    {Z : ℕ → ℝ → Ω → Ch N}
    (hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n)) (T : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∫ ω, (∫ s in (0 : ℝ)..T, ∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k|) ∂P ≤ C := by
  obtain ⟨R, hR⟩ := hz₀b
  set ρ : Ch N := e4_rho N with hρ
  set K1 : ℝ := 2 * Real.pi * a * (N : ℝ) ^ 2 with hK1
  set K2 : ℝ := 16 * Real.pi * N * a * (N : ℝ) ^ 2 with hK2
  set cF1 : ℝ := (1 / 2) * ‖F ρ‖ ^ 2 with hcF1
  set cF2 : ℝ := 1 + 2 * (L : ℝ) with hcF2
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  have hc1p : 0 ≤ cF1 := by positivity
  have hLp : (0 : ℝ) ≤ L := L.2
  have hc2p : 0 ≤ cF2 := by positivity
  refine ⟨max 0 (e4_bound N R ‖ρ‖ σ' (max T 0) K1 K2 cF1 cF2), fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rcases le_or_gt 0 T with hT | hT
  · refine le_trans ?_ (le_max_right _ _)
    obtain ⟨hZc, hZF, heq⟩ := hZ n hn
    set G : Ch N → Ch N := fun z => (n : ℝ) • (z - J n z) with hG
    have hGlip := hJ.lip n hnpos
    have hGc : Continuous G := hGlip.continuous
    have hFc : Continuous F := hF.continuous
    have hGb : ∀ z, ‖G z‖ ≤ ‖G 0‖ + ((Real.toNNReal n : ℝ≥0) : ℝ) * ‖z‖ := fun z => e4_lip_growth hGlip z
    have hFb : ∀ z, ‖F z‖ ≤ ‖F 0‖ + (L : ℝ) * ‖z‖ := fun z => e4_lip_growth hF z
    have hBc : Continuous fun z => -G z + F z := hGc.neg.add hFc
    have hBb : ∀ z, ‖-G z + F z‖ ≤ (‖G 0‖ + ‖F 0‖) + (((Real.toNNReal n : ℝ≥0) : ℝ) + L) * ‖z‖ := fun z => by
      have h1 := norm_add_le (-G z) (F z)
      rw [norm_neg] at h1
      have h2 := hGb z
      have h3 := hFb z
      nlinarith
    obtain ⟨A, hS⟩ := e4_setup_of_solution hW' hπ (σ' := σ') hR hBc (by positivity) (by positivity) hBb
      (Z := Z n) hZc hZF heq hT
    have hS' : E4Setup P ℱ N T σ' (cep_noise π W') (e4_clamp (Z n)) A := hS
    have heq' : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → e4_clamp (Z n) t ω = z₀ ω +
        (∫ s in (0 : ℝ)..t, (-G (e4_clamp (Z n) s ω) + F (e4_clamp (Z n) s ω))) + σ' • cep_noise π W' t ω := by
      filter_upwards [heq] with ω hω t ht
      have e1 : e4_clamp (Z n) t ω = Z n t ω := by simp [e4_clamp, max_eq_left ht]
      rw [e1, hω t ht]
      congr 2
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [Set.uIcc_of_le ht] at hs
      simp [e4_clamp, max_eq_left hs.1, hG]
    have key := e4_uniform hS' hz₀ hR ρ hGc hFc (by positivity) (by positivity) (by positivity) hLp hGb hFb
      heq' hK1p hK2p hc1p hc2p (fun z => by
        have := (e4_yosida_pointwise ha hJ hnpos z).1
        simpa [hG, hK1] using this)
      (fun z => by
        have := (e4_yosida_pointwise ha hJ hnpos z).2
        simpa [hG, hK2] using this)
      (fun z => e4_F_pointwise hF ρ z) hT
    have hmax : max T 0 = T := max_eq_left hT
    rw [hmax]
    refine le_trans (le_of_eq ?_) key
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le hT] at hs
    simp [e4_clamp, max_eq_left hs.1, hG]
  · refine le_trans ?_ (le_max_left _ _)
    have : ∀ ω, (∫ s in (0 : ℝ)..T, ∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k|) ≤ 0 := by
      intro ω
      rw [intervalIntegral.integral_symm]
      have : 0 ≤ ∫ s in T..(0 : ℝ), ∑ k : Fin N, |((n : ℝ) • (Z n s ω - J n (Z n s ω))) k| :=
        intervalIntegral.integral_nonneg hT.le fun s _ => Finset.sum_nonneg fun k _ => abs_nonneg _
      linarith
    exact integral_nonpos fun ω => this ω

end HRS.MC.CepE4
