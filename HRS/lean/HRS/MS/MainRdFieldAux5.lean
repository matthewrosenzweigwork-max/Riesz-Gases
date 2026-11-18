import HRS.MS.MainRdFieldAux4
import HRS.MH.DualityRdFinal
import HRS.MS.GenPathAux13

/-!
# S.A.6, packet P4: the `H^{-Γ}`-valued decomposition `σΞ = I_emp + M_t + R` at one time

* `sa6_hilbert_version`: the continuous `H`-valued martingale of a bounded progressive integrand over a finite index set
  (as `mrm_hilbert_version`, additionally exporting `IsHilbertItoIntegral`);
* `sa6_M_pairing`: its pairing with a smooth test is the real Itô integral of the paired integrand;
* `sa6_pairing_identity`: for every smooth test and a.e. `ζ`,
  `⟨φ, Ξ - I' - M_t⟩ = (σ/2) ∫_0^t Comm_N(Mᵀ∇U^{r,t}φ; X_r, ρ_r) dr` (the duality identity `duality_identity_rd`);
* `sa6_remainder_pathwise`, `sa6_remainder_L1`: `‖R‖ ≤ (σ/2) K' ∫_0^T (F + o + e) dr` and `E‖R‖ ≤ ½ K' σ T (𝔈 + e)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MS.GenPath HRS.MH.DualityRd

variable {d : ℕ}

/-! ### Elementary facts -/

lemma sa6_cb_mono {f : Euc d → ℝ} {j n : ℕ} (hjn : j ≤ n) : cbNorm j f ≤ cbNorm n f := by
  unfold cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
    fun i _ _ => Real.iSup_nonneg fun w => norm_nonneg _

lemma sa6_ws_mono {r r' : ℕ} (hr : r' ≤ r) (L : ℝ) (f : Euc d → ℝ) :
    weightedSupE r' L f ≤ weightedSupE r L f := by
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
  exact le_iSup_of_le (⟨(j : ℕ), by have := j.2; omega⟩ : Fin (r + 1))
    (le_iSup_of_le i (le_iSup_of_le x le_rfl))

lemma sa6_regular_mono {s Λ T : ℝ} {r r' : ℕ} {ρ : ℝ → Euc d → ℝ} (h : IsRegularMFRd s r Λ T ρ)
    (hr : r' ≤ r) : IsRegularMFRd s r' Λ T ρ := by
  unfold IsRegularMFRd at h ⊢
  refine ⟨fun t ht => ?_, h.2⟩
  obtain ⟨hmem, hws, hle⟩ := h.1 t ht
  refine ⟨⟨hmem.1.of_le (by exact_mod_cast hr), fun j hj => hmem.2 j (hj.trans hr)⟩,
    lt_of_le_of_lt (sa6_ws_mono hr _ _) hws, ?_⟩
  have h1 := sa6_cb_mono (f := ρ t) hr
  have h2 : (weightedSupE r' ((d : ℝ) + 3) (ρ t)).toReal ≤ (weightedSupE r ((d : ℝ) + 3) (ρ t)).toReal :=
    ENNReal.toReal_mono hws.ne (sa6_ws_mono hr _ _)
  linarith

lemma sa6_classical_prop {Cf : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ}
    (h : ∃ f, IsClassicalAdjointW Cf t φ f) :
    IsClassicalAdjointW Cf t φ (fun r => propagatorW Cf r t φ) := by
  have : (fun r => propagatorW Cf r t φ) = h.choose := by
    funext r; unfold propagatorW; rw [dif_pos h]
  rw [this]; exact h.choose_spec

/-- `c_N = σ_N √(2 β_N⁻¹) / N`. -/
def sa6_cN (S : WholeMainData d) (N : ℕ) : ℝ := S.sigma N * Real.sqrt (2 * S.invβ N) / N

lemma sa6_sigma_nonneg (S : WholeMainData d) (N : ℕ) : 0 ≤ S.sigma N := mrr_sigma_nonneg S N

lemma sa6_cN_sq (S : WholeMainData d) {N : ℕ} (hN : 0 < N) :
    sa6_cN S N ^ 2 * N = 2 * S.qN N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hν := S.hinvβ N
  unfold sa6_cN WholeMainData.qN qScale
  by_cases h0 : S.invβ N = 0
  · rw [h0]; simp
  · rw [if_neg h0, div_pow, mul_pow, Real.sq_sqrt (by linarith)]
    field_simp
    rfl

lemma sa6_q_le_one (S : WholeMainData d) {N : ℕ} (hN : 0 < N) : S.qN N ≤ 1 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hν := S.hinvβ N
  unfold WholeMainData.qN qScale
  by_cases h0 : S.invβ N = 0
  · rw [h0]; simp
  · rw [if_neg h0]
    have hνp : 0 < S.invβ N := lt_of_le_of_ne hν (Ne.symm h0)
    have hσ : S.sigma N ≤ Real.sqrt (N / S.invβ N) := by
      unfold WholeMainData.sigma sigmaScale
      rw [if_neg h0]
      exact min_le_right _ _
    have hσ0 := sa6_sigma_nonneg S N
    have h2 : S.sigma N ^ 2 ≤ N / S.invβ N := by
      calc S.sigma N ^ 2 ≤ Real.sqrt (N / S.invβ N) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
        _ = N / S.invβ N := Real.sq_sqrt (by positivity)
    rw [div_le_one hNp]
    calc S.sigma N ^ 2 * S.invβ N ≤ (N / S.invβ N) * S.invβ N := mul_le_mul_of_nonneg_right h2 hν
      _ = N := by field_simp

/-! ### The Hilbert-valued martingale -/

section HilbertIto

variable {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  {κ : Type} [Fintype κ]

open HRS.GF HRS.Uniform.Q07c in
theorem sa6_hilbert_version {W' : ℝ≥0 → Ω → κ → ℝ} (hW : IsBrownianFiltration P ℱ W')
    {Z : ℝ → Ω → κ → H} (hZ : ∀ T', IsHSIntegrand P ℱ T' Z) :
    ∃ M : ℝ → Ω → H, (∀ ω, Continuous fun τ => M τ ω) ∧ (∀ τ, Measurable[ℱ τ] (M τ)) ∧
      (∀ T', IsHilbertMartingaleWithCovariation P ℱ T' M (fun r ω => hsCovForm (Z r ω))) ∧
      IsHilbertItoIntegral P ℱ W' Z M ∧
      ∀ (x : H) (τ : ℝ), 0 ≤ τ → (fun ω => inner ℝ (M τ ω) x) =ᵐ[P]
        itoIntegral P ℱ W' (fun r ω k => inner ℝ (Z r ω k) x) τ := by
  have hWc : IsCylindricalBrownian P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hW
  obtain ⟨Mart, hc, had, hz, hJ⟩ := gfb3_exists_hilbert_version hWc hZ
  have hMart : IsHilbertItoIntegral P ℱ W' Z Mart := by
    refine ⟨hc, had, hz, ?_⟩
    intro τ hτ x
    obtain ⟨J, hIJ, hae⟩ := hJ x
    refine (hIJ.approx τ hτ).congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hae τ hτ] with ω h
    rw [h]
    rfl
  refine ⟨Mart, hc, had, fun T' => isHM_of_ito hWc hZ hc had hz hJ T', hMart, fun x τ hτ => ?_⟩
  exact gfb3_pair_ito hW hMart x (pc_isProgressiveL2_inner hZ x Finset.univ) hτ

end HilbertIto

lemma sa6_tau_prog {Ω : Type} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ mΩ) (T : ℝ) :
    IsProgressive ℱ (fun (r : ℝ) (ζ : Ω) => if r ≤ (fun _ : Ω => T) ζ ∨ T < r then (1 : ℝ) else 0) := by
  have : (fun (r : ℝ) (ζ : Ω) => if r ≤ (fun _ : Ω => T) ζ ∨ T < r then (1 : ℝ) else 0) =
      fun _ _ => (1 : ℝ) := by
    funext r ζ
    have : r ≤ T ∨ T < r := le_or_gt r T
    simp [this]
  rw [this]
  exact isProgressive_const ℱ 1

section MExists

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {N : ℕ} {Γ : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}

theorem sa6_Z_hs {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    (hK : Sa6Kern (S.coeff N) S.T Γ C₁ Kern) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (T' : ℝ) :
    IsHSIntegrand (R N).P ℱ T'
      (mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X) :=
  mrm_isHS_of_bdd (fun ia => sa6_Z_progressive hK (sa6_cN S N) ht.2 (fun _ => S.T) (R N).X
    hF.progressive (sa6_tau_prog ℱ S.T) ia) (|sa6_cN S N| * C₁)
    (fun r ζ ia => sa6_Z_norm hK (sa6_cN S N) ht.2 (fun _ => S.T) (R N).X r ζ ia) T'

theorem sa6_M_exists {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    (hK : Sa6Kern (S.coeff N) S.T Γ C₁ Kern) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) :
    ∃ M : ℝ → (R N).Ω → HNeg d (Γ : ℝ), (∀ τ, Measurable[ℱ τ] (M τ)) ∧
      (∀ T', IsHilbertMartingaleWithCovariation (R N).P ℱ T' M
        (fun r ω => hsCovForm (mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X r ω))) ∧
      IsHilbertItoIntegral (R N).P ℱ W' (mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X) M ∧
      ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
        HNeg.pairing φ (M t ζ) = itoIntegral (R N).P ℱ W'
          (mrmPhi (S.coeff N) (sa6_cN S N) t (fun _ => S.T) (R N).X φ) t ζ := by
  obtain ⟨M, hc, had, hM, hIto, hpair⟩ :=
    sa6_hilbert_version hF.brownian (sa6_Z_hs hF hK ht)
  refine ⟨M, had, hM, hIto, fun φ hφ => ?_⟩
  obtain ⟨g, hg⟩ := mrm_riesz hφ
  have hint : (fun r ω ia => inner ℝ (mrmZ Kern (sa6_cN S N) t (fun _ => S.T) (R N).X r ω ia) g) =
      mrmPhi (S.coeff N) (sa6_cN S N) t (fun _ => S.T) (R N).X φ := by
    funext r ω ia
    rw [real_inner_comm, hg, sa6_Z_pair hK (sa6_cN S N) ht.2 (fun _ => S.T) (R N).X hφ]
  filter_upwards [hpair g t ht.1] with ζ hζ
  rw [← hg, real_inner_comm]
  rw [hint] at hζ
  exact hζ

end MExists

end HRS.MS.MainRdField
