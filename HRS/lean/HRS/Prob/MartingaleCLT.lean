import HRS.Prob.MartingaleLindeberg

/-!
# Lemma A.21 (package CLT-01)

`HRS.multivariate_martingale_clt` and `HRS.multivariate_martingale_clt_dc2`
(Lemma A.21 `M:B:lem:lindeberg`, source lines 10545-10551) assembled from
`lindeberg_partition_bound`, `martingale_lindeberg_tendsto` and `gaussian_lindeberg_tendsto` in
`HRS/Prob/MartingaleLindeberg.lean` (they live here because that file imports `CLT.lean`).
Route: mollify `h` by `gaussSmooth h (ε² I)` (Lipschitz Hessian, uniform cost `½ H ε² p`),
apply the partition bound, let `n → ∞`, then `ε → 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

section Multivariate

variable {p : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open LindebergAux

/-- Lemma A.21 `M:B:lem:lindeberg` (lines 10545-10551), bound `B:eq:lindeberg-bound`: for
deterministic integrable symmetric nonnegative `sb : [0,t] → ℝ^{p×p}` and
`G ∼ N(0, ∫_0^t sb)`, for every `h ∈ C²(ℝ^p)` with bounded second derivatives,
`|E h(M_t) - E h(G)| ≤ ½ sup_x ‖∇²h(x)‖_op E ∫_0^t ‖Σ_σ - sb_σ‖_{S_1} dσ`. -/
theorem multivariate_martingale_clt (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef)
    (h : (ℝ^p) → ℝ) (hh : ContDiff ℝ 2 h)
    (hbdd : BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ 2 h x‖)) :
    |∫ ω, h (M t ω) ∂P -
        ∫ x, h x ∂(ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun i j => ∫ σ in Set.Icc 0 t, sb σ i j))| ≤
      (1 / 2) * (⨆ x, ‖iteratedFDeriv ℝ 2 h x‖) *
        ∫ ω, (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ)) ∂P := by
  classical
  have hcov : (Matrix.of fun i j => ∫ σ in Set.Icc 0 t, sb σ i j) = covBlock sb 0 t := rfl
  rw [hcov]
  set H := ⨆ x, ‖iteratedFDeriv ℝ 2 h x‖ with hHdef
  have hH : ∀ x, ‖iteratedFDeriv ℝ 2 h x‖ ≤ H := fun x => le_ciSup hbdd x
  have hH0 : 0 ≤ H := (norm_nonneg _).trans (hH 0)
  have hent := sb_entry_integrableOn hsbmeas hsbint hsbpsd
  have hGpsd : (covBlock sb 0 t).PosSemidef := covBlock_psd hsbpsd hent le_rfl le_rfl
  set γ := ProbabilityTheory.multivariateGaussian (0 : ℝ^p) (covBlock sb 0 t) with hγ
  set J := ∫ ω, (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ)) ∂P with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun ω =>
    setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  have hmt : MemLp (M t) 2 P := hM.sq_int t ⟨ht, le_rfl⟩
  have hγm : MemLp (id : (ℝ^p) → (ℝ^p)) 2 γ := ProbabilityTheory.IsGaussian.memLp_two_id
  have key : ∀ ε : ℝ, 0 < ε →
      |∫ ω, h (M t ω) ∂P - ∫ x, h x ∂γ| ≤ (1 / 2) * H * J + H * (ε ^ 2 * p) := by
    intro ε hε
    set Qe : Matrix (Fin p) (Fin p) ℝ := ε ^ 2 • (1 : Matrix (Fin p) (Fin p) ℝ) with hQe
    have hQpd : Qe.PosDef := Matrix.PosDef.one.smul (by positivity)
    obtain ⟨happ, L, hL⟩ := gaussSmooth_approx Qe hQpd h hh H hH
    have hQtr : Qe.trace = ε ^ 2 * p := by simp [hQe, Matrix.trace_smul]
    obtain ⟨he2, heH, -⟩ := gaussSmooth_hessian Qe hQpd.posSemidef h hh H hH
    have hL' : ∀ x y, ‖iteratedFDeriv ℝ 2 (gaussSmooth h Qe) x -
        iteratedFDeriv ℝ 2 (gaussSmooth h Qe) y‖ ≤ max L 0 * ‖x - y‖ := fun x y =>
      (hL x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    set δ := (1 / 2) * H * (ε ^ 2 * p) with hδdef
    have hδ : ∀ x, |gaussSmooth h Qe x - h x| ≤ δ := fun x => by
      have := happ x
      rwa [hQtr] at this
    have iP1 : Integrable (fun ω => h (M t ω)) P := integrable_comp_memLp P hh hH hmt
    have iP2 : Integrable (fun ω => gaussSmooth h Qe (M t ω)) P :=
      integrable_comp_memLp P he2 heH hmt
    have iG1 : Integrable h γ := integrable_comp_memLp γ hh hH hγm
    have iG2 : Integrable (gaussSmooth h Qe) γ := integrable_comp_memLp γ he2 heH hγm
    have d1 : |∫ ω, h (M t ω) ∂P - ∫ ω, gaussSmooth h Qe (M t ω) ∂P| ≤ δ := by
      rw [← integral_sub iP1 iP2, ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le (μ := P) (integrable_const δ)
        (f := fun ω => h (M t ω) - gaussSmooth h Qe (M t ω))
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_sub_comm]; exact hδ _)
      simpa using this
    have d2 : |∫ x, h x ∂γ - ∫ x, gaussSmooth h Qe x ∂γ| ≤ δ := by
      rw [← integral_sub iG1 iG2, ← Real.norm_eq_abs]
      have := norm_integral_le_of_norm_le (μ := γ) (integrable_const δ)
        (f := fun x => h x - gaussSmooth h Qe x)
        (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_sub_comm]; exact hδ _)
      simpa using this
    have hL0 : 0 ≤ max L 0 := le_max_right _ _
    have hS := martingale_lindeberg_tendsto P ℱ t ht M Sg hM H (max L 0) hH0 hL0
    have hG := gaussian_lindeberg_tendsto t ht sb hsbmeas hsbint hsbpsd H (max L 0) hH0 hL0
    have hlim : Tendsto (fun n : ℕ => (1 / 2) * H * J + 2 * δ +
        ((∑ k ∈ Finset.range n, ∫ ω, taylorRem H (max L 0)
            (M (unifPart t n (k + 1)) ω - M (unifPart t n k) ω) ∂P) +
         ∑ k ∈ Finset.range n, ∫ y, taylorRem H (max L 0) y ∂(ProbabilityTheory.multivariateGaussian 0
          (covBlock sb (unifPart t n k) (unifPart t n (k + 1)))))) atTop
        (𝓝 ((1 / 2) * H * J + 2 * δ + (0 + 0))) :=
      tendsto_const_nhds.add (hS.add hG)
    have hfin : |∫ ω, h (M t ω) ∂P - ∫ x, h x ∂γ| ≤ (1 / 2) * H * J + 2 * δ + (0 + 0) := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hb := lindeberg_partition_bound P ℱ t ht M Sg hM sb hsbmeas hsbint hsbpsd
        (gaussSmooth h Qe) he2 H (max L 0) heH hL' n hn
      rw [Finset.sum_add_distrib] at hb
      have e : ∫ ω, h (M t ω) ∂P - ∫ x, h x ∂γ =
          (∫ ω, gaussSmooth h Qe (M t ω) ∂P - ∫ x, gaussSmooth h Qe x ∂γ) +
            (∫ ω, h (M t ω) ∂P - ∫ ω, gaussSmooth h Qe (M t ω) ∂P) -
            (∫ x, h x ∂γ - ∫ x, gaussSmooth h Qe x ∂γ) := by ring
      rw [e]
      have a1 := abs_le.1 hb
      have a2 := abs_le.1 d1
      have a3 := abs_le.1 d2
      rw [abs_le]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
    have : 2 * δ = H * (ε ^ 2 * p) := by rw [hδdef]; ring
    linarith
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hpos : 0 < H * p + 1 := by positivity
  set ε := Real.sqrt (η / (H * p + 1)) with hεdef
  have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
  have hε2 : ε ^ 2 = η / (H * p + 1) := Real.sq_sqrt (by positivity)
  have := key ε hε
  have h3 : H * (ε ^ 2 * p) ≤ η := by
    rw [hε2]
    have : H * (η / (H * p + 1) * p) = η * (H * p) / (H * p + 1) := by field_simp
    rw [this, div_le_iff₀ hpos]
    nlinarith [mul_nonneg hH0 (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  have hpos' : (1 / 2) * H * J ≥ 0 := by positivity
  linarith

/-- Lemma A.21, consequence: `d_{C²}(Law M_t, Law G) ≤ ½ E ∫_0^t ‖Σ - sb‖_{S_1}`. -/
theorem multivariate_martingale_clt_dc2 (ℱ : Filtration ℝ mΩ) (t : ℝ) (ht : 0 ≤ t)
    (M : ℝ → Ω → (ℝ^p)) (Sg : ℝ → Ω → Matrix (Fin p) (Fin p) ℝ)
    (hM : IsVectorMartingaleWithCovariation P ℱ t M Sg)
    (sb : ℝ → Matrix (Fin p) (Fin p) ℝ) (hsbmeas : Measurable sb)
    (hsbint : IntegrableOn (fun σ => s1Norm (sb σ)) (Set.Icc 0 t))
    (hsbpsd : ∀ σ ∈ Set.Icc 0 t, (sb σ).PosSemidef) :
    smoothDist 2 (law P (M t)) (ProbabilityTheory.multivariateGaussian 0 (Matrix.of fun i j => ∫ σ in Set.Icc 0 t, sb σ i j)) ≤
      (1 / 2) * ∫ ω, (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ)) ∂P := by
  classical
  have hmt : AEMeasurable (M t) P := (hM.sq_int t ⟨ht, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hJ0 : 0 ≤ ∫ ω, (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ)) ∂P :=
    integral_nonneg fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
  refine Real.iSup_le (fun Φ => ?_) (by positivity)
  obtain ⟨hΦ, hbd, hnorm⟩ := Φ.2
  have h2 := hbd 2 le_rfl
  have hle : (⨆ x, ‖iteratedFDeriv ℝ 2 Φ.1 x‖) ≤ 1 := by
    refine le_trans ?_ hnorm
    unfold cbNorm
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    have a0 : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 Φ.1 z‖ := Real.iSup_nonneg fun _ => norm_nonneg _
    have a1 : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 1 Φ.1 z‖ := Real.iSup_nonneg fun _ => norm_nonneg _
    linarith
  have hmain := multivariate_martingale_clt P ℱ t ht M Sg hM sb hsbmeas hsbint hsbpsd Φ.1 hΦ h2
  have hH0 : 0 ≤ ⨆ x, ‖iteratedFDeriv ℝ 2 Φ.1 x‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  have e : ∫ z, Φ.1 z ∂(law P (M t)) = ∫ ω, Φ.1 (M t ω) ∂P :=
    integral_map hmt hΦ.continuous.aestronglyMeasurable
  rw [e]
  refine hmain.trans ?_
  have : (⨆ x, ‖iteratedFDeriv ℝ 2 Φ.1 x‖) * ∫ ω, (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ)) ∂P ≤
      1 * ∫ ω, (∫ σ in Set.Icc 0 t, s1Norm (Sg σ ω - sb σ)) ∂P :=
    mul_le_mul_of_nonneg_right hle hJ0
  nlinarith

end Multivariate

end HRS

end
