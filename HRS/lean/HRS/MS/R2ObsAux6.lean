import HRS.MS.R2ObsAux5
import HRS.MS.R2IidPathTie

/-!
# S9.10 path row, packet 6: the covariance of the path Gaussian

Worker S910, namespace `HRS.MS.R2Obs`.  `K = s11p_K d = ℓ²(ℕ × ℕ^d)`.

* `s910_gauss_int`: `E⟨a,z⟩⟨b,z⟩ = covarianceBilin G a b` for a centered Gaussian `G` on `K`, with integrability;
* `s910_hasSum_fiber`: a vector supported on the fibre `{(n,α)}` is the series `∑_n A_n b_{(n,α)}` of basis vectors;
* `s910_cov_expand`: `covarianceBilin G u v = ∑_n A_n ∑_m A'_m covarianceBilin G b_{(n,α)} b_{(m,α')}`;
* `s910_susc_smul`: `C(cφ, cψ) = c² C(φ,ψ)`;
* `s910_path_cov`: `E⟨v_{t,α},z⟩⟨v_{t',α'},z⟩ = C(U^{0,t}φ_α, U^{0,t'}φ_{α'})` for the Gaussian `G` of the scaled orbit features.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

noncomputable section

namespace HRS.MS.R2Obs

open S99 S45 HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d : ℕ}

theorem s910_gauss_int {G : Measure (s11p_K d)} [IsProbabilityMeasure G] (hg : HRS.IsCenteredGaussian G)
    (a b : s11p_K d) :
    Integrable (fun z : s11p_K d => inner ℝ a z * inner ℝ b z) G ∧
      ∫ z, inner ℝ a z * inner ℝ b z ∂G = covarianceBilin G a b := by
  haveI := hg.1
  have hmem : MemLp id 2 G := ProbabilityTheory.IsGaussian.memLp_two_id
  have hn : Integrable (fun z : s11p_K d => ‖z‖ ^ 2) G := by
    have := hmem.integrable_norm_pow (p := 2) (by norm_num)
    simpa using this
  have hint : Integrable (fun F : s11p_K d => inner ℝ a F * inner ℝ b F) G := by
    refine (hn.const_mul (‖a‖ * ‖b‖)).mono' ?_ (Filter.Eventually.of_forall fun F => ?_)
    · exact ((continuous_const.inner continuous_id).mul
        (continuous_const.inner continuous_id)).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖inner ℝ a F‖ * ‖inner ℝ b F‖ ≤ (‖a‖ * ‖F‖) * (‖b‖ * ‖F‖) :=
            mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _) (norm_nonneg _)
              (by positivity)
        _ = ‖a‖ * ‖b‖ * ‖F‖ ^ 2 := by ring
  refine ⟨hint, ?_⟩
  rw [covarianceBilin_apply hmem, HRS.HilbertCLTAux.gaussian_mean_zero hg]
  simp

theorem s910_c_eq (z : s11p_K d) (q : ℕ × MultiIndex d) :
    z.c q = inner ℝ (s11p_basis0 d q : s11p_K d) z := by
  rw [s11p_basis0_apply]
  exact s11p_c_eq_inner z q

theorem s910_hasSum_fiber (u : s11p_K d) (α : MultiIndex d) (A : ℕ → ℝ)
    (hu : ∀ q : ℕ × MultiIndex d, u.c q = if q.2 = α then A q.1 else 0) :
    HasSum (fun n : ℕ => A n • (s11p_basis0 d (n, α) : s11p_K d)) u := by
  classical
  have h := (s11p_basis0 d).hasSum_repr u
  have h' : HasSum (fun q => u.c q • (s11p_basis0 d q : s11p_K d)) u := by
    convert h using 2 with q
    rw [HilbertBasis.repr_apply_apply, ← s910_c_eq]
  have hinj : Function.Injective (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) :=
    fun a b hab => by simpa using hab
  have hz : ∀ q ∉ Set.range (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)),
      u.c q • (s11p_basis0 d q : s11p_K d) = 0 := by
    intro q hq
    have : q.2 ≠ α := fun h => hq ⟨q.1, Prod.ext rfl h.symm⟩
    rw [hu q, if_neg this, zero_smul]
  have h2 := (hinj.hasSum_iff hz).2 h'
  convert h2 using 2 with n
  simp only [Function.comp, hu (n, α), if_true]

theorem s910_cov_expand {G : Measure (s11p_K d)} (α α' : MultiIndex d) (A A' : ℕ → ℝ) (u v : s11p_K d)
    (hu : ∀ q : ℕ × MultiIndex d, u.c q = if q.2 = α then A q.1 else 0)
    (hv : ∀ q : ℕ × MultiIndex d, v.c q = if q.2 = α' then A' q.1 else 0) :
    covarianceBilin G u v = ∑' n, A n * ∑' m, A' m *
      covarianceBilin G (s11p_basis0 d (n, α) : s11p_K d) (s11p_basis0 d (m, α') : s11p_K d) := by
  have h1 := (s910_hasSum_fiber u α A hu).mapL ((covarianceBilin G).flip v)
  have e1 : covarianceBilin G u v =
      ∑' n, A n * covarianceBilin G (s11p_basis0 d (n, α) : s11p_K d) v := by
    have := h1.tsum_eq
    simp only [ContinuousLinearMap.flip_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at this
    exact this.symm
  have e2 : ∀ n, covarianceBilin G (s11p_basis0 d (n, α) : s11p_K d) v = ∑' m, A' m *
      covarianceBilin G (s11p_basis0 d (n, α) : s11p_K d) (s11p_basis0 d (m, α') : s11p_K d) := fun n => by
    have h2 := (s910_hasSum_fiber v α' A' hv).mapL (covarianceBilin G (s11p_basis0 d (n, α) : s11p_K d))
    have := h2.tsum_eq
    simp only [map_smul, smul_eq_mul] at this
    exact this.symm
  rw [e1]
  exact tsum_congr fun n => by rw [e2 n]

theorem s910_term_bound {T : ℝ} (hT : 0 < T) (n : ℕ) (t : ℝ) :
    |s11p_kap n * r2CosBasis T n t| ≤ Real.sqrt (2 / T) := by
  rw [abs_mul, abs_of_pos (s11p_kap_pos n)]
  calc s11p_kap n * |r2CosBasis T n t| ≤ 1 * Real.sqrt (2 / T) :=
        mul_le_mul (s11p_kap_le_one n) (s11p_cos_bound hT n t) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

section Path

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ)

include hd hs0 hsd ha hβ hγ

theorem s910_susc_smul {φ ψ : Euc d → ℝ} (hψ : MemCb (J1 d) ψ) (c : ℝ) :
    HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ (fun x => c * φ x) (fun x => c * ψ x) =
      c ^ 2 * HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ φ ψ := by
  have hψ' : MemCb (J1 d) (fun x => c * ψ x) := (HRS.MS.Tc5.tc5_cb_smul c hψ).1
  rw [s910_susc_eq hd hs0 hsd ha hβ hγ hψ', s910_susc_eq hd hs0 hsd ha hβ hγ hψ, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [s910_resp_smul hd hs0 hsd ha hβ hγ hψ c x, integral_const_mul]
  ring

/-- **The covariance of the path Gaussian.** -/
theorem s910_path_cov {T : ℝ} (hT : 0 < T) {f : ℕ × MultiIndex d → Euc d → ℝ}
    (hf : ∀ q, MemCb (J1 d) (f q)) (hsum : Summable fun q => cbNorm (J1 d) (f q))
    {U : MultiIndex d → ℝ → Euc d → ℝ}
    (hU : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T → ∀ x : Euc d,
      HasSum (fun n => s11p_kap n * r2CosBasis T n t * f (n, α) x) (U α t x))
    (σ : ℕ ≃ ℕ × MultiIndex d) {G : Measure (s11p_K d)} [IsProbabilityMeasure G]
    (hg : HRS.IsCenteredGaussian G)
    (hG : ∀ n m, ∫ z, inner ℝ (s11p_basis σ n) z * inner ℝ (s11p_basis σ m) z ∂G =
      HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ
        (fun x => s11p_cJ T * f (σ n) x) (fun x => s11p_cJ T * f (σ m) x))
    (t t' : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (ht' : t' ∈ Set.Icc (0 : ℝ) T) (α α' : MultiIndex d) :
    ∫ z, inner ℝ (s11p_vec hT t α) z * inner ℝ (s11p_vec hT t' α') z ∂G =
      HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) γ (U α t) (U α' t') := by
  set c := s11p_cJ T with hcdef
  have hc : 0 < c := s11p_cJ_pos T
  set A : ℕ → ℝ := fun n => c⁻¹ * (s11p_kap n * r2CosBasis T n t) with hA
  set A' : ℕ → ℝ := fun n => c⁻¹ * (s11p_kap n * r2CosBasis T n t') with hA'
  have hu : ∀ q : ℕ × MultiIndex d, (s11p_vec hT t α).c q = if q.2 = α then A q.1 else 0 := fun q => rfl
  have hv : ∀ q : ℕ × MultiIndex d, (s11p_vec hT t' α').c q = if q.2 = α' then A' q.1 else 0 := fun q => rfl
  rw [(s910_gauss_int hg _ _).2, s910_cov_expand α α' A A' _ _ hu hv]
  -- the entries
  have hent : ∀ q q' : ℕ × MultiIndex d, covarianceBilin G (s11p_basis0 d q : s11p_K d)
      (s11p_basis0 d q' : s11p_K d) = c ^ 2 * HRS.Whole.susceptibilityCov (rieszKernel d s)
        (thermalMeasure d s a β) γ (f q) (f q') := fun q q' => by
    rw [← (s910_gauss_int hg _ _).2]
    have e : ∀ z : s11p_K d, inner ℝ (s11p_basis0 d q : s11p_K d) z * inner ℝ (s11p_basis0 d q' : s11p_K d) z =
        inner ℝ (s11p_basis σ (σ.symm q)) z * inner ℝ (s11p_basis σ (σ.symm q')) z := fun z => by
      rw [s11p_inner_basis, s11p_inner_basis, Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← s910_c_eq,
        ← s910_c_eq]
    simp_rw [e]
    rw [hG (σ.symm q) (σ.symm q')]
    simp only [Equiv.apply_symm_apply]
    exact s910_susc_smul hd hs0 hsd ha hβ hγ (hf q') c
  simp_rw [hent]
  -- the covariance of the series
  have hinj : ∀ α : MultiIndex d, Function.Injective (fun n : ℕ => ((n, α) : ℕ × MultiIndex d)) :=
    fun α a b hab => by simpa using hab
  have hsα : ∀ α : MultiIndex d, Summable fun n : ℕ => cbNorm (J1 d) (f (n, α)) := fun α =>
    hsum.comp_injective (hinj α)
  have hser := s910_susc_series hd hs0 hsd ha hβ hγ (f := fun n => f (n, α)) (f' := fun n => f (n, α'))
    (fun n => hf _) (hsα α) (fun n => hf _) (hsα α')
    (fun n => s11p_kap n * r2CosBasis T n t) (fun n => s11p_kap n * r2CosBasis T n t')
    (B := Real.sqrt (2 / T)) (fun n => s910_term_bound hT n t) (fun n => s910_term_bound hT n t')
    (g := U α t) (g' := U α' t') (fun x => hU α t ht x) (fun x => hU α' t' ht' x)
  rw [hser]
  refine tsum_congr fun n => ?_
  simp only [hA, hA']
  have e1 : ∀ m : ℕ, c⁻¹ * (s11p_kap m * r2CosBasis T m t') * (c ^ 2 * HRS.Whole.susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (f (n, α)) (f (m, α'))) =
      c * ((s11p_kap m * r2CosBasis T m t') * HRS.Whole.susceptibilityCov (rieszKernel d s)
        (thermalMeasure d s a β) γ (f (n, α)) (f (m, α'))) := fun m => by
    field_simp
  simp_rw [e1]
  rw [tsum_mul_left]
  field_simp

end Path

end HRS.MS.R2Obs

end
