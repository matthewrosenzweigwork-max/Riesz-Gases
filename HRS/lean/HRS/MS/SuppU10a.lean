import HRS.Whole.AppendixBField
import HRS.MP.HNegInfra
import HRS.Prob.HilbertCLT
import HRS.MS.SuppU10aAux1
import HRS.MS.SuppU10aAux2

/-!
# U10a: proof of `HRS.Whole.limit_field_rd_gaussian` (S.B.7 (ii))

The covariance `Q(u,v) = 2q ∫_0^t ∫ ∑_j ⟨K_j,u⟩⟨K_j,v⟩ ρ dx dr` is a trace-class form on `H = H^{-Γ}`
(`u10_core`, `SuppU10aAux1`), the Gaussian measure `ν` is the one of
`exists_centeredGaussian_of_traceClass`, and the extension is the product `Ω × H` with `P ⊗ ν`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.MS.U10

open HRS HRS.Whole HRS.MP.HNegInfra

variable {d : ℕ}

theorem u10_pairing_add {Γ : ℝ} {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) (F G : HNeg d Γ) :
    HNeg.pairing φ (F + G) = HNeg.pairing φ F + HNeg.pairing φ G := by
  rw [mhn_pairing_eq hφ.2, mhn_pairing_eq hφ.2, mhn_pairing_eq hφ.2]
  show (inner ℂ (mhn_psiLp hφ.2) ((F : HNegSubmodule d Γ).1 + (G : HNegSubmodule d Γ).1 :
      Lp ℂ 2 (sobolevMeasure d Γ))).re = _
  rw [inner_add_right, Complex.add_re]

theorem u10_pairing_smul {Γ : ℝ} {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) (c : ℝ)
    (F : HNeg d Γ) : HNeg.pairing φ (c • F) = c * HNeg.pairing φ F := by
  rw [mhn_pairing_eq hφ.2, mhn_pairing_eq hφ.2]
  show (inner ℂ (mhn_psiLp hφ.2) (c • (F : HNegSubmodule d Γ).1 :
      Lp ℂ 2 (sobolevMeasure d Γ))).re = _
  rw [inner_smul_right_eq_smul, Complex.smul_re, smul_eq_mul]

/-- Riesz representative of the pairing with a smooth test. -/
theorem u10_riesz {Γ : ℝ} {φ : Euc d → ℝ} (hφ : IsSobolevTest Γ φ) :
    ∃ g : HNeg d Γ, ∀ F : HNeg d Γ, inner ℝ g F = HNeg.pairing φ F := by
  let ℓ : HNeg d Γ →ₗ[ℝ] ℝ :=
    { toFun := fun F => HNeg.pairing φ F
      map_add' := u10_pairing_add hφ
      map_smul' := fun c F => by simpa using u10_pairing_smul hφ c F }
  let ℓc : HNeg d Γ →L[ℝ] ℝ := ℓ.mkContinuous (HRS.Whole.sobolevNorm Γ φ) (fun F => by
    have := hneg_pairing_le hφ F
    simpa [ℓ, Real.norm_eq_abs, mul_comm] using this)
  refine ⟨(InnerProductSpace.toDual ℝ (HNeg d Γ)).symm ℓc, fun F => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem limit_field_rd_gaussian_proof : type_of% @HRS.Whole.limit_field_rd_gaussian := by
  intro d Γ C q T B hq hρ hρm Kern hK t ht
  have ht0 : 0 ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hρt : ∀ r ∈ Set.Icc (0 : ℝ) t, HRS.Whole.IsProbDensity (C.ρ r) :=
    fun r hr => hρ r ⟨hr.1, hr.2.trans htT⟩
  haveI := u10_isFinite ht0 hρt hρm
  set μ := u10_mu d t C.ρ with hμ
  let k : ℝ × Euc d → Fin d → HNeg d Γ := fun p j => Kern p.1 t p.2 j
  have hkB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ (x : Euc d) (j : Fin d), ‖k (r, x) j‖ ≤ B :=
    fun r hr x j => hK.bound r t hr.1 hr.2 htT x j
  have hk : U10Data μ k B :=
    ⟨fun j => (hK.measurable j).comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)),
      by
        have h : ∀ᵐ p ∂(u10_m d t), ∀ j, ‖k p j‖ ≤ B := by
          filter_upwards [u10_ae_mem (d := d) t] with p hp j using hkB p.1 hp p.2 j
        exact (withDensity_absolutelyContinuous _ _).ae_le h⟩
  obtain ⟨ν, hν, hcg, hsq, hcov⟩ := u10_core μ k B hk q hq
  -- the trace as an iterated integral
  have hgm : Measurable fun p : ℝ × Euc d => ∑ j, ‖k p j‖ ^ 2 :=
    Finset.measurable_sum _ fun j _ => (hk.meas j).norm.pow_const 2
  have hgb : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d, ‖∑ j, ‖k (r, x) j‖ ^ 2‖ ≤ d * B ^ 2 := by
    intro r hr x
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    calc ∑ j, ‖k (r, x) j‖ ^ 2 ≤ ∑ _j : Fin d, B ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hkB r hr x j) 2
      _ = d * B ^ 2 := by simp
  have htr := (u10_integral_eq (d := d) ht0 hρt hρm hgm hgb).2
  have htr' : ∫ p, ∑ j, ‖k p j‖ ^ 2 ∂μ =
      ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ∑ j, ‖Kern r t x j‖ ^ 2 * C.ρ r x := by
    rw [htr]
    refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [k, Finset.sum_mul]
  have hbound : ∫ p, ∑ j, ‖k p j‖ ^ 2 ∂μ ≤ d * B ^ 2 * t := by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (u10_ae_bound (d := d) (ρ := C.ρ)
      (g := fun p : ℝ × Euc d => ∑ j, ‖k p j‖ ^ 2) hgb)
    rw [u10_real_univ ht0 hρt hρm] at h
    exact (le_abs_self _).trans (by simpa using h)
  refine ⟨ν, hν, hcg, ?_, ?_, ?_, ?_⟩
  · rw [hsq, htr']
  · rw [hsq]
    refine ENNReal.ofReal_le_ofReal ?_
    calc 2 * q * ∫ p, ∑ j, ‖k p j‖ ^ 2 ∂μ ≤ 2 * q * (d * B ^ 2 * t) :=
          mul_le_mul_of_nonneg_left hbound (by linarith)
      _ = 2 * q * d * t * B ^ 2 := by ring
  · intro φ ψ hφ hψ
    obtain ⟨u, hu⟩ := u10_riesz hφ
    obtain ⟨v, hv⟩ := u10_riesz hψ
    have h1 := hcov u v
    simp_rw [hu, hv] at h1
    have hS : ∀ p, u10_S k u v p =
        ∑ j, HNeg.pairing φ (k p j) * HNeg.pairing ψ (k p j) := by
      intro p
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_comm, hu, ← real_inner_comm (k p j) v, hv]
    have hSb : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d,
        ‖u10_S k u v (r, x)‖ ≤ Fintype.card (Fin d) * (B ^ 2 * ‖u‖ * ‖v‖) :=
      fun r hr x => u10_S_bound_pt (hkB r hr x) u v
    have h2 := (u10_integral_eq (d := d) ht0 hρt hρm (u10_S_measurable hk u v) hSb).2
    have h3 : ∫ p, u10_S k u v p ∂μ = ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ∑ j,
        HNeg.pairing φ (Kern r t x j) * HNeg.pairing ψ (Kern r t x j) * C.ρ r x := by
      rw [h2]
      refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only [hS, k, Finset.sum_mul]
    have hA : ∫ x, HNeg.pairing φ x * HNeg.pairing ψ x ∂ν =
        2 * q * ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ∑ j,
          HNeg.pairing φ (Kern r t x j) * HNeg.pairing ψ (Kern r t x j) * C.ρ r x := by
      rw [h1, h3]
    refine ⟨hA, ?_⟩
    rw [hA]
    unfold noiseCovW
    rw [min_self]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [PiLp.inner_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hK.represent r t hr.1 hr.2 htT x j φ hφ, hK.represent r t hr.1 hr.2 htT x j ψ hψ]
    simp [mul_comm]
  · intro Ω _ P _ β _ Y hY
    refine ⟨Ω × HNeg d Γ, inferInstance, P.prod ν, inferInstance, Prod.fst, Prod.snd,
      measurePreserving_fst, measurable_snd, ?_, ?_⟩
    · show (P.prod ν).map Prod.snd = ν
      simp
    · exact indepFun_prod hY measurable_id

end HRS.MS.U10
