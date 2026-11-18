import HRS.MS.SharpBiasAux4
import HRS.MS.SharpIns
import HRS.MS.ThmSpec
import HRS.MS.Poinc
import HRS.MS.EucRegH
import HRS.MS.Canon

/-!
# HRS.MS.SharpBias -- S7.1 `sharp_bias`

Packet S71, namespace `HRS.Whole.S71`, helper prefix `s71_`.  Proof of `HRS.Whole.sharp_bias`
(TeX S L5314-5338, proof S L5847-5917).

* `s71_gwd`: `GibbsWellDefined` for every `N = n + 1 ≥ 1` and `β ≥ 0` (integrability of the exponent from the
  cavity decomposition `wr13a_E`; positivity of the normaliser).
* `s71_small`: the bound of `‖(θ-1)/δ_N - b‖_{L²(μ)}` for the finitely many `N ≤ N₁` (bounded density, `δ_N ≥ 1/N`,
  `‖R P_μ ρ‖ ≤ M`).
* `s71_core`: all `N ≥ 1`, `β ∈ [βm, βp]`, for a background satisfying the sharp insertion bound with
  constants `(C0, N0)` (taken as a hypothesis, so that the same core serves `sharp_bias` and
  `sharp_bias_uniform_beta`).
* `sharp_bias_proof`: `type_of% @HRS.Whole.sharp_bias`, from `sharp_insertion_rate_proof` (S7.6).

Statement adjustments: none.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Whole.S71

open HRS.MS.Wr HRS.External

variable {d : ℕ} {s : ℝ}

/-! ### `GibbsWellDefined` for every `N ≥ 1` -/

theorem s71_gwd (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ)
    {M : ℝ} (hM : ∀ x, ρ x ≤ M) {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    GibbsWellDefined (fun x y => rieszKernel d s (x - y)) (n + 1) β (withDensityReal ρ) := by
  haveI := wr13a_isProb_density hρ
  have hconv := wr13a_conv_le_density (by omega) hs0 hsd hρ hM
  have hint : ∀ x, Integrable (fun y => rieszKernel d s (x - y)) (withDensityReal ρ) :=
    fun x => (wr13a_potential_bound (by omega) hs0 hsd hρ hM x).1
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  set c0 : ℝ := -β * ((n + 1 : ℕ) : ℝ) * ((1 / 2) * energyPairing (rieszKernel d s) (withDensityReal ρ)
    (withDensityReal ρ)) with hc0
  have hw : ∀ X : EucConfig d (n + 1), -β * ((n + 1 : ℕ) : ℝ) *
      modulatedEnergy (rieszKernel d s) X (withDensityReal ρ) =
      wr13a_E d s (withDensityReal ρ) (β / ((n + 1 : ℕ) : ℝ)) β X + c0 := by
    intro X
    rw [modulatedEnergy_eq_sum_lt (rieszKernel d s) (fun z => rieszKernel_neg z) X (withDensityReal ρ)]
    unfold wr13a_E wr13a_pairSum
    simp only [hc0]
    field_simp
    ring
  have hexp := wr13a_exp_E_integrable hs0 hconv hlam hβ c0 (n + 1)
  have hrow : RowOKE (withDensityReal ρ) (fun x y => rieszKernel d s (x - y)) := by
    refine ⟨((wr13a_g_meas hs0).comp (measurable_fst.sub measurable_snd)), hint, ?_⟩
    refine ⟨potentialBound d s M, fun x => ?_⟩
    have : ∫ y, |rieszKernel d s (x - y)| ∂(withDensityReal ρ) = convMeasure (rieszKernel d s) (withDensityReal ρ) x := by
      unfold convMeasure
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      exact abs_of_nonneg (wr13a_g_nonneg hs0 _)
    rw [this]
    exact hconv x
  have hwint : Integrable (fun X : EucConfig d (n + 1) => Real.exp (-β * ((n + 1 : ℕ) : ℝ) *
      pairEnergy (fun x y => rieszKernel d s (x - y)) X (withDensityReal ρ)))
      (Measure.pi fun _ => withDensityReal ρ) := by
    have e : (fun X : EucConfig d (n + 1) => Real.exp (-β * ((n + 1 : ℕ) : ℝ) *
        pairEnergy (fun x y => rieszKernel d s (x - y)) X (withDensityReal ρ))) =
        fun X => Real.exp (wr13a_E d s (withDensityReal ρ) (β / ((n + 1 : ℕ) : ℝ)) β X + c0) := by
      funext X
      rw [← hw X]
      rfl
    rw [e]
    exact hexp
  refine ⟨hint, hrow.integrable_prod, hwint, ?_⟩
  unfold pairNormalizer
  exact integral_exp_pos hwint

/-! ### Small `N` -/

section Small

theorem s71_one_le_pow {N N1 θ' : ℝ} (hN : 0 < N) (hNN : N ≤ N1) (hθ : 0 ≤ θ') :
    1 ≤ N1 ^ θ' * N ^ (-θ') := by
  have h1 : N ^ θ' ≤ N1 ^ θ' := Real.rpow_le_rpow hN.le hNN hθ
  have h2 : N ^ θ' * N ^ (-θ') = 1 := by
    rw [← Real.rpow_add hN]; simp
  calc (1 : ℝ) = N ^ θ' * N ^ (-θ') := h2.symm
    _ ≤ N1 ^ θ' * N ^ (-θ') := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hN.le _)

theorem s71_small (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβ : βm ≤ βp) (M : ℝ) (N1 : ℕ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ n : ℕ, n + 1 ≤ N1 →
        MemLp (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) / deltaN d s (n + 1) -
            biasDensity d s β ρ x) 2 (withDensityReal ρ) ∧
        l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) /
            deltaN d s (n + 1) - biasDensity d s β ρ x) ≤ C * ((n + 1 : ℕ) : ℝ) ^ (-biasTheta d s) := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by linarith
  obtain ⟨hp1, hp2⟩ := s74_p_bounds hd hs hsd
  obtain ⟨hθ'0, -, -, -, -, -, -, -⟩ := s71_theta_pos_exp hd hs hsd
  have hpb1 : 1 < biasP d s := hp1
  have hpb2 : biasP d s < 2 := hp2
  have hβp0 : 0 ≤ βp := hβm.le.trans hβ
  set Cθ : ℝ := Real.exp (2 * βp * |potentialBound d s M|) with hCθ
  have hCθ1 : 1 ≤ Cθ := Real.one_le_exp (by positivity)
  set B : ℝ := (Cθ + 1) * N1 + 2 * |biasConst d s| * βp ^ biasP d s * max M 0 with hB
  refine ⟨B * (N1 : ℝ) ^ biasTheta d s, fun ρ hρ hM β hβ1 hββp n hn => ?_⟩
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  haveI hμp := wr13a_isProb_density hρ
  have hq : Q34.Q34Hyp d s ρ M := ⟨hd1, hs0, hsd, hρ, hM⟩
  have hN1r : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n + 1)
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  have hNN1 : ((n + 1 : ℕ) : ℝ) ≤ N1 := by exact_mod_cast hn
  have hδ : deltaN d s (n + 1) = ((n + 1 : ℕ) : ℝ) ^ (-(biasP d s - 1)) := by
    rw [s74_deltaN hs]; congr 1; simp only [biasP]; ring
  have hδpos : 0 < deltaN d s (n + 1) := by rw [hδ]; exact Real.rpow_pos_of_pos hNpos _
  have hδN : (((n + 1 : ℕ) : ℝ))⁻¹ ≤ deltaN d s (n + 1) := by
    rw [hδ, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hN1r (by linarith)
  have hθ0 : ∀ x, 0 < wr13d_theta d s n β (withDensityReal ρ) x := s71_theta_pos hd hs0 hsd hρ hM hβ0 n
  have hθm : Measurable (wr13d_theta d s n β (withDensityReal ρ)) := wr13d_theta_meas hd hs0 hsd hρ hM hβ0 n
  have hθCθ : ∀ x, wr13d_theta d s n β (withDensityReal ρ) x ≤ Cθ :=
    fun x => s71_theta_le hd hs0 hsd hρ hM hβ0 hββp n x
  have hzb : ∀ x, |wr13d_theta d s n β (withDensityReal ρ) x - 1| ≤ Cθ + 1 := fun x => by
    rw [abs_le]
    have := hθ0 x
    have := hθCθ x
    constructor <;> linarith
  have hzL : MemLp (fun x => wr13d_theta d s n β (withDensityReal ρ) x - 1) 2 (withDensityReal ρ) :=
    MemLp.of_bound (hθm.sub_const 1).aestronglyMeasurable (Cθ + 1)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hzb x)
  have hρL : MemLp ρ 2 (withDensityReal ρ) :=
    MemLp.of_bound hρ.measurable.aestronglyMeasurable M (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      exact hM x)
  have hrL : MemLp (responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ) 2 (withDensityReal ρ) :=
    (s71_resp_spec hq hβpos hρL).1.1
  have hEL : MemLp (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) / deltaN d s (n + 1) -
      biasDensity d s β ρ x) 2 (withDensityReal ρ) :=
    (s71_memLp_div hzL _).sub (hrL.const_mul (2 * biasConst d s * β ^ biasP d s))
  refine ⟨hEL, ?_⟩
  have hbL : MemLp (fun x => 2 * biasConst d s * β ^ biasP d s *
      responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ x) 2 (withDensityReal ρ) :=
    hrL.const_mul _
  have h1 : l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) /
      deltaN d s (n + 1)) ≤ (Cθ + 1) * ((n + 1 : ℕ) : ℝ) := by
    refine s71_l2Norm_le_of_bound (by positivity) (fun x => ?_)
    rw [abs_div, abs_of_pos hδpos, div_le_iff₀ hδpos]
    have h2 : (Cθ + 1) * ((n + 1 : ℕ) : ℝ) * deltaN d s (n + 1) ≥ (Cθ + 1) := by
      have : 1 ≤ ((n + 1 : ℕ) : ℝ) * deltaN d s (n + 1) := by
        have := mul_le_mul_of_nonneg_left hδN hNpos.le
        rwa [mul_inv_cancel₀ hNpos.ne'] at this
      nlinarith
    exact (hzb x).trans h2
  have h2 : l2Norm (withDensityReal ρ) (fun x => 2 * biasConst d s * β ^ biasP d s *
      responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ x) ≤
      2 * |biasConst d s| * βp ^ biasP d s * max M 0 := by
    rw [s71_l2Norm_const_mul]
    have hR := HRS.MS.SuppN.u12_R_l2 hd hs hsd β M hβpos ρ hρ hM
    have hc : |2 * biasConst d s * β ^ biasP d s| ≤ 2 * |biasConst d s| * βp ^ biasP d s := by
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg (Real.rpow_nonneg hβ0 _)]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hβ0 hββp (by linarith)) (by positivity)
    calc |2 * biasConst d s * β ^ biasP d s| *
          l2Norm (withDensityReal ρ) (responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ)
        ≤ (2 * |biasConst d s| * βp ^ biasP d s) * max M 0 :=
          mul_le_mul hc (hR.trans (le_max_left _ _)) (s71_l2Norm_nonneg _ _) (by positivity)
      _ = _ := by ring
  have h3 := s71_l2Norm_sub_le (s71_memLp_div hzL (deltaN d s (n + 1))) hbL
  have hY := s71_one_le_pow hNpos hNN1 hθ'0.le
  have hBnn : 0 ≤ B := by positivity
  calc l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) /
          deltaN d s (n + 1) - biasDensity d s β ρ x)
      ≤ (Cθ + 1) * ((n + 1 : ℕ) : ℝ) + 2 * |biasConst d s| * βp ^ biasP d s * max M 0 := by
        have h3' : l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) /
            deltaN d s (n + 1) - biasDensity d s β ρ x) ≤
            l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) /
              deltaN d s (n + 1)) + l2Norm (withDensityReal ρ) (fun x => 2 * biasConst d s * β ^ biasP d s *
              responseInverse (rieszKernel d s) (withDensityReal ρ) β ρ x) := h3
        linarith
    _ ≤ B := by
        rw [hB]
        have : (Cθ + 1) * ((n + 1 : ℕ) : ℝ) ≤ (Cθ + 1) * N1 :=
          mul_le_mul_of_nonneg_left hNN1 (by positivity)
        linarith
    _ = B * 1 := (mul_one _).symm
    _ ≤ B * ((N1 : ℝ) ^ biasTheta d s * ((n + 1 : ℕ) : ℝ) ^ (-biasTheta d s)) :=
        mul_le_mul_of_nonneg_left hY hBnn
    _ = B * (N1 : ℝ) ^ biasTheta d s * ((n + 1 : ℕ) : ℝ) ^ (-biasTheta d s) := by ring

end Small

/-! ### The core theorem -/

theorem s71_core (hd : 2 ≤ d) (hs : (d : ℝ) / 2 < s) (hsd : s < d) {βm βp : ℝ} (hβm : 0 < βm)
    (hβ : βm ≤ βp) (M C0 : ℝ) (N0 : ℕ) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, N0 ≤ N → ∀ x : Euc d,
        |insertionDefect d s N β (withDensityReal ρ) x / (((N : ℝ) - 1) * (β / N) ^ biasP d s) -
            2 * biasConst d s * ρ x| ≤ C0 * (N : ℝ) ^ (-biasTheta d s)) →
      ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ N : ℕ, 1 ≤ N → SharpBiasConclusion d s N β ρ C := by
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  obtain ⟨Cl, N1, hN1, hlarge⟩ := s71_large hd hs hsd hβm hβ M C0 N0
  obtain ⟨Cs, hsmall⟩ := s71_small hd hs hsd hβm hβ M N1
  refine ⟨max Cl Cs, fun ρ hρ hM hIns β hβ1 hββp N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hβ0 : 0 ≤ β := (hβm.trans_le hβ1).le
  have hβpos : 0 < β := hβm.trans_le hβ1
  have hY : 0 ≤ ((n + 1 : ℕ) : ℝ) ^ (-biasTheta d s) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hE : MemLp (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) / deltaN d s (n + 1) -
        biasDensity d s β ρ x) 2 (withDensityReal ρ) ∧
      l2Norm (withDensityReal ρ) (fun x => (wr13d_theta d s n β (withDensityReal ρ) x - 1) /
        deltaN d s (n + 1) - biasDensity d s β ρ x) ≤ max Cl Cs * ((n + 1 : ℕ) : ℝ) ^ (-biasTheta d s) := by
    by_cases hn : N1 ≤ n + 1
    · obtain ⟨h1, h2⟩ := hlarge ρ hρ hM hIns β hβ1 hββp n hn
      exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hY)⟩
    · obtain ⟨h1, h2⟩ := hsmall ρ hρ hM β hβ1 hββp n (not_le.1 hn).le
      exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hY)⟩
  have hθCθ : ∀ x, wr13d_theta d s n β (withDensityReal ρ) x ≤ Real.exp (2 * βp * |potentialBound d s M|) :=
    fun x => s71_theta_le hd hs0 hsd hρ hM hβ0 hββp n x
  exact s71_conclusion hd hs hsd hβpos hρ hM (by omega) (s71_gwd hd hs0 hsd hρ hM hβ0 n)
    (wr13d_theta_meas hd hs0 hsd hρ hM hβ0 n) (fun x => (s71_theta_pos hd hs0 hsd hρ hM hβ0 n x).le)
    hθCθ (wr13d_firstMarginal_eq hd hs0 hsd hρ hM hβ0 n) (s71_theta_integral hd hs0 hsd hρ hM hβ0 n) hE

/-! ### The frozen statement -/

/-- **Theorem S7.1** (`HRS.Whole.sharp_bias`). -/
theorem sharp_bias_proof : type_of% @HRS.Whole.sharp_bias := by
  intro d s hd hs hsd β M Λ hβ
  obtain ⟨C0, N0, hrate⟩ := HRS.MS.S76.sharp_insertion_rate_proof hd hs hsd β M Λ hβ
  obtain ⟨C, hC⟩ := s71_core hd hs hsd hβ (le_refl β) M C0 N0
  refine ⟨C, fun ρ hρ hM hΛ N hN => hC ρ hρ hM ?_ β le_rfl le_rfl N hN⟩
  intro β' hβ1 hβ2 N' hN' x
  have : β' = β := le_antisymm hβ2 hβ1
  subst this
  exact hrate N' hN' ρ hρ hM hΛ x

/-! ### Uniformity in `β` -/

/-- **Theorem S7.1, uniformity in `β`** (`HRS.Whole.sharp_bias_uniform_beta`): the sharp insertion rate
uniform in `β ∈ [βm, βp]` (`HRS.MS.S76.s71_rate_u`, the uniform-in-`β` form of S7.6 proved from the same inputs)
feeds the core with `N0 = 3`. -/
theorem sharp_bias_uniform_beta_proof : type_of% @HRS.Whole.sharp_bias_uniform_beta := by
  intro d s hd hs hsd ρ hρ M hM Λ hΛ βm βp hβm hβ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  obtain ⟨C0, hrate⟩ := HRS.MS.S76.s71_rate_u hd hs hsd hβm hβ M Λ hM0
  obtain ⟨C, hC⟩ := s71_core hd hs hsd hβm hβ M C0 3
  exact ⟨C, fun β hβmem N hN => hC ρ hρ hM
    (fun β' h1 h2 N' hN' x => hrate ρ hρ hM hΛ β' h1 h2 N' hN' x) β hβmem.1 hβmem.2 N hN⟩

/-! ### Quadratic confinement -/

theorem s71_thermal_equilibrium (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) : IsThermalEquilibrium d s a β (thermalDensity d s a β) := by
  obtain ⟨⟨ρ, hρ, -⟩, -, -⟩ := HRS.MS.Thm.thermalDensity_spec_proof hd hs0 hsd a β ha hβ
  have hex : ∃ ρ, IsThermalEquilibrium d s a β ρ := ⟨ρ, hρ⟩
  unfold thermalDensity
  rw [dif_pos hex]
  exact hex.choose_spec

theorem s71_thermal_bounded (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) : ∃ M : ℝ, ∀ x, thermalDensity d s a β x ≤ M := by
  obtain ⟨c, hc, C, hb, -⟩ := HRS.MS.Poinc.euc_thermal_gaussian_bounds_proof hd hs0 hsd a β ha hβ
  refine ⟨|C| * (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2), fun x => ?_⟩
  have hG : gaussianComparison d a β x ≤ (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) := by
    unfold gaussianComparison
    have h1 : Real.exp (-β * a * ‖x‖ ^ 2 / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ β * a * ‖x‖ ^ 2 := by positivity
      linarith
    have h0 : 0 ≤ (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) := by positivity
    calc (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) * Real.exp (-β * a * ‖x‖ ^ 2 / 2)
        ≤ (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left h1 h0
      _ = _ := mul_one _
  have hG0 : 0 ≤ gaussianComparison d a β x := by unfold gaussianComparison; positivity
  calc thermalDensity d s a β x ≤ C * gaussianComparison d a β x := (hb x).2
    _ ≤ |C| * gaussianComparison d a β x := mul_le_mul_of_nonneg_right (le_abs_self _) hG0
    _ ≤ |C| * (β * a / (2 * Real.pi)) ^ ((d : ℝ) / 2) := mul_le_mul_of_nonneg_left hG (abs_nonneg _)

theorem s71_thermal_lipschitz (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (a β : ℝ) (ha : 0 < a)
    (hβ : 0 < β) : ∃ Λ : ℝ≥0, LipschitzWith Λ (thermalDensity d s a β) := by
  obtain ⟨hcd, -, -, -, h5, -⟩ := HRS.MS.Thm.euc_thermal_regularity_proof hd hs0 hsd a β ha hβ
  obtain ⟨-, K, hK⟩ := h5 1
  refine ⟨K.toNNReal, lipschitzWith_of_nnnorm_fderiv_le (hcd.differentiable (by simp)) (fun x => ?_)⟩
  have h1 : ‖fderiv ℝ (thermalDensity d s a β) x‖ ≤ K := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]; exact hK x
  have : ((‖fderiv ℝ (thermalDensity d s a β) x‖₊ : ℝ≥0) : ℝ) ≤ ((K.toNNReal : ℝ≥0) : ℝ) := by
    rw [coe_nnnorm]; exact h1.trans (Real.le_coe_toNNReal K)
  exact_mod_cast this

/-- **Theorem S7.1, quadratic confinement** (`HRS.Whole.sharp_bias_quadratic`). -/
theorem sharp_bias_quadratic_proof : type_of% @HRS.Whole.sharp_bias_quadratic := by
  intro d s hd hs hsd a β ha hβ
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    linarith
  have hth := s71_thermal_equilibrium hd hs0 hsd a β ha hβ
  have hprob : IsProbDensity (thermalDensity d s a β) := hth.2.1
  obtain ⟨M, hM⟩ := s71_thermal_bounded hd hs0 hsd a β ha hβ
  obtain ⟨Λ, hΛ⟩ := s71_thermal_lipschitz hd hs0 hsd a β ha hβ
  have hint : ∀ x, Integrable (fun y => rieszKernel d s (x - y)) (withDensityReal (thermalDensity d s a β)) :=
    fun x => (wr13a_potential_bound (by omega) hs0 hsd hprob hM x).1
  have hcan : ∀ N, canonicalGibbs (rieszKernel d s) (confinement a) N β =
      modulatedGibbs (rieszKernel d s) N β (thermalMeasure d s a β) := fun N =>
    HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof (N := N) (rieszKernel d s) (confinement a) β
      (thermalDensity d s a β) hth.2 (fun x => rieszKernel_neg x) hint
  obtain ⟨C, hC⟩ := sharp_bias_proof hd hs hsd β M Λ hβ
  exact ⟨hprob, ⟨M, hM⟩, ⟨Λ, hΛ⟩, hcan, C, fun N hN => hC _ hprob hM hΛ N hN⟩

end HRS.Whole.S71
