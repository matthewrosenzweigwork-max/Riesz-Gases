import Mathlib
import HRS.MS.SuppU5Aux8
import HRS.Whole.AppendixBField

/-!
# Packet U5: `iid_init_field_rd` (S.B.2, single time)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

open HRS HRS.Whole HRS.MP.RdProp HRS.MP.HNegInfra

variable {d : ℕ}

lemma u5_fieldAmp_bounds (N : ℕ) (hN : 1 ≤ N) (invβ : ℝ) (h0 : 0 ≤ invβ) :
    0 ≤ fieldAmp N invβ ∧ fieldAmp N invβ ≤ 1 := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  unfold fieldAmp Ascale sigmaScale
  by_cases hb : invβ = 0
  · simp [hb]
  · simp only [hb, if_false]
    refine ⟨div_nonneg (le_min hs.le (Real.sqrt_nonneg _)) hs.le, ?_⟩
    rw [div_le_one hs]
    exact min_le_left _ _

lemma u5_log_ge_one {N : ℕ} (hN : 3 ≤ N) : (1 : ℝ) ≤ Real.log N := by
  have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  have h2 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num)]
    exact this
  have : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) h3
  linarith

/-- The data extracted from the adjoint input at one time. -/
lemma u5_adj_data {Γ : ℕ} {T K : ℝ} {C : WholeCoeff d} (hadj : AdjointInputOne (Γ : ℝ) C T K)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (∀ φ, IsSobolevTest (Γ : ℝ) φ → MemCb 1 (propagatorW C 0 t φ) ∧
        cbNorm 1 (propagatorW C 0 t φ) ≤ K * HRS.Whole.sobolevNorm (Γ : ℝ) φ) ∧
    (∀ (φ₁ φ₂ : Euc d → ℝ) (c : ℝ), IsSobolevTest (Γ : ℝ) φ₁ → IsSobolevTest (Γ : ℝ) φ₂ →
        propagatorW C 0 t (φ₁ + c • φ₂) = propagatorW C 0 t φ₁ + c • propagatorW C 0 t φ₂) := by
  obtain ⟨-, hlin, hbd⟩ := hadj t ht
  exact ⟨fun φ hφ => hbd φ hφ, fun φ₁ φ₂ c h₁ h₂ => hlin φ₁ φ₂ h₁ h₂ c 0 ⟨le_rfl, ht.1⟩⟩

lemma u5_range_orth_bot (Γ : ℝ) : (LinearMap.range (rpk_J (d := d) Γ))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro F hF
  refine hneg_eq_zero_of_pairing_zero F fun φ hφ => ?_
  rw [← rpk_J_inner (⟨φ, hφ⟩ : rpk_Tst d Γ) F]
  exact (Submodule.mem_orthogonal _ _).1 hF _ ⟨⟨φ, hφ⟩, rfl⟩

lemma u5_hmean {Γ : ℝ} (A : ℝ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (ψ : (Euc d → ℝ) → (Euc d → ℝ)) (hψc : ∀ φ, IsSobolevTest Γ φ → MemCb 1 (ψ φ))
    (J : Euc d → HNeg d Γ)
    (hJ : ∀ x φ, IsSobolevTest Γ φ → HNeg.pairing φ (J x) = A * (ψ φ x - HRS.Whole.pair μ (ψ φ))) :
    ∀ w ∈ LinearMap.range (rpk_J Γ), ∫ x, inner ℝ w (J x) ∂μ = 0 := by
  rintro w ⟨Φ, rfl⟩
  have : ∀ x, inner ℝ (rpk_J Γ Φ) (J x) = A * (ψ Φ.1 x - HRS.Whole.pair μ (ψ Φ.1)) := fun x => by
    rw [rpk_J_inner, hJ x _ Φ.2]
  simp_rw [this]
  rw [integral_const_mul, integral_sub (u5_cb_integrable (hψc _ Φ.2) μ) (integrable_const _)]
  simp [HRS.Whole.pair]

end HRS.U5

open HRS HRS.Whole HRS.U5 HRS.MP.RdProp HRS.MP.HNegInfra

variable {d : ℕ} in
theorem iid_init_field_rd_proof : type_of% @HRS.Whole.iid_init_field_rd := by
  intro d hd Γ T K m₂
  refine ⟨max (3 * u5_C0 d m₂ * max K 0) (8 * (max K 0) ^ 2), ?_⟩
  intro Cf invβ hinv hadj μ hμ hμ2 hm N hN t ht
  haveI := hμ
  set A := fieldAmp N (invβ N) with hAdef
  obtain ⟨hA0, hA1⟩ := u5_fieldAmp_bounds N hN (invβ N) (hinv N)
  obtain ⟨hψ, hlin⟩ := u5_adj_data (hadj N hN) ht
  set ψ : (Euc d → ℝ) → Euc d → ℝ := fun φ => propagatorW (Cf N) 0 t φ with hψdef
  obtain ⟨J, hJ, hJb, hJL⟩ := u5_feature (Γ : ℝ) K A hA0 μ ψ hψ hlin
  set Kp : ℝ := max K 0 with hKp
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  have hJc : Continuous J :=
    (LipschitzWith.of_dist_le' (K := A * Kp) fun x y => by
      simpa [dist_eq_norm] using hJL x y).continuous
  set S₀ : EucConfig d N → HNeg d (Γ : ℝ) := fun X => (Real.sqrt N)⁻¹ • ∑ i, J (X i) with hS₀
  have hS₀m : Measurable S₀ :=
    Measurable.const_smul (g := fun X : EucConfig d N => ∑ i, J (X i))
      (Finset.measurable_sum Finset.univ fun i _ => hJc.measurable.comp (measurable_pi_apply i))
      (Real.sqrt N)⁻¹
  have hS₀pair : ∀ X φ, IsSobolevTest (Γ : ℝ) φ → HNeg.pairing φ (S₀ X) =
      A * Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (ψ φ) - HRS.Whole.pair μ (ψ φ)) := fun X φ hφ =>
    u5_pairing_sum hN A μ ψ J (fun φ hφ => (hψ φ hφ).1) hJ X φ hφ
  refine ⟨⟨S₀, hS₀m, fun φ hφ X => hS₀pair X φ hφ⟩, ?_, ?_⟩
  · intro Ω' _ P' _ η hη
    exact u5_exists_I K A hA0 μ ψ hψ hlin P' η hη.1 hη.2
  · intro Ω _ P _ X hXm hXl Iemp hIm hIemp Ω' _ P' _ η hη I hIm' hI
    have hae : Iemp =ᵐ[P] fun ζ => S₀ (X ζ) :=
      u5_ae_eq_of_pairing P Iemp (fun ζ => S₀ (X ζ)) (fun φ hφ => by
        filter_upwards [hIemp φ hφ] with ζ hζ
        rw [hζ, hS₀pair (X ζ) φ hφ])
    have hlawE : law P Iemp = P.map (fun ζ => S₀ (X ζ)) := Measure.map_congr hae
    have hb0 : 0 ≤ 2 * A * Kp := by positivity
    have hΛ0 : 0 ≤ A * Kp := by positivity
    have hIl : ∀ (L : ℕ) (w : Fin L → HNeg d (Γ : ℝ)), (∀ a, w a ∈ LinearMap.range (rpk_J (Γ : ℝ))) →
        P'.map (fun ζ => (WithLp.toLp 2 fun a => inner ℝ (w a) (I ζ) : Ek L)) =
          multivariateGaussian 0 (Matrix.of fun a b => ∫ x, inner ℝ (w a) (J x) * inner ℝ (w b) (J x) ∂μ) :=
      fun L w hw => u5_coords_law K A hA0 μ ψ (fun φ hφ => (hψ φ hφ).1) J hJ P' η hη.1 hη.2 I hI L w hw
    obtain ⟨hW, hmS, hmI⟩ := u5_assembly (E := HNeg d (Γ : ℝ)) hd hN μ hμ2 hm
      (LinearMap.range (rpk_J (Γ : ℝ))) (u5_range_orth_bot _) J hJc.measurable hb0 hΛ0 hJb hJL
      (u5_hmean A μ ψ (fun φ hφ => (hψ φ hφ).1) J hJ) P X hXm hXl P' I hIm' hIl
    set Cc : ℝ := max (3 * u5_C0 d m₂ * max K 0) (8 * (max K 0) ^ 2) with hCc
    have hCc0 : 0 ≤ Cc := le_trans (by have := u5_C0_nonneg d m₂; positivity) (le_max_left _ _)
    have hmomE : ∫⁻ ζ, ‖Iemp ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal ((2 * A * Kp) ^ 2) := by
      rw [lintegral_congr_ae (hae.mono fun ζ h => by rw [h])]
      exact hmS
    refine ⟨fun h3 => ?_, ?_⟩
    · have hlog := u5_log_ge_one h3
      have hrpow : 1 ≤ Real.log N ^ (1 / (2 * (d : ℝ) + 5)) :=
        Real.one_le_rpow hlog (by positivity)
      have hNa : 0 ≤ (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) := by positivity
      have hX0 : 0 ≤ Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log N ^ (1 / (2 * (d : ℝ) + 5)) := by positivity
      have hC0 := u5_C0_nonneg d m₂
      have hmain : u5_C0 d m₂ * (A * Kp + 2 * A * Kp) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) ≤
          Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
            Real.log N ^ (1 / (2 * (d : ℝ) + 5)) := by
        have h1 : u5_C0 d m₂ * (A * Kp + 2 * A * Kp) ≤ Cc * A := by
          have : 3 * u5_C0 d m₂ * Kp ≤ Cc := le_max_left _ _
          nlinarith [this, hA0]
        calc u5_C0 d m₂ * (A * Kp + 2 * A * Kp) * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10)))
            ≤ Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) := mul_le_mul_of_nonneg_right h1 hNa
          _ ≤ Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
                Real.log N ^ (1 / (2 * (d : ℝ) + 5)) := by
              have : 0 ≤ Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) := by positivity
              nlinarith [this, hrpow]
      have hW1 : wassersteinE 1 (law P Iemp) (law P' I) ≤
          ENNReal.ofReal (Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
            Real.log N ^ (1 / (2 * (d : ℝ) + 5))) := by
        rw [hlawE]
        exact hW.trans (ENNReal.ofReal_le_ofReal hmain)
      refine ⟨hW1, ?_⟩
      have h1 : ENNReal.ofReal (smoothDist 1 (law P Iemp) (law P' I)) ≤
          ENNReal.ofReal (Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
            Real.log N ^ (1 / (2 * (d : ℝ) + 5))) :=
        (smoothDist_one_le_wasserstein _ _).trans hW1
      have h2 := (ENNReal.ofReal_le_ofReal_iff hX0).1 h1
      exact (smoothDist_succ_le 1 _ _).trans h2
    · have h1 : ENNReal.ofReal ((2 * A * Kp) ^ 2) + ENNReal.ofReal ((2 * A * Kp) ^ 2) ≤
          ENNReal.ofReal Cc := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have : 8 * Kp ^ 2 ≤ Cc := le_max_right _ _
        have hA2 : A ^ 2 ≤ 1 := by nlinarith
        nlinarith [sq_nonneg Kp, mul_nonneg (sq_nonneg Kp) (sub_nonneg.2 hA2)]
      exact (add_le_add hmomE hmI).trans h1
