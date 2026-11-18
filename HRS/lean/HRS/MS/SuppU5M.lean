import Mathlib
import HRS.MS.SuppU5
import HRS.MS.SuppU5Aux9
import HRS.Whole.AppendixBField

/-!
# Packet U5: `iid_init_field_rd_multitime` (S.B.2, finite collection of times)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

open HRS HRS.Whole HRS.MP.RdProp HRS.MP.HNegInfra

variable {d : ℕ}

lemma u5_pi_norm_le {E : Type*} [NormedAddCommGroup E] {p : ℕ} (v : Fin p → E) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a, ‖v a‖ ≤ c) : ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : Fin p => E))‖ ≤ Real.sqrt p * c := by
  rw [PiLp.norm_eq_of_L2]
  calc Real.sqrt (∑ a, ‖(WithLp.toLp 2 v : PiLp 2 (fun _ : Fin p => E)) a‖ ^ 2)
      ≤ Real.sqrt (∑ _a : Fin p, c ^ 2) := by
        refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun a _ => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (h a) 2
    _ = Real.sqrt p * c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_sq hc]

end HRS.U5

open HRS HRS.Whole HRS.U5 HRS.MP.RdProp HRS.MP.HNegInfra

theorem iid_init_field_rd_multitime_proof : type_of% @HRS.Whole.iid_init_field_rd_multitime := by
  intro d hd Γ T K m₂ p
  refine ⟨max (3 * u5_C0 d m₂ * (Real.sqrt p * max K 0)) (8 * p * (max K 0) ^ 2), ?_⟩
  intro Cf invβ hinv hadj μ hμ hμ2 hm N hN ts hts Ω _ P _ X hXm hXl Iemp hIm hIemp Ω' _ P' _ η hη I hIm' hI
  haveI := hμ
  set A := fieldAmp N (invβ N) with hAdef
  obtain ⟨hA0, hA1⟩ := u5_fieldAmp_bounds N hN (invβ N) (hinv N)
  set Kp : ℝ := max K 0 with hKp
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  set ψ : Fin p → (Euc d → ℝ) → Euc d → ℝ := fun a φ => propagatorW (Cf N) 0 (ts a) φ with hψdef
  have hψ : ∀ a φ, IsSobolevTest (Γ : ℝ) φ → MemCb 1 (ψ a φ) ∧
      cbNorm 1 (ψ a φ) ≤ K * HRS.Whole.sobolevNorm (Γ : ℝ) φ := fun a => (u5_adj_data (hadj N hN) (hts a)).1
  have hlin : ∀ a (φ₁ φ₂ : Euc d → ℝ) (c : ℝ), IsSobolevTest (Γ : ℝ) φ₁ → IsSobolevTest (Γ : ℝ) φ₂ →
      ψ a (φ₁ + c • φ₂) = ψ a φ₁ + c • ψ a φ₂ := fun a => (u5_adj_data (hadj N hN) (hts a)).2
  choose J hJ hJb hJL using fun a => u5_feature (Γ : ℝ) K A hA0 μ (ψ a) (hψ a) (hlin a)
  have hJc : ∀ a, Continuous (J a) := fun a =>
    (LipschitzWith.of_dist_le' (K := A * Kp) fun x y => by
      simpa [dist_eq_norm] using hJL a x y).continuous
  set Jp : Euc d → PiLp 2 (fun _ : Fin p => HNeg d (Γ : ℝ)) := fun x => WithLp.toLp 2 (fun a => J a x) with hJp
  have hJpm : Measurable Jp :=
    (MeasurableEquiv.toLp 2 (Fin p → HNeg d (Γ : ℝ))).measurable.comp
      (measurable_pi_iff.2 fun a => (hJc a).measurable)
  have hb0 : 0 ≤ Real.sqrt p * (2 * A * Kp) := by positivity
  have hΛ0 : 0 ≤ Real.sqrt p * (A * Kp) := by positivity
  have hJpb : ∀ x, ‖Jp x‖ ≤ Real.sqrt p * (2 * A * Kp) := fun x =>
    u5_pi_norm_le (fun a => J a x) (by positivity) (fun a => hJb a x)
  have hJpL : ∀ x y, ‖Jp x - Jp y‖ ≤ (Real.sqrt p * (A * Kp)) * ‖x - y‖ := fun x y => by
    have := u5_pi_norm_le (fun a => J a x - J a y) (c := A * Kp * ‖x - y‖) (by positivity)
      (fun a => hJL a x y)
    calc ‖Jp x - Jp y‖ = ‖(WithLp.toLp 2 (fun a => J a x - J a y) : PiLp 2 (fun _ : Fin p => HNeg d (Γ : ℝ)))‖ := rfl
      _ ≤ _ := this
      _ = _ := by ring
  -- the empirical vector
  set S₀ : Ω → PiLp 2 (fun _ : Fin p => HNeg d (Γ : ℝ)) := fun ζ => (Real.sqrt N)⁻¹ • ∑ i, Jp (X ζ i) with hS₀
  have hS₀a : ∀ ζ a, S₀ ζ a = (Real.sqrt N)⁻¹ • ∑ i, J a (X ζ i) := fun ζ a => by
    simp [hS₀, hJp]
  have hae : Iemp =ᵐ[P] S₀ := by
    have : ∀ a, (fun ζ => Iemp ζ a) =ᵐ[P] fun ζ => (Real.sqrt N)⁻¹ • ∑ i, J a (X ζ i) := fun a =>
      u5_ae_eq_of_pairing P (fun ζ => Iemp ζ a) (fun ζ => (Real.sqrt N)⁻¹ • ∑ i, J a (X ζ i))
        (fun φ hφ => by
          filter_upwards [hIemp a φ hφ] with ζ hζ
          rw [hζ]
          exact (u5_pairing_sum hN A μ (ψ a) (J a) (fun φ hφ => (hψ a φ hφ).1) (hJ a) (X ζ) φ hφ).symm)
    have hall : ∀ᵐ ζ ∂P, ∀ a, Iemp ζ a = (Real.sqrt N)⁻¹ • ∑ i, J a (X ζ i) := ae_all_iff.2 this
    filter_upwards [hall] with ζ hζ
    ext a
    rw [hS₀a]
    exact hζ a
  have hlawE : law P Iemp = P.map S₀ := Measure.map_congr hae
  -- the assembly
  have hIl := fun (L : ℕ) (w : Fin L → PiLp 2 (fun _ : Fin p => HNeg d (Γ : ℝ))) (hw : ∀ c, w c ∈ u5_Rpi (d := d) (Γ : ℝ) p) =>
    u5_coords_law_multi A μ ψ (fun a φ hφ => (hψ a φ hφ).1) J hJ P' η hη.1 hη.2 I hI L w hw
  have hmean : ∀ w ∈ u5_Rpi (d := d) (Γ : ℝ) p, ∫ x, inner ℝ w (Jp x) ∂μ = 0 := by
    intro w hw
    have hint : ∀ a, Integrable (fun x => inner ℝ (w a) (J a x)) μ := fun a =>
      Integrable.of_bound ((measurable_const.inner (hJc a).measurable).aestronglyMeasurable)
        (‖w a‖ * (2 * A * Kp)) (ae_of_all _ fun x => by
          rw [Real.norm_eq_abs]
          exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hJb a x) (norm_nonneg _)))
    have : ∀ x, inner ℝ w (Jp x) = ∑ a, inner ℝ (w a) (J a x) := fun x => by
      rw [hJp, PiLp.inner_apply]
    simp_rw [this]
    rw [integral_finsetSum _ fun a _ => hint a]
    exact Finset.sum_eq_zero fun a _ => u5_hmean A μ (ψ a) (fun φ hφ => (hψ a φ hφ).1) (J a) (hJ a) _ (hw a)
  obtain ⟨hW, hmS, hmI⟩ := u5_assembly (E := PiLp 2 (fun _ : Fin p => HNeg d (Γ : ℝ))) hd hN μ hμ2 hm (u5_Rpi (d := d) (Γ : ℝ) p)
    (u5_Rpi_orth _ _) Jp hJpm hb0 hΛ0 hJpb hJpL hmean P X hXm hXl P' I hIm' hIl
  set Cc : ℝ := max (3 * u5_C0 d m₂ * (Real.sqrt p * max K 0)) (8 * p * (max K 0) ^ 2) with hCc
  have hmomE : ∫⁻ ζ, ‖Iemp ζ‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal ((Real.sqrt p * (2 * A * Kp)) ^ 2) := by
    rw [lintegral_congr_ae (hae.mono fun ζ h => by rw [h])]
    exact hmS
  have hC0 := u5_C0_nonneg d m₂
  have hCc0 : 0 ≤ Cc := le_trans (by positivity) (le_max_left _ _)
  refine ⟨fun h3 => ?_, ?_⟩
  · have hlog := u5_log_ge_one h3
    have hrpow : 1 ≤ Real.log N ^ (1 / (2 * (d : ℝ) + 5)) :=
      Real.one_le_rpow hlog (by positivity)
    have hNa : 0 ≤ (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) := by positivity
    have hX0 : 0 ≤ Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
        Real.log N ^ (1 / (2 * (d : ℝ) + 5)) := by positivity
    have hmain : u5_C0 d m₂ * (Real.sqrt p * (A * Kp) + Real.sqrt p * (2 * A * Kp)) *
        (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) ≤
        Cc * A * (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10))) *
          Real.log N ^ (1 / (2 * (d : ℝ) + 5)) := by
      have h1 : u5_C0 d m₂ * (Real.sqrt p * (A * Kp) + Real.sqrt p * (2 * A * Kp)) ≤ Cc * A := by
        have : 3 * u5_C0 d m₂ * (Real.sqrt p * Kp) ≤ Cc := le_max_left _ _
        nlinarith [this, hA0]
      calc u5_C0 d m₂ * (Real.sqrt p * (A * Kp) + Real.sqrt p * (2 * A * Kp)) *
            (N : ℝ) ^ (-(1 / (4 * (d : ℝ) + 10)))
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
  · have h1 : ENNReal.ofReal ((Real.sqrt p * (2 * A * Kp)) ^ 2) +
        ENNReal.ofReal ((Real.sqrt p * (2 * A * Kp)) ^ 2) ≤ ENNReal.ofReal Cc := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have : 8 * p * Kp ^ 2 ≤ Cc := le_max_right _ _
      have hA2 : A ^ 2 ≤ 1 := by nlinarith
      have hp : Real.sqrt p ^ 2 = p := Real.sq_sqrt (Nat.cast_nonneg p)
      have e : (Real.sqrt p * (2 * A * Kp)) ^ 2 + (Real.sqrt p * (2 * A * Kp)) ^ 2 =
          8 * p * (A ^ 2 * Kp ^ 2) := by
        rw [mul_pow, hp]; ring
      rw [e]
      have : 0 ≤ (p : ℝ) * Kp ^ 2 := by positivity
      nlinarith [mul_nonneg this (sub_nonneg.2 hA2)]
    exact (add_le_add hmomE hmI).trans h1
