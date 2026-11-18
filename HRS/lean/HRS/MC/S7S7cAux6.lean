import HRS.MC.S7S7cAux5

/-!
# Packet `s7_S7c_hilbert_stein`, helper 6: `E |B_N^v| <= C (sum L_j)`

The argument of `sed_B4b_energy_proof` (`L^2` bound under the product law, Holder transfer with exponent `2`)
with explicit constants: `B = Y - E Y` with `Y = N mE(h_v) + J/2`, `E_Q |Y| <= C2 (3 ||h_v||_2^2)^{1/2}`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ}

theorem s7c_B_L1 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (v : Fin d → Torus d → ℝ) (L : Fin d → ℝ), (∀ k, 0 ≤ L k) →
      (∀ k, HRS.KernelGrad.IsLipschitz (L k) (v k)) → (∀ j, Torus.IsSmooth (v j)) →
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))
          (sed_Q d s N γ ρ) ∧
        Integrable (sed_B d s ρ γ v) (sed_Q d s N γ ρ) ∧
        ∫ X, |sed_B d s ρ γ v X| ∂(sed_Q d s N γ ρ) ≤ CB * ∑ k, L k := by
  haveI hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨C2, hC2, T2⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof hd hs0 hs hγ hρ (r := 2)
    (by norm_num)
  obtain ⟨G, hG0, hG⟩ := s7c_L2_bound hd hs0 hs hρ
  refine ⟨2 * C2 * Real.sqrt (3 * G), by positivity, fun v L hL0 hL hv N hN => ?_⟩
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hS : 0 ≤ ∑ k, L k := Finset.sum_nonneg fun k _ => hL0 k
  set S : ℝ := ∑ k, L k with hSdef
  set J : ℝ := ∫ x, ∫ y, Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hJ
  set K : ℝ := 3 * ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ)
    with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (by norm_num) (integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _)
  have hKle : K ≤ 3 * G * S ^ 2 := by
    have := hG v L hL0 hL hv
    rw [hK]; nlinarith
  set A : ℝ := C2 * K ^ (1 / 2 : ℝ) with hAdef
  have hA0 : 0 ≤ A := mul_nonneg hC2 (Real.rpow_nonneg hK0 _)
  have hAle : A ≤ C2 * Real.sqrt (3 * G) * S := by
    have h1 : K ^ (1 / 2 : ℝ) ≤ (3 * G * S ^ 2) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hK0 hKle (by norm_num)
    have h2 : (3 * G * S ^ 2) ^ (1 / 2 : ℝ) = Real.sqrt (3 * G) * S := by
      rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_sq hS]
    calc A = C2 * K ^ (1 / 2 : ℝ) := rfl
      _ ≤ C2 * (Real.sqrt (3 * G) * S) := by rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hC2
      _ = _ := by ring
  obtain ⟨hYm, hYL, hYint⟩ := HRS.MC.SEdge.B4b.b4b_L2 hd hs0 hs hρ hv N hN
  set Y : Config d N → ℝ := HRS.MC.SEdge.B4b.b4b_Y d s ρ v N with hYdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hYsq : ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
      ENNReal.ofReal K := by
    rw [← ofReal_integral_eq_lintegral_ofReal hYL.integrable_sq
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hYint
  have hA : ∫⁻ X, ENNReal.ofReal |Y X| ∂(sed_Q d s N γ ρ) ≤ ENNReal.ofReal A := by
    have h1 := T2 N hN (fun X => ENNReal.ofReal |Y X|) hYm.abs.ennreal_ofReal
    have h2 : ∫⁻ X, (ENNReal.ofReal |Y X|) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)
        = ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) := by
      refine lintegral_congr fun X => ?_
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
    rw [h2] at h1
    refine h1.trans ?_
    calc ENNReal.ofReal C2 * (∫⁻ X, ENNReal.ofReal (Y X ^ 2)
          ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)) ^ (1 / (2 : ℝ))
        ≤ ENNReal.ofReal C2 * (ENNReal.ofReal K) ^ (1 / (2 : ℝ)) := by gcongr
      _ = ENNReal.ofReal A := by
        rw [hAdef, ENNReal.ofReal_mul hC2, ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num)]
  have hGY : Integrable Y (sed_Q d s N γ ρ) := by
    refine ⟨hYm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact lt_of_le_of_lt hA ENNReal.ofReal_lt_top
  have hYabs : ∫ X, |Y X| ∂(sed_Q d s N γ ρ) ≤ A := by
    have := ofReal_integral_eq_lintegral_ofReal hGY.abs
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    rw [← this] at hA
    exact (ENNReal.ofReal_le_ofReal_iff hA0).1 hA
  set c : ℝ := ∫ X, Y X ∂(sed_Q d s N γ ρ) with hc
  have hcA : |c| ≤ A := (abs_integral_le_integral_abs).trans hYabs
  have hmE : ∀ X, modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) =
      (N : ℝ)⁻¹ * (Y X - J / 2) := by
    intro X
    simp only [hYdef, HRS.MC.SEdge.B4b.b4b_Y, hJ]
    field_simp
    ring
  have hNmE : ∀ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) =
      Y X - J / 2 := by
    intro X
    rw [hmE X]
    field_simp
  have hint1 : Integrable (fun X : Config d N =>
      modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)) (sed_Q d s N γ ρ) := by
    have : (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)) =
        fun X => (N : ℝ)⁻¹ * (Y X - J / 2) := funext hmE
    rw [this]
    exact (hGY.sub (integrable_const _)).const_mul _
  have hint2 : ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
      ∂(sed_Q d s N γ ρ) = c - J / 2 := by
    simp_rw [hNmE]
    rw [integral_sub hGY (integrable_const _)]
    simp [hc]
  have hB : ∀ X, sed_B d s ρ γ v X = Y X - c := by
    intro X
    unfold sed_B
    have h3 : ∫ Z, modulatedEnergy (Q66.q66_hv d s v) Z (withDensityReal ρ)
        ∂(sed_Q d s N γ ρ) = (N : ℝ)⁻¹ * (c - J / 2) := by
      rw [← hint2, integral_const_mul]
      field_simp
    rw [h3, mul_sub, hNmE X]
    field_simp
    ring
  refine ⟨hint1, ?_, ?_⟩
  · have : sed_B d s ρ γ v = fun X => Y X - c := funext hB
    rw [this]
    exact hGY.sub (integrable_const _)
  · simp_rw [hB]
    have hint_abs : ∫ X, |Y X - c| ∂(sed_Q d s N γ ρ) ≤ ∫ X, (|Y X| + |c|) ∂(sed_Q d s N γ ρ) :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        (hGY.abs.add (integrable_const _)) (Filter.Eventually.of_forall fun X => abs_sub _ _)
    have : ∫ X, (|Y X| + |c|) ∂(sed_Q d s N γ ρ) = ∫ X, |Y X| ∂(sed_Q d s N γ ρ) + |c| := by
      rw [integral_add hGY.abs (integrable_const _)]; simp
    calc ∫ X, |Y X - c| ∂(sed_Q d s N γ ρ) ≤ 2 * A := by linarith
      _ ≤ 2 * (C2 * Real.sqrt (3 * G) * S) := by linarith
      _ = _ := by ring

end HRS.MC.Sec7.S7c

end
