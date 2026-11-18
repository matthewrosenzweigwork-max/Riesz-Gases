import HRS.MC.S7S7cAux4
import HRS.MC.SEdgeB4b
import HRS.MC.SEdgeB2b

/-!
# Packet `s7_S7c_hilbert_stein`, helper 5: `E |B_{N,k}| <= C b_k`

The envelope of `h_v` with explicit dependence on the Lipschitz constants of `v`, the resulting `L^2` bound
for the pair kernel, and the argument of `sed_B4b_energy` (Holder transfer from the product law, exponent `2`)
with explicit constants.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ}

theorem s7c_env (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) :
    ∃ K c : ℝ, 0 ≤ K ∧ (∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + c) ∧
      ∀ (v : Fin d → Torus d → ℝ) (L : Fin d → ℝ), (∀ k, 0 ≤ L k) →
        (∀ k, HRS.KernelGrad.IsLipschitz (L k) (v k)) →
        ∀ x y : Torus d, x ≠ y →
          |Q66.q66_hv d s v x y| ≤ K * (∑ k, L k) * (periodicRiesz d s (x - y) + c) := by
  have hdpos : (0 : ℝ) < d := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hsd : s < (d : ℝ) := by linarith
  obtain ⟨Cg, hCg⟩ := HRS.Quad.periodicRiesz_lower_env hd hs0 hsd
  obtain ⟨C, hC⟩ := HRS.KernelGrad.periodicRieszGrad_bound_tdist hd hs0 hsd
  have hg1 : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + Cg := fun z hz => by
    have := HRS.Quad.one_le_envT (d := d) (s := s) z
    have := hCg z hz
    linarith
  refine ⟨max C 0 * (1 + d), Cg, by positivity, hg1, fun v L hL0 hL x y hxy => ?_⟩
  set z := x - y with hzdef
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy
  set t := HRS.KernelGrad.tdist z 0 with ht
  have htpos : 0 < t := by
    rcases (HRS.KernelGrad.tdist_nonneg z 0).lt_or_eq with h | h
    · exact h
    · exact absurd ((HRS.Commutator.EnergyAux.tdist_eq_zero_iff z).1 h.symm) hz
  have htd : t ≤ d := HRS.Commutator.SliceAux.tdist_le_dim z
  have hxy_t : HRS.KernelGrad.tdist x y = t := HRS.KernelGrad.tdist_eq_sub_zero x y
  have hgrad : ∀ k, |(periodicRieszGrad d s z) k| ≤ max C 0 * (t ^ (-s - 1) + 1) := fun k => by
    have h1 : |(periodicRieszGrad d s z) k| ≤ ‖periodicRieszGrad d s z‖ := by
      have := PiLp.norm_apply_le (periodicRieszGrad d s z) k
      rwa [Real.norm_eq_abs] at this
    refine h1.trans ((hC z hz).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _)
      (by positivity)
  have hterm : ∀ k, |(v k x - v k y) * (periodicRieszGrad d s (x - y)) k| ≤
      L k * (max C 0 * (t ^ (-s) + t)) := fun k => by
    rw [abs_mul]
    have h1 : |v k x - v k y| ≤ L k * t := by
      have := hL k x y
      rwa [hxy_t] at this
    have h2 := hgrad k
    have h3 : t * (t ^ (-s - 1) + 1) = t ^ (-s) + t := by
      have : t ^ (-s - 1 + 1) = t ^ (-s - 1) * t := Real.rpow_add_one htpos.ne' _
      rw [show -s - 1 + 1 = -s by ring] at this
      rw [this]; ring
    calc |v k x - v k y| * |(periodicRieszGrad d s (x - y)) k|
        ≤ (L k * t) * (max C 0 * (t ^ (-s - 1) + 1)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg (hL0 k) htpos.le)
      _ = L k * (max C 0 * (t * (t ^ (-s - 1) + 1))) := by ring
      _ = _ := by rw [h3]
  have hsum : |Q66.q66_hv d s v x y| ≤ (∑ k, L k) * (max C 0 * (t ^ (-s) + t)) := by
    unfold Q66.q66_hv
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun k _ => hterm k
  have hg := hCg z hz
  have hg1z := hg1 z hz
  have hr := HRS.MC.SEdge.B2a.b2a_rpow_le_envT (d := d) (s := s) z
  have hmax : 0 ≤ max C 0 := le_max_right _ _
  have hLs : 0 ≤ ∑ k, L k := Finset.sum_nonneg fun k _ => hL0 k
  have hpos : 0 ≤ (∑ k, L k) * max C 0 := mul_nonneg hLs hmax
  have hbound : t ^ (-s) + t ≤ (1 + d) * (periodicRiesz d s z + Cg) := by
    have : HRS.Quad.envT s z ≤ periodicRiesz d s z + Cg := by linarith
    nlinarith
  calc |Q66.q66_hv d s v x y| ≤ (∑ k, L k) * (max C 0 * (t ^ (-s) + t)) := hsum
    _ = ((∑ k, L k) * max C 0) * (t ^ (-s) + t) := by ring
    _ ≤ ((∑ k, L k) * max C 0) * ((1 + d) * (periodicRiesz d s z + Cg)) :=
        mul_le_mul_of_nonneg_left hbound hpos
    _ = _ := by ring

theorem s7c_L2_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) :
    ∃ G : ℝ, 0 ≤ G ∧ ∀ (v : Fin d → Torus d → ℝ) (L : Fin d → ℝ), (∀ k, 0 ≤ L k) →
      (∀ k, HRS.KernelGrad.IsLipschitz (L k) (v k)) → (∀ j, Torus.IsSmooth (v j)) →
      ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ) ≤
        G * (∑ k, L k) ^ 2 := by
  haveI := isProb_withDensityReal hρ.density
  obtain ⟨K, c, hK0, -, henv⟩ := s7c_env hd hs0 hs
  obtain ⟨Λ, -, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  have hg2 := HRS.periodicRiesz_sq_integrable hd hs0 hs ρ hρ.density Λ hΛ
  set I : ℝ := ∫ z : Torus d × Torus d, periodicRiesz d s (z.1 - z.2) ^ 2
    ∂((withDensityReal ρ).prod (withDensityReal ρ)) with hI
  refine ⟨2 * K ^ 2 * (I + c ^ 2), ?_, fun v L hL0 hL hv => ?_⟩
  · have : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
    positivity
  have hS : 0 ≤ ∑ k, L k := Finset.sum_nonneg fun k _ => hL0 k
  have hint := HRS.MC.SEdge.B2b.sed_B2b_hs_proof hd hs0 hs hρ hv
  set S := ∑ k, L k with hSdef
  have hdom : Integrable (fun z : Torus d × Torus d =>
      2 * (K * S) ^ 2 * (periodicRiesz d s (z.1 - z.2) ^ 2) + 2 * (K * S) ^ 2 * c ^ 2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    (hg2.const_mul _).add (integrable_const _)
  rw [← integral_prod (fun z : Torus d × Torus d => Q66.q66_hv d s v z.1 z.2 ^ 2) hint]
  have hle : ∫ z : Torus d × Torus d, Q66.q66_hv d s v z.1 z.2 ^ 2
      ∂((withDensityReal ρ).prod (withDensityReal ρ)) ≤
      ∫ z : Torus d × Torus d, (2 * (K * S) ^ 2 * (periodicRiesz d s (z.1 - z.2) ^ 2) +
        2 * (K * S) ^ 2 * c ^ 2) ∂((withDensityReal ρ).prod (withDensityReal ρ)) := by
    refine integral_mono_ae hint hdom ?_
    filter_upwards [HRS.Parx.PXFID.ae_ne_prod (by omega) hρ.density] with z hz
    have h1 := henv v L hL0 hL z.1 z.2 hz
    calc Q66.q66_hv d s v z.1 z.2 ^ 2 = |Q66.q66_hv d s v z.1 z.2| ^ 2 := (sq_abs _).symm
      _ ≤ (K * S * (periodicRiesz d s (z.1 - z.2) + c)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = (K * S) ^ 2 * (periodicRiesz d s (z.1 - z.2) + c) ^ 2 := by ring
      _ ≤ _ := by
          nlinarith [sq_nonneg (K * S), mul_nonneg (sq_nonneg (K * S))
            (sq_nonneg (periodicRiesz d s (z.1 - z.2) - c))]
  refine hle.trans (le_of_eq ?_)
  rw [integral_add (hg2.const_mul _) (integrable_const _), integral_const_mul, integral_const]
  simp only [probReal_univ, one_smul]
  rw [← hI]
  ring

end HRS.MC.Sec7.S7c

end
