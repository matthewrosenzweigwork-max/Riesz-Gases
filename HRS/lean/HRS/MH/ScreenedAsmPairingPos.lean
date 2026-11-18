import HRS.MH.ScreenedAsmLocal
import HRS.MH.ScreenedS5c
import HRS.MH.ScreenedK5

/-!
# Assembly `screened_pairing_pos` (S.B.4(iii), `s > d - 1`)

`aψ ∈ H^σ` (`σ = s + 1 - d ∈ (0,1)`) by `mult_sobolev_proof` with `B = Λ`; the representative `w'` of
`screened_local_global_proof` equals `u` a.e. (`gk_unique_proof`); Cauchy-Schwarz.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma apos_holder {f g : Euc d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    ENNReal.ofReal |∫ x, f x * g x| ≤ eLpNorm f 2 volume * eLpNorm g 2 volume := by
  have h1 : eLpNorm (f • g) 1 volume ≤ eLpNorm f 2 volume * eLpNorm g 2 volume :=
    eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hf.aestronglyMeasurable
      hg.aestronglyMeasurable
  have hm : AEStronglyMeasurable (f • g) volume := hf.aestronglyMeasurable.smul hg.aestronglyMeasurable
  calc ENNReal.ofReal |∫ x, f x * g x| = ‖∫ x, f x * g x‖ₑ := by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    _ ≤ ∫⁻ x, ‖f x * g x‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (f • g) 1 volume := by
        rw [eLpNorm_one_eq_lintegral_enorm hm]; rfl
    _ ≤ _ := h1

theorem screened_pairing_pos_proof : type_of% @HRS.Whole.screened_pairing_pos := by
  intro d hd s hsd hs1
  have hσ0 : 0 < s + 1 - d := by linarith
  have hσ1 : s + 1 - d < 1 := by linarith
  obtain ⟨Cm, hCm0, hCm⟩ := mult_sobolev_proof hd hσ0.le hσ1
  obtain ⟨Cg, hCg⟩ := screened_local_global_proof hd hsd hs1.le
  refine ⟨max Cg 0 * Cm, fun La Λ a hL hΛ i ψ w u hψ hw hψS hu => ?_⟩
  have hLa : 0 ≤ La := s5b_La_nonneg hd hL
  have hjb : ∀ x : Euc d, 1 ≤ jbracket x ^ ((d : ℝ) + 3) := fun x => by
    refine Real.one_le_rpow ?_ (by positivity)
    unfold jbracket
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith [sq_nonneg ‖x‖]
  have hab : ∀ x, |a x| ≤ Λ := fun x =>
    calc |a x| ≤ jbracket x ^ ((d : ℝ) + 3) * |a x| :=
          le_mul_of_one_le_left (abs_nonneg _) (hjb x)
      _ ≤ Λ := hΛ x
  have hΛ0 : 0 ≤ Λ := le_trans (abs_nonneg _) (hab 0)
  have hN : sobolevNormE (s + 1 - d) (fun y => a y * ψ y) ≤
      ENNReal.ofReal (Cm * (La + Λ)) * sobolevNormE (s + 1 - d) ψ := hCm La Λ a ψ hL hab
  have hNfin : sobolevNormE (s + 1 - d) (fun y => a y * ψ y) < ⊤ :=
    lt_of_le_of_lt hN (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hψS)
  obtain ⟨w', hrep, hw'2, hw'n⟩ := hCg i _ hNfin
  have hae : w' =ᵐ[volume] u := gk_unique_proof i hrep hu
  have hu2 : MemLp u 2 volume := hw'2.ae_eq hae
  refine ⟨hu2, ?_⟩
  have hint : ∫ x, u x * w x = ∫ x, w' x * w x :=
    integral_congr_ae (hae.mono fun x hx => by show u x * w x = w' x * w x; rw [hx])
  rw [hint]
  calc ENNReal.ofReal |∫ x, w' x * w x| ≤ eLpNorm w' 2 volume * eLpNorm w 2 volume :=
        apos_holder hw'2 hw
    _ ≤ (ENNReal.ofReal Cg * sobolevNormE (s + 1 - d) (fun y => a y * ψ y)) * eLpNorm w 2 volume := by
        gcongr
    _ ≤ (ENNReal.ofReal (max Cg 0) * (ENNReal.ofReal (Cm * (La + Λ)) * sobolevNormE (s + 1 - d) ψ)) *
          eLpNorm w 2 volume := by
        gcongr
        · exact le_max_left _ _
    _ = ENNReal.ofReal (max Cg 0 * Cm * (La + Λ)) * sobolevNormE (s + 1 - d) ψ * eLpNorm w 2 volume := by
        rw [show max Cg 0 * Cm * (La + Λ) = max Cg 0 * (Cm * (La + Λ)) by ring,
          ENNReal.ofReal_mul (le_max_right _ _)]
        ring

end HRS.MH.Screened
