import HRS.MS.Canon
import HRS.MS.ThmConsAux1
import HRS.MS.LogBndAux1

/-!
# CAN2 (part 1): clause 1 of `euc_thermal_canonical` and of `logThermal_canonical`

`thermalDensity d s a β` solves the thermal equation (`HRS.Whole.IsThermalDensity`, from the merged
`thermalDensity_spec_proof` / `logThermalDensity_spec_proof`), the kernel `rieszKernel d s` is even, and
`y ↦ g (x - y)` is `thermalMeasure`-integrable for every `x` (K1 against `γ` for `s > 0`, K1 for `K̃` and `γ̄` for
`s = 0`, using `ρ ≤ M γ`, resp. `ρ ≤ M γ̄`).  Then `HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof` applies.

Exports: `can2_clause1_pos`, `can2_clause1_log`, and the thermal-density facts used by part 2.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Can2

open HRS.Whole HRS.MS.Thm

variable {d : ℕ}

lemma can2_rieszKernel_neg (s : ℝ) (x : Euc d) : rieszKernel d s (-x) = rieszKernel d s x := by
  simp [rieszKernel]

/-- `thermalDensity` is a thermal density for `0 < s < d`. -/
lemma can2_isThermalDensity_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) :
    HRS.Whole.IsThermalDensity (rieszKernel d s) (confinement a) β (thermalDensity d s a β) := by
  obtain ⟨⟨ρ, hρ, _⟩, _, _⟩ := thermalDensity_spec_proof (d := d) (s := s) hd hs0 hsd a β ha hβ
  have hex : ∃ ρ, HRS.Whole.IsThermalEquilibrium d s a β ρ := ⟨ρ, hρ⟩
  have hτ : HRS.Whole.IsThermalEquilibrium d s a β (thermalDensity d s a β) := by
    unfold thermalDensity
    rw [dif_pos hex]
    exact hex.choose_spec
  exact hτ.2

/-- `thermalDensity` is a thermal density for `s = 0`. -/
lemma can2_isThermalDensity_log (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    HRS.Whole.IsThermalDensity (rieszKernel d 0) (confinement a) β (thermalDensity d 0 a β) := by
  obtain ⟨⟨ρ, hρ, _⟩, _, _⟩ := logThermalDensity_spec_proof (d := d) hd a β ha hβ
  have hex : ∃ ρ, HRS.Whole.IsThermalEquilibrium d 0 a β ρ := ⟨ρ, hρ⟩
  have hτ : HRS.Whole.IsThermalEquilibrium d 0 a β (thermalDensity d 0 a β) := by
    unfold thermalDensity
    rw [dif_pos hex]
    exact hex.choose_spec
  exact hτ.2

/-- Clause 1 of `euc_thermal_canonical`. -/
theorem can2_clause1_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {a β : ℝ}
    (ha : 0 < a) (hβ : 0 < β) (N : ℕ) :
    HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β =
      HRS.Whole.modulatedGibbs (rieszKernel d s) N β (thermalMeasure d s a β) := by
  have hd1 : 1 ≤ d := by omega
  have hth := can2_isThermalDensity_pos hd hs0 hsd ha hβ
  obtain ⟨_, c, C, hc, hC, hbd⟩ := cb_thermal_two_sided hd1 hs0 hsd ha hβ
  obtain ⟨B, _, hB⟩ := convMeasure_bound_of_le hd1 hs0 hsd ha hβ
  have hint : ∀ x, Integrable (fun y => rieszKernel d s (x - y))
      (HRS.Whole.withDensityReal (thermalDensity d s a β)) := fun x =>
    (hB C (thermalDensity d s a β) hth.1 hC.le (fun y => (hbd y).2) x).1
  exact HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof (rieszKernel d s) (confinement a) β
    (thermalDensity d s a β) hth (fun x => can2_rieszKernel_neg s x) hint

/-- Integrability of `y ↦ g (x - y)` against a density `ρ ≤ M γ̄` (`s = 0`). -/
lemma can2_hint_log (hd : 1 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : 0 ≤ M) (hle : ∀ x, ρ x ≤ M * t67gammaBar d a β x)
    (x : Euc d) :
    Integrable (fun y => rieszKernel d 0 (x - y)) (HRS.Whole.withDensityReal ρ) := by
  rw [HRS.Whole.withDensityReal, integrable_withDensity_iff_integrable_smul'
    hρ.measurable.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  obtain ⟨B, hB⟩ := t67_k1 hd ha hβ
  have hK := (hB x).1
  have hγi := t67gammaBar_integrable (d := d) ha hβ
  have hlγ := t67_l_gammaBar_integrable (d := d) ha hβ
  have hmaj : Integrable fun y : Euc d => M * (t67K d x y * t67gammaBar d a β y +
      ((1 / 2) * t67l x + (1 / 2) * Real.log 2) * t67gammaBar d a β y +
        (1 / 2) * (t67l y * t67gammaBar d a β y)) :=
    ((hK.add (hγi.const_mul _)).add (hlγ.const_mul _)).const_mul M
  have hgm : Measurable fun y : Euc d => rieszKernel d 0 (x - y) :=
    t67_g_measurable.comp (measurable_const.sub measurable_id)
  refine Integrable.mono' hmaj ?_ (ae_of_all _ fun y => ?_)
  · exact (hρ.measurable.ennreal_ofReal.ennreal_toReal.smul hgm).aestronglyMeasurable
  · have hρ0 := hρ.nonneg y
    have hlx := t67l_nonneg x
    have hly := t67l_nonneg y
    have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hK0 := t67K_nonneg (d := d) x y
    have hγ0 := (t67gammaBar_pos (d := d) ha hβ y).le
    have hgeq : rieszKernel d 0 (x - y) = t67K d x y - (1 / 2) * t67l x - (1 / 2) * t67l y
        - (1 / 2) * Real.log 2 := by
      unfold t67K; ring
    have habs : |rieszKernel d 0 (x - y)| ≤ t67K d x y + ((1 / 2) * t67l x + (1 / 2) * Real.log 2)
        + (1 / 2) * t67l y := by
      rw [abs_le]; constructor <;> rw [hgeq] <;> nlinarith
    rw [Real.norm_eq_abs, smul_eq_mul, ENNReal.toReal_ofReal hρ0, abs_mul, abs_of_nonneg hρ0]
    have hs : 0 ≤ t67K d x y + ((1 / 2) * t67l x + (1 / 2) * Real.log 2) + (1 / 2) * t67l y := by
      linarith
    calc ρ y * |rieszKernel d 0 (x - y)|
        ≤ (M * t67gammaBar d a β y) *
          (t67K d x y + ((1 / 2) * t67l x + (1 / 2) * Real.log 2) + (1 / 2) * t67l y) :=
          mul_le_mul (hle y) habs (abs_nonneg _) (mul_nonneg hM hγ0)
      _ = _ := by ring

/-- Clause 1 of `logThermal_canonical`. -/
theorem can2_clause1_log (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (N : ℕ) :
    HRS.Whole.canonicalGibbs (rieszKernel d 0) (confinement a) N β =
      HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (thermalMeasure d 0 a β) := by
  have hd1 : 1 ≤ d := by omega
  have hth := can2_isThermalDensity_log hd ha hβ
  obtain ⟨B, M, μ, hS, hM, hρC, hρfix, hpt⟩ := clb_thermalDensity_eq_rep hd1 ha hβ
  have hle : ∀ x, thermalDensity d 0 a β x ≤ M * t67gammaBar d a β x := fun x =>
    (hpt x) ▸ hρC.2 x
  have hint : ∀ x, Integrable (fun y => rieszKernel d 0 (x - y))
      (HRS.Whole.withDensityReal (thermalDensity d 0 a β)) := fun x =>
    can2_hint_log hd1 ha hβ hth.1 (by linarith) hle x
  exact HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof (rieszKernel d 0) (confinement a) β
    (thermalDensity d 0 a β) hth (fun x => can2_rieszKernel_neg 0 x) hint

end HRS.MS.Can2

end
