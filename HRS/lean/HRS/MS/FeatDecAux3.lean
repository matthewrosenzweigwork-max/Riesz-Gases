import HRS.MS.FeatDecAux2
import HRS.MS.ThmSpec
import HRS.MS.EucRegH
import HRS.MS.UlWitTie
import HRS.MS.OrbFeatTie
import HRS.Whole.CriticalNoise

/-!
# S8.5 `feature_decay`, part 3 (S85 packet): the critical thermal setting

* `s85_thermal_eq`: any `IsThermalEquilibrium d s a β ρ` (`0 < s < d`) is the density `thermalDensity d s a β` (pointwise);
  hence the quantifier `∃ C, ∀ ρβ ...` of `feature_decay` is about one density.
* `s85_thermal_schwartz`: `thermalDensity` is a Schwartz probability density (`euc_thermal_regularity_proof`).
* `s85_crit_eq`: `critCoeff d a β ρ = (⟨d/2, -1, quadV (a • 1) 0, β⁻¹⟩).coeff (fun _ => ρ)` (the form of the UL witness).
* `s85_wse_of_rapid`: a rapidly decreasing smooth function has finite weighted sup norms.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S85

open HRS HRS.Whole HRS.MS.Ul HRS.MS.Adj

variable {d : ℕ}

theorem s85_thermal_eq (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < (d : ℝ)) (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) :
    ρ = thermalDensity d s a β ∧ IsThermalEquilibrium d s a β (thermalDensity d s a β) := by
  obtain ⟨⟨ρ0, hρ0, -⟩, -, hmin⟩ := HRS.MS.Thm.thermalDensity_spec_proof hd hs0 hsd a β ha hβ
  have hex : ∃ ρ, IsThermalEquilibrium d s a β ρ := ⟨ρ0, hρ0⟩
  have hτ : IsThermalEquilibrium d s a β (thermalDensity d s a β) := by
    unfold thermalDensity
    rw [dif_pos hex]
    exact hex.choose_spec
  have hae : ρ =ᵐ[volume] thermalDensity d s a β := hmin ρ hρ.1
  refine ⟨funext fun x => HRS.MS.Thm.thermalDensity_eq_pointwise hρ.2 hτ.2 hae x, hτ⟩

theorem s85_thermal_schwartz (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 < s) (hsd : s < (d : ℝ)) (ha : 0 < a)
    (hβ : 0 < β) : IsSchwartzDensity (thermalDensity d s a β) := by
  have hτ := (s85_thermal_eq hd hs0 hsd ha hβ (ρ := thermalDensity d s a β)
    (by
      obtain ⟨⟨ρ0, hρ0, -⟩, -, -⟩ := HRS.MS.Thm.thermalDensity_spec_proof hd hs0 hsd a β ha hβ
      have hex : ∃ ρ, IsThermalEquilibrium d s a β ρ := ⟨ρ0, hρ0⟩
      unfold thermalDensity
      rw [dif_pos hex]
      exact hex.choose_spec)).2
  obtain ⟨hsm, -, -, hder, -⟩ := HRS.MS.Thm.euc_thermal_regularity_proof hd hs0 hsd a β ha hβ
  refine ⟨hτ.1.1, ?_⟩
  have hb : 0 < β * a / 2 := by positivity
  refine ⟨⟨thermalDensity d s a β, hsm, ?_⟩, rfl⟩
  intro k n
  obtain ⟨Cn, hCn⟩ := hder n
  obtain ⟨C', hC'0, hC'⟩ := HRS.MS.Thm.rege_poly_gauss_bdd hb (k + n)
  refine ⟨max Cn 0 * C', fun x => ?_⟩
  have h1 := hCn x
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have e : Real.exp (-β * a * ‖x‖ ^ 2 / 2) = Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := by
    congr 1; ring
  rw [e] at h1
  have h2 : ‖x‖ ^ k ≤ (1 + ‖x‖) ^ k := pow_le_pow_left₀ hx0 (by linarith) k
  have h3 := hC' ‖x‖ hx0
  have h4 : (1 + ‖x‖) ^ (k + n) * Real.exp (-(β * a / 2) * ‖x‖ ^ 2) ≤ C' := by
    simpa using h3
  have hE : 0 ≤ Real.exp (-(β * a / 2) * ‖x‖ ^ 2) := (Real.exp_pos _).le
  have hCn0 : Cn ≤ max Cn 0 := le_max_left _ _
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (thermalDensity d s a β) x‖
      ≤ (1 + ‖x‖) ^ k * (Cn * (1 + ‖x‖) ^ n * Real.exp (-(β * a / 2) * ‖x‖ ^ 2)) := by
        apply mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ ≤ (1 + ‖x‖) ^ k * (max Cn 0 * (1 + ‖x‖) ^ n * Real.exp (-(β * a / 2) * ‖x‖ ^ 2)) := by
        gcongr
    _ = max Cn 0 * ((1 + ‖x‖) ^ (k + n) * Real.exp (-(β * a / 2) * ‖x‖ ^ 2)) := by
        rw [pow_add]; ring
    _ ≤ max Cn 0 * C' := mul_le_mul_of_nonneg_left h4 (le_max_right _ _)

theorem s85_crit_eq (a β : ℝ) (ρ : Euc d → ℝ) :
    critCoeff d a β ρ =
      (⟨(d : ℝ) / 2, -1, quadV (a • (1 : Matrix (Fin d) (Fin d) ℝ)) 0, β⁻¹⟩ : WholeDyn d).coeff
        (fun _ => ρ) := by
  unfold critCoeff quadraticGradientDyn
  congr 2
  funext x
  unfold confinement quadV Torus.matVec
  simp [Matrix.toEuclideanLin, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

theorem s85_wse_of_rapid {h : Euc d → ℝ} (hh : UlRapid h) (r : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ Λ : ℝ, weightedSupE r L h ≤ ENNReal.ofReal Λ := by
  choose C hC using fun m : ℕ => hh.2 m ⌈L⌉₊
  refine ⟨∑ m ∈ Finset.range (r + 1), max (C m) 0, ?_⟩
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun I => iSup_le fun x => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hj : (j : ℕ) ≤ r := Nat.lt_succ_iff.mp j.2
  have hw : 0 < 1 + ‖x‖ := by positivity
  have h1 : jbracket x ^ L ≤ (1 + ‖x‖) ^ (⌈L⌉₊ : ℝ) := by
    calc jbracket x ^ L ≤ (1 + ‖x‖) ^ L :=
          Real.rpow_le_rpow (u2_jb_pos x).le (u2_jb_le x) hL
      _ ≤ (1 + ‖x‖) ^ (⌈L⌉₊ : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (Nat.le_ceil L)
  have h2 : |partialDeriv I h x| ≤ ‖iteratedFDeriv ℝ (j : ℕ) h x‖ := HRS.MS.Lc.lc4_partial_le (j : ℕ) I x
  have h3 := hC (j : ℕ) x
  have hCm : max (C (j : ℕ)) 0 ≤ ∑ m ∈ Finset.range (r + 1), max (C m) 0 :=
    Finset.single_le_sum (f := fun m => max (C m) 0) (fun m _ => le_max_right _ _)
      (Finset.mem_range.mpr (by omega))
  calc jbracket x ^ L * |partialDeriv I h x|
      ≤ (1 + ‖x‖) ^ (⌈L⌉₊ : ℝ) * ‖iteratedFDeriv ℝ (j : ℕ) h x‖ :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = (1 + ‖x‖) ^ ⌈L⌉₊ * ‖iteratedFDeriv ℝ (j : ℕ) h x‖ := by
        rw [Real.rpow_natCast]
    _ ≤ C (j : ℕ) := h3
    _ ≤ max (C (j : ℕ)) 0 := le_max_left _ _
    _ ≤ _ := hCm

end HRS.MS.S85
