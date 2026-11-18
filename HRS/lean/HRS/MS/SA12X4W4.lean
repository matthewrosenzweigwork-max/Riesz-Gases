import HRS.MS.SA12X4W3
import HRS.MS.SA12X3C15J

/-!
# S.A.12 (SA12X4) W4: the weighted flowed-cell mass is bounded by the weighted cell energy

`∑_{z'} ω^{unit}_{z'} 𝓜_{z'}(τ) ≤ C ∑_z ω^{fine}_z 𝓕_z(τ)` (the weighted form of `sa12x3_cellMass_le`, from the second
conjunct of `fine_cell_cover`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x4_cellMass_weighted (hd : 1 ≤ d) (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ψ : ℝ → Euc d → Euc d) (τ : ℝ), Function.Bijective (Ψ τ) → Continuous (Ψ τ) →
      Continuous (Function.invFun (Ψ τ)) → ∀ F : Euc d → ℝ, ContDiff ℝ ∞ F →
      (∀ (z : Fin d → ℤ) {j : ℕ} (idx : Fin j → Fin d),
        Integrable (fun x => (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx F x) ^ 2)) →
      ∑' z', ENNReal.ofReal (cellWeight d z') * ENNReal.ofReal (cellMass m Ψ τ z' F) ≤
        ENNReal.ofReal C * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d z) F) := by
  classical
  obtain ⟨N, C, hN, hC, hcov⟩ := fine_cell_cover hd χ hχ
  refine ⟨C, hC, fun Ψ τ hbij hc hci F hF hint => ?_⟩
  have hnn : ∀ (j : ℕ) (idx : Fin j → Fin d) (z' : Fin d → ℤ), 0 ≤ ∫ x in flowCell Ψ τ z', (partialDeriv idx F x) ^ 2 :=
    fun j idx z' => setIntegral_nonneg_of_ae_restrict (Filter.Eventually.of_forall fun x => sq_nonneg _)
  -- per jet
  have hjet : ∀ (j : ℕ) (idx : Fin j → Fin d),
      ∑' z', ENNReal.ofReal (cellWeight d z') * ENNReal.ofReal (∫ x in flowCell Ψ τ z', (partialDeriv idx F x) ^ 2) ≤
        ENNReal.ofReal C * ∑' z, ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) *
          ENNReal.ofReal (∫ x, (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx F x) ^ 2) := by
    intro j idx
    have hg : Measurable (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous.measurable
    have h1 := (hcov Ψ τ hbij hc hci (partialDeriv idx F) hg).2
    calc _ ≤ ∑' z', ENNReal.ofReal (cellWeight d z') * ∫⁻ x in flowCell Ψ τ z', ENNReal.ofReal ((partialDeriv idx F x) ^ 2) := by
          refine ENNReal.tsum_le_tsum fun z' => ?_
          gcongr
          by_cases hi : IntegrableOn (fun x => (partialDeriv idx F x) ^ 2) (flowCell Ψ τ z')
          · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => sq_nonneg _)]
          · rw [integral_undef hi]; simp
      _ ≤ _ := by
          refine h1.trans (le_of_eq ?_)
          congr 1
          refine tsum_congr fun z => ?_
          congr 1
          exact ofReal_integral_eq_lintegral_ofReal (hint z idx) (Filter.Eventually.of_forall fun x => sq_nonneg _) |>.symm
  -- sum over jets
  have hcoef : ∀ j : ℕ, (0 : ℝ) ≤ (Nat.choose m j : ℝ) := fun j => Nat.cast_nonneg _
  have hmass : ∀ z', ENNReal.ofReal (cellMass m Ψ τ z' F) =
      ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (Nat.choose m j : ℝ) *
        ∑ idx : Fin j → Fin d, ENNReal.ofReal (∫ x in flowCell Ψ τ z', (partialDeriv idx F x) ^ 2) := by
    intro z'
    unfold cellMass
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hcoef j) (Finset.sum_nonneg fun idx _ => hnn j idx z')]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul (hcoef j), ENNReal.ofReal_sum_of_nonneg fun idx _ => hnn j idx z']
  have henergy : ∀ z : Fin d → ℤ, ENNReal.ofReal (cellEnergy m χ Ψ τ (cellPt d z) F) =
      ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (Nat.choose m j : ℝ) *
        ∑ idx : Fin j → Fin d, ENNReal.ofReal (∫ x, (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx F x) ^ 2) := by
    intro z
    unfold cellEnergy jetSq
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg (hcoef j) (Finset.sum_nonneg fun idx _ =>
      integral_nonneg fun x => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul (hcoef j), ENNReal.ofReal_sum_of_nonneg fun idx _ => integral_nonneg fun x => sq_nonneg _]
  have hswap : ∀ (wt : (Fin d → ℤ) → ℝ≥0∞) (a : ∀ j : ℕ, (Fin j → Fin d) → (Fin d → ℤ) → ℝ≥0∞),
      ∑' z, wt z * ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, a j idx z =
        ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑' z, wt z * a j idx z := by
    intro wt a
    calc ∑' z, wt z * ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, a j idx z
        = ∑' z, ∑ j ∈ Finset.range (m + 1), ENNReal.ofReal (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, wt z * a j idx z := by
          refine tsum_congr fun z => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_left_comm, Finset.mul_sum]
      _ = ∑ j ∈ Finset.range (m + 1), ∑' z, ENNReal.ofReal (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, wt z * a j idx z :=
          Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)
      _ = _ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have e1 := hswap (fun z' => ENNReal.ofReal (cellWeight d z'))
    (fun j idx z' => ENNReal.ofReal (∫ x in flowCell Ψ τ z', (partialDeriv idx F x) ^ 2))
  have e2 := hswap (fun z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))))
    (fun j idx z => ENNReal.ofReal (∫ x, (advCutoff χ Ψ τ (cellPt d z) x * partialDeriv idx F x) ^ 2))
  simp only [← hmass] at e1
  simp only [← henergy] at e2
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_left_comm (ENNReal.ofReal C)]
  gcongr
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun idx _ => hjet j idx

end HRS.MH.AdjointRd.Phase2SA12X4
