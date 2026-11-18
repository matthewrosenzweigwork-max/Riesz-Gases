import HRS.MS.SA12C31

/-!
# S.A.12(c), packet E7.05 (part 4): averaged energies and dissipations; Young splitting of a jet pairing
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12c_avg_jetSq {L : ℝ} (hL : 0 < L) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (m : ℕ)
    {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) (p : Euc d) :
    Integrable (fun c => jetSq m (fun x => χ (x - (c + p))) F) (volume.restrict (periodBox d L)) ∧
    ∫ c in periodBox d L, jetSq m (fun x => χ (x - (c + p))) F = (∫ v, χ v ^ 2) * boxEnergy m L F := by
  unfold jetSq boxEnergy
  have hterm : ∀ j : ℕ, ∀ α : Fin j → Fin d,
      ∫ c in periodBox d L, ∫ x, ((fun x => χ (x - (c + p))) x * partialDeriv α F x) ^ 2 =
      (∫ v, χ v ^ 2) * ∫ x in periodBox d L, (partialDeriv α F x) ^ 2 := by
    intro j α
    have hc : Continuous fun x => (partialDeriv α F x) ^ 2 := (sa12c_pd_cont hF α).pow 2
    have hper : ∀ (x : Euc d) (k : Fin d → ℤ), (partialDeriv α F (x + L • latticePt k)) ^ 2 =
        (partialDeriv α F x) ^ 2 := by
      intro x k; rw [sa12c_pd_periodic hFp α x k]
    have := sa12c_avg_shift hL hχ hc hper p
    simpa [mul_pow] using this
  have hI : ∀ j : ℕ, ∀ α : Fin j → Fin d,
      Integrable (fun c => ∫ x, ((fun x => χ (x - (c + p))) x * partialDeriv α F x) ^ 2)
        (volume.restrict (periodBox d L)) := by
    intro j α
    have := sa12c_inner_int (L := L) hχ ((sa12c_pd_cont hF α).pow 2) p
    simpa [mul_pow] using this
  refine ⟨integrable_finset_sum _ fun j hj => (integrable_finset_sum _ fun α _ => hI j α).const_mul _, ?_⟩
  rw [integral_finset_sum _ fun j hj => (integrable_finset_sum _ fun α _ => hI j α).const_mul _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_const_mul, integral_finset_sum _ fun α _ => hI j α]
  simp_rw [hterm j]
  simp only [Finset.mul_sum]
  ring

theorem sa12c_avg_dissip {L : ℝ} (hL : 0 < L) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) (m : ℕ)
    {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) (p : Euc d) :
    Integrable (fun c => dissipSq m (fun x => χ (x - (c + p))) F) (volume.restrict (periodBox d L)) ∧
    ∫ c in periodBox d L, dissipSq m (fun x => χ (x - (c + p))) F = (∫ v, χ v ^ 2) * boxDissip m L F := by
  unfold dissipSq boxDissip
  have hterm : ∀ j : ℕ, ∀ (α : Fin j → Fin d) (i : Fin d),
      ∫ c in periodBox d L, ∫ x, ((fun x => χ (x - (c + p))) x *
        partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F x) ^ 2 =
      (∫ v, χ v ^ 2) * ∫ x in periodBox d L, (partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F x) ^ 2 := by
    intro j α i
    have hc : Continuous fun x => (partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F x) ^ 2 :=
      (sa12c_pd_cont hF _).pow 2
    have hper : ∀ (x : Euc d) (k : Fin d → ℤ),
        (partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F (x + L • latticePt k)) ^ 2 =
        (partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F x) ^ 2 := by
      intro x k; rw [sa12c_pd_periodic hFp _ x k]
    have := sa12c_avg_shift hL hχ hc hper p
    simpa [mul_pow] using this
  have hI : ∀ j : ℕ, ∀ (α : Fin j → Fin d) (i : Fin d),
      Integrable (fun c => ∫ x, ((fun x => χ (x - (c + p))) x *
        partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F x) ^ 2) (volume.restrict (periodBox d L)) := by
    intro j α i
    have := sa12c_inner_int (L := L) hχ ((sa12c_pd_cont hF (Fin.snoc α i : Fin (j + 1) → Fin d)).pow 2) p
    simpa [mul_pow] using this
  have hI2 : ∀ j : ℕ, ∀ α : Fin j → Fin d,
      Integrable (fun c => ∑ i : Fin d, ∫ x, ((fun x => χ (x - (c + p))) x *
        partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F x) ^ 2) (volume.restrict (periodBox d L)) :=
    fun j α => integrable_finset_sum _ fun i _ => hI j α i
  refine ⟨integrable_finset_sum _ fun j hj => (integrable_finset_sum _ fun α _ => hI2 j α).const_mul _, ?_⟩
  rw [integral_finset_sum _ fun j hj => (integrable_finset_sum _ fun α _ => hI2 j α).const_mul _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_const_mul, integral_finset_sum _ fun α _ => hI2 j α]
  have hterm2 : ∀ (α : Fin j → Fin d),
      (∫ c in periodBox d L, ∑ i : Fin d, ∫ x,
        ((fun x => χ (x - (c + p))) x * partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F x) ^ 2) =
      (∫ v, χ v ^ 2) * ∑ i : Fin d, ∫ x in periodBox d L,
        (partialDeriv (Fin.snoc α i : Fin (j + 1) → Fin d) F x) ^ 2 := by
    intro α
    rw [integral_finset_sum _ fun i _ => hI j α i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hterm j α i
  simp_rw [hterm2]
  simp only [Finset.mul_sum]
  ring

theorem sa12c_two_ab {u v : Euc d → ℝ} (hu : Integrable (fun x => u x ^ 2) volume)
    (hv : Integrable (fun x => v x ^ 2) volume) (huv : Integrable (fun x => u x * v x) volume) :
    -(2 * ∫ x, u x * v x) ≤ (∫ x, u x ^ 2) + ∫ x, v x ^ 2 := by
  have h0 : 0 ≤ ∫ x, (u x + v x) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (u x + v x) ^ 2 = ∫ x, ((u x ^ 2 + 2 * (u x * v x)) + v x ^ 2) := by
    congr 1; funext x; ring
  rw [e] at h0
  have hinter : (∫ x, u x ^ 2 + 2 * (u x * v x)) =
      (∫ x, u x ^ 2) + 2 * (∫ x, u x * v x) := by
    simpa only [Pi.add_apply, integral_const_mul] using (integral_add hu (huv.const_mul 2))
  have hsum : (∫ x, (u x ^ 2 + 2 * (u x * v x)) + v x ^ 2) =
      (∫ x, u x ^ 2) + 2 * (∫ x, u x * v x) + (∫ x, v x ^ 2) := by
    calc
      _ = (∫ x, u x ^ 2 + 2 * (u x * v x)) + (∫ x, v x ^ 2) := by
        simpa only [Pi.add_apply] using (integral_add (hu.add (huv.const_mul 2)) hv)
      _ = _ := by rw [hinter]
  rw [hsum] at h0
  linarith

/-- Young splitting of a jet pairing: `-2⟨F,S⟩_w ≤ jetSq(w;F) + jetSq(w;S)`. -/
theorem sa12c_jetPair_neg_le {m : ℕ} {w F S : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hF : ContDiff ℝ ∞ F) (hS : ContDiff ℝ m S) :
    -(2 * jetPair m w F S) ≤ jetSq m w F + jetSq m w S := by
  have hterm : ∀ j ∈ Finset.range (m + 1), ∀ idx : Fin j → Fin d,
      -(2 * ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx S x)) ≤
        (∫ x, (w x * partialDeriv idx F x) ^ 2) + ∫ x, (w x * partialDeriv idx S x) ^ 2 := by
    intro j hj idx
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hpF : Continuous (partialDeriv idx F) := sa12c_pd_cont hF idx
    have hpS : Continuous (partialDeriv idx S) :=
      (sa12x2_pd_cd (k := 0) (by simpa using hS.of_le (by exact_mod_cast hjm)) idx).continuous
    have hu : Continuous fun x => w x * partialDeriv idx F x := hw.mul hpF
    have hv : Continuous fun x => w x * partialDeriv idx S x := hw.mul hpS
    have hucs : HasCompactSupport fun x => w x * partialDeriv idx F x := hwc.mul_right
    have hvcs : HasCompactSupport fun x => w x * partialDeriv idx S x := hwc.mul_right
    have e : ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx S x) =
        ∫ x, (w x * partialDeriv idx F x) * (w x * partialDeriv idx S x) := by
      congr 1; funext x; ring
    rw [e]
    have hucompact : HasCompactSupport (fun x => (w x * partialDeriv idx F x) ^ 2) := by
      have heq : (fun x => (w x * partialDeriv idx F x) ^ 2) =
          (fun x => w x * partialDeriv idx F x) * (fun x => w x * partialDeriv idx F x) := by
        funext x; simp only [Pi.mul_apply, pow_two]
      rw [heq]
      exact hucs.mul_right
    have hvcompact : HasCompactSupport (fun x => (w x * partialDeriv idx S x) ^ 2) := by
      have heq : (fun x => (w x * partialDeriv idx S x) ^ 2) =
          (fun x => w x * partialDeriv idx S x) * (fun x => w x * partialDeriv idx S x) := by
        funext x; simp only [Pi.mul_apply, pow_two]
      rw [heq]
      exact hvcs.mul_right
    exact sa12c_two_ab ((hu.pow 2).integrable_of_hasCompactSupport hucompact)
      ((hv.pow 2).integrable_of_hasCompactSupport hvcompact)
      ((hu.mul hv).integrable_of_hasCompactSupport (hucs.mul_right (f' := fun x => w x * partialDeriv idx S x)))
  unfold jetPair jetSq
  calc -(2 * ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
        ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx S x))
      = ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          (-(2 * ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx S x))) := by
        rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]; ring
    _ ≤ ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
          ((∫ x, (w x * partialDeriv idx F x) ^ 2) + ∫ x, (w x * partialDeriv idx S x) ^ 2) := by
        refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun idx _ => hterm j hj idx) (Nat.cast_nonneg _)
    _ = _ := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← mul_add, ← Finset.sum_add_distrib]

end HRS.MH.AdjointRd.Phase2SA12C
