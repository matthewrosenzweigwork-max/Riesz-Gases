import HRS.MS.SA12X3C7C4

/-!
# S.A.12 C7 (SA12X3), part C5 (7C): pairing bound for the far box term
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- The combination of the derivatives of the smooth representatives. -/
def sa12x3_Pc (M : Matrix (Fin d) (Fin d) ℝ) (Sh : Fin d → Fin d → Euc d → ℝ) {n : ℕ} (idx : Fin n → Fin d)
    (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, M j i * partialDeriv idx (Sh i j) x

theorem sa12x3_far_pairing {s L : ℝ} {γ : Euc d → ℝ}
    (hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ) {h R' R'' : ℝ} (hh : 0 < h) (hR : 0 < R'')
    (hR'' : R' + h / 2 ≤ R'') (hRL : R'' < L / 2) {c : Euc d} (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ)
    (hM : ∀ i j, |M i j| ≤ MB) {w η μ F : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hη : Continuous η) (hμ : Continuous μ) (hF : ContDiff ℝ ∞ F)
    (hwN : ∀ x, w x ≠ 0 → x ∈ ball c R' ∧ ∀ y ∈ ball x h, η y = 1) (m : ℕ) {En Mass : ℝ}
    (hwp : ∀ n ≤ m, ∀ idx : Fin n → Fin d, ∫ x, (w x * partialDeriv idx F x) ^ 2 ≤ En)
    (hT : ∀ n ≤ m, ∀ (idx : Fin n → Fin d) (i j : Fin d),
      ∫ x, (w x * sa12x3_Tfar L γ c η μ F idx i j x) ^ 2 ≤ Mass) :
    -(2 * jetPair m w F (sa12x3_Far L γ c M η μ F)) ≤
      (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j) *
        (En + (d : ℝ) ^ 4 * (max MB 0) ^ 2 * Mass) := by
  obtain ⟨Sh, hSs, hFar, hpd⟩ := sa12x3_far_pd hγ hh hR hR'' hRL M hw hη hμ hF hwN
  have hMB0 : ∀ i j, |M i j| ≤ max MB 0 := fun i j => (hM i j).trans (le_max_left _ _)
  set MB' : ℝ := max MB 0 with hMB'
  have hMB'0 : 0 ≤ MB' := le_max_right _ _
  have hPc : ∀ {n : ℕ} (idx : Fin n → Fin d), Continuous (sa12x3_Pc M Sh idx) := by
    intro n idx
    unfold sa12x3_Pc
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => continuous_const.mul ?_
    exact (sa12z3_pd_contDiff_inf (hSs i j) idx).continuous
  have hPfar : ∀ {n : ℕ} (idx : Fin n → Fin d) (x : Euc d), w x ≠ 0 →
      partialDeriv idx (sa12x3_Far L γ c M η μ F) x = sa12x3_Pc M Sh idx x := by
    intro n idx x hx
    unfold sa12x3_Pc
    have hopen : IsOpen {x : Euc d | w x ≠ 0} := isOpen_ne_fun hw continuous_const
    have hEq : EqOn (sa12x3_Far L γ c M η μ F) (fun y => ∑ i : Fin d, ∑ j : Fin d, M j i * Sh i j y)
        {x : Euc d | w x ≠ 0} := fun y hy => hFar y hy
    rw [sa12x3_pd_congr_open hopen hEq idx hx]
    have hcd : ∀ i j, ContDiff ℝ n (Sh i j) := fun i j => (hSs i j).of_le (sa12x2_le_top n)
    have hSeq : (fun y => ∑ i : Fin d, ∑ j : Fin d, M j i * Sh i j y) = fun y => ∑ i ∈ (Finset.univ : Finset (Fin d)),
        (fun _ => (1 : ℝ)) i * (fun i y => ∑ j : Fin d, M j i * Sh i j y) i y := by
      funext y
      exact Finset.sum_congr rfl fun i _ => by simp only [one_mul]
    rw [hSeq, sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun i y => ∑ j : Fin d, M j i * Sh i j y)
      (fun _ => 1) (n := n) (fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (hcd i j)) idx x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [one_mul, sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun j y => Sh i j y) (fun j => M j i)
      (n := n) (fun j _ => hcd i j) idx x]
  -- w * pd (Sh) = w * Tfar
  have hwT : ∀ {n : ℕ} (idx : Fin n → Fin d) (i j : Fin d) (x : Euc d),
      w x * partialDeriv idx (Sh i j) x = w x * sa12x3_Tfar L γ c η μ F idx i j x := by
    intro n idx i j x
    by_cases hx : w x = 0
    · simp [hx]
    · rw [hpd n idx i j x hx]
  -- the `L²` bound of `w P`
  have hwP : ∀ n ≤ m, ∀ idx : Fin n → Fin d,
      ∫ x, (w x * sa12x3_Pc M Sh idx x) ^ 2 ≤ (d : ℝ) ^ 4 * MB' ^ 2 * Mass := by
    intro n hn idx
    have hint : ∀ i j : Fin d, Integrable (fun x => (w x * partialDeriv idx (Sh i j) x) ^ 2) := by
      intro i j
      have hc : Continuous (fun x => w x * partialDeriv idx (Sh i j) x) :=
        hw.mul (sa12z3_pd_contDiff_inf (hSs i j) idx).continuous
      exact Continuous.integrable_of_hasCompactSupport (f := fun x => (w x * partialDeriv idx (Sh i j) x) ^ 2)
        (hc.pow 2) ((hwc.mul_right (f' := partialDeriv idx (Sh i j))).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    have hI : ∀ i j : Fin d, ∫ x, (w x * partialDeriv idx (Sh i j) x) ^ 2 ≤ Mass := by
      intro i j
      have : (fun x => (w x * partialDeriv idx (Sh i j) x) ^ 2) =
          fun x => (w x * sa12x3_Tfar L γ c η μ F idx i j x) ^ 2 := by
        funext x; rw [hwT idx i j x]
      rw [this]
      exact hT n hn idx i j
    have hpt : ∀ x, (w x * sa12x3_Pc M Sh idx x) ^ 2 ≤ (d : ℝ) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
        MB' ^ 2 * (w x * partialDeriv idx (Sh i j) x) ^ 2 := by
      intro x
      have e1 : w x * sa12x3_Pc M Sh idx x = ∑ i : Fin d, ∑ j : Fin d, M j i * (w x * partialDeriv idx (Sh i j) x) := by
        simp only [sa12x3_Pc, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [e1]
      have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => ∑ j : Fin d, M j i * (w x * partialDeriv idx (Sh i j) x))
      have h2 : ∀ i : Fin d, (∑ j : Fin d, M j i * (w x * partialDeriv idx (Sh i j) x)) ^ 2 ≤
          (d : ℝ) * ∑ j : Fin d, (M j i * (w x * partialDeriv idx (Sh i j) x)) ^ 2 := fun i => by
        have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
          (f := fun j => M j i * (w x * partialDeriv idx (Sh i j) x))
        simpa using this
      have h3 : ∀ i j : Fin d, (M j i * (w x * partialDeriv idx (Sh i j) x)) ^ 2 ≤
          MB' ^ 2 * (w x * partialDeriv idx (Sh i j) x) ^ 2 := fun i j => by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (by
          have := hMB0 j i
          nlinarith [abs_nonneg (M j i), sq_abs (M j i)]) (sq_nonneg _)
      calc (∑ i : Fin d, ∑ j : Fin d, M j i * (w x * partialDeriv idx (Sh i j) x)) ^ 2
          ≤ (Finset.univ : Finset (Fin d)).card * ∑ i : Fin d, (∑ j : Fin d, M j i *
              (w x * partialDeriv idx (Sh i j) x)) ^ 2 := h1
        _ ≤ (d : ℝ) * ∑ i : Fin d, (d : ℝ) * ∑ j : Fin d, (M j i * (w x * partialDeriv idx (Sh i j) x)) ^ 2 := by
            simp only [Finset.card_univ, Fintype.card_fin]
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => h2 i) (Nat.cast_nonneg _)
        _ ≤ (d : ℝ) * ∑ i : Fin d, (d : ℝ) * ∑ j : Fin d, MB' ^ 2 * (w x * partialDeriv idx (Sh i j) x) ^ 2 := by
            refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _)
            exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => h3 i j) (Nat.cast_nonneg _)
        _ = (d : ℝ) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, MB' ^ 2 * (w x * partialDeriv idx (Sh i j) x) ^ 2 := by
            rw [← Finset.mul_sum]; ring
    have hPint : Integrable (fun x => (w x * sa12x3_Pc M Sh idx x) ^ 2) := by
      exact Continuous.integrable_of_hasCompactSupport (f := fun x => (w x * sa12x3_Pc M Sh idx x) ^ 2)
        ((hw.mul (hPc idx)).pow 2) ((hwc.mul_right (f' := sa12x3_Pc M Sh idx)).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    have hRint : Integrable (fun x => (d : ℝ) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
        MB' ^ 2 * (w x * partialDeriv idx (Sh i j) x) ^ 2) :=
      (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hint i j).const_mul _).const_mul _
    calc ∫ x, (w x * sa12x3_Pc M Sh idx x) ^ 2 ≤ ∫ x, (d : ℝ) ^ 2 * ∑ i : Fin d, ∑ j : Fin d,
          MB' ^ 2 * (w x * partialDeriv idx (Sh i j) x) ^ 2 := integral_mono hPint hRint hpt
      _ = (d : ℝ) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, MB' ^ 2 * ∫ x, (w x * partialDeriv idx (Sh i j) x) ^ 2 := by
          rw [integral_const_mul, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
            (hint i j).const_mul _]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finset_sum _ fun j _ => (hint i j).const_mul _]
          exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
      _ ≤ (d : ℝ) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, MB' ^ 2 * Mass := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_)
            (by positivity)
          exact mul_le_mul_of_nonneg_left (hI i j) (sq_nonneg _)
      _ = (d : ℝ) ^ 4 * MB' ^ 2 * Mass := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- the pairing of each jet
  have hpair : ∀ n ≤ m, ∀ idx : Fin n → Fin d,
      -(∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx (sa12x3_Far L γ c M η μ F) x)) ≤
        (En + (d : ℝ) ^ 4 * MB' ^ 2 * Mass) / 2 := by
    intro n hn idx
    have hpc : Continuous (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous
    have heq : ∀ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx (sa12x3_Far L γ c M η μ F) x) =
        (w x * partialDeriv idx F x) * (w x * sa12x3_Pc M Sh idx x) := by
      intro x
      by_cases hx : w x = 0
      · simp [hx]
      · rw [hPfar idx x hx]; ring
    simp_rw [heq]
    have hi1 : Integrable (fun x => (w x * partialDeriv idx F x) ^ 2) :=
      Continuous.integrable_of_hasCompactSupport (f := fun x => (w x * partialDeriv idx F x) ^ 2)
        ((hw.mul hpc).pow 2) ((hwc.mul_right (f' := partialDeriv idx F)).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    have hi2 : Integrable (fun x => (w x * sa12x3_Pc M Sh idx x) ^ 2) :=
      Continuous.integrable_of_hasCompactSupport (f := fun x => (w x * sa12x3_Pc M Sh idx x) ^ 2)
        ((hw.mul (hPc idx)).pow 2) ((hwc.mul_right (f' := sa12x3_Pc M Sh idx)).comp_left (g := fun t : ℝ => t ^ 2) (by simp))
    have hi3 : Integrable (fun x => (w x * partialDeriv idx F x) * (w x * sa12x3_Pc M Sh idx x)) :=
      Continuous.integrable_of_hasCompactSupport (f := fun x => (w x * partialDeriv idx F x) * (w x * sa12x3_Pc M Sh idx x))
        ((hw.mul hpc).mul (hw.mul (hPc idx))) (by
          refine HasCompactSupport.intro (K := tsupport w) hwc fun y hy => ?_
          have : w y = 0 := image_eq_zero_of_notMem_tsupport hy
          simp [this])
    have hamgm : ∫ x, -((w x * partialDeriv idx F x) * (w x * sa12x3_Pc M Sh idx x)) ≤
        ∫ x, ((w x * partialDeriv idx F x) ^ 2 / 2 + (w x * sa12x3_Pc M Sh idx x) ^ 2 / 2) := by
      refine integral_mono hi3.neg ((hi1.div_const 2).add (hi2.div_const 2)) fun x => ?_
      nlinarith [sq_nonneg (w x * partialDeriv idx F x + w x * sa12x3_Pc M Sh idx x)]
    rw [integral_neg] at hamgm
    rw [integral_add (hi1.div_const 2) (hi2.div_const 2), integral_div, integral_div] at hamgm
    have := hwp n hn idx
    have := hwP n hn idx
    linarith
  -- assemble
  unfold jetPair
  have hsum : ∀ j ∈ Finset.range (m + 1), -((Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx (sa12x3_Far L γ c M η μ F) x)) ≤
      (Nat.choose m j : ℝ) * ((d : ℝ) ^ j * ((En + (d : ℝ) ^ 4 * MB' ^ 2 * Mass) / 2)) := by
    intro j hj
    have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.1 hj)
    have h1 : -(∑ idx : Fin j → Fin d, ∫ x, w x ^ 2 * (partialDeriv idx F x *
        partialDeriv idx (sa12x3_Far L γ c M η μ F) x)) ≤
        (d : ℝ) ^ j * ((En + (d : ℝ) ^ 4 * MB' ^ 2 * Mass) / 2) := by
      calc -(∑ idx : Fin j → Fin d, ∫ x, w x ^ 2 * (partialDeriv idx F x *
            partialDeriv idx (sa12x3_Far L γ c M η μ F) x))
          = ∑ idx : Fin j → Fin d, -(∫ x, w x ^ 2 * (partialDeriv idx F x *
            partialDeriv idx (sa12x3_Far L γ c M η μ F) x)) := by rw [Finset.sum_neg_distrib]
        _ ≤ ∑ idx : Fin j → Fin d, (En + (d : ℝ) ^ 4 * MB' ^ 2 * Mass) / 2 :=
            Finset.sum_le_sum fun idx _ => hpair j hjm idx
        _ = (d : ℝ) ^ j * ((En + (d : ℝ) ^ 4 * MB' ^ 2 * Mass) / 2) := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    have hc : (0 : ℝ) ≤ Nat.choose m j := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left h1 hc
    linarith
  have hfin := Finset.sum_le_sum hsum
  rw [Finset.sum_neg_distrib] at hfin
  have hrhs : ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ((d : ℝ) ^ j *
      ((En + (d : ℝ) ^ 4 * MB' ^ 2 * Mass) / 2)) =
      (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j) *
        ((En + (d : ℝ) ^ 4 * MB' ^ 2 * Mass) / 2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hrhs] at hfin
  have : -(2 * ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx (sa12x3_Far L γ c M η μ F) x)) =
      2 * (-∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
      ∫ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx (sa12x3_Far L γ c M η μ F) x)) := by ring
  rw [this]
  nlinarith [hfin]

end HRS.MH.AdjointRd.Phase2SA12Near
