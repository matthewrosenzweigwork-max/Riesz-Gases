import HRS.MS.SA12Z3NearN4

/-!
# S.A.12 N4 (SA12Z3): `odd_gradient_finite`
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12z3_fr_cont {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) : Continuous (firstRiesz d s i v) := by
  have hK : firstRiesz d s i v = HRS.Whole.convFun (rieszKernel d s) (D1 i v) :=
    funext fun x => sa12z3_firstRiesz_eq' hs0 hsd i hv hvc x
  rw [hK]
  exact K_cont hs0 hsd ((hv.continuous_fderiv one_ne_zero).clm_apply continuous_const) (D1_supp hvc i)

theorem sa12z3_cb_mono {a : Euc d → ℝ} (ha : MemCb 2 a) : cbNorm 1 a ≤ cbNorm 2 a := by
  unfold cbNorm
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by norm_num))
    (fun _ _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

/-- **N4.** The `β = 1` gradient exchange at positive odd order. -/
theorem odd_gradient_finite (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hs1 : (d : ℝ)-1<s) (hsd : s<d) :
    ∃ C : ℝ, 0 < C ∧ ∀ i j l : Fin d,
      ∀ a : Euc d → ℝ, MemCb 2 a →
      ∀ Z : Euc d → ℝ, MemCb 2 Z → HasCompactSupport Z →
      Integrable (fun x => partialDeriv (fun _ : Fin 1 => l) Z x*a x*
        firstRiesz d s i (partialDeriv (fun _ : Fin 1 => j) Z) x) volume ∧
      |∫ x, partialDeriv (fun _ : Fin 1 => l) Z x*a x*
        firstRiesz d s i (partialDeriv (fun _ : Fin 1 => j) Z) x| ≤
        C*cbNorm 2 a*((∫ x, Z x^2)+(∫ x, ‖fderiv ℝ Z x‖^2)) := by
  obtain ⟨CT, hCT0, hCT⟩ := sa12z3_T_pair hd hs0 hsd hs1
  have hK0 : 0 ≤ ∫ z, sa12z3_kap d s z := integral_nonneg fun z => sa12z3_kap_nonneg s z
  have hσ : 0 ≤ movtr_sigma s := by unfold movtr_sigma; split_ifs <;> linarith
  refine ⟨1 + movtr_sigma s * (∫ z, sa12z3_kap d s z) + 3 * CT, by positivity, ?_⟩
  intro i j l a ha Z hZ hZc
  have hZ2 : ContDiff ℝ 2 Z := by simpa using hZ.1
  have hZ1 : ContDiff ℝ 1 Z := hZ2.of_le (by norm_num)
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have ha1' : MemCb 1 a := ⟨by simpa using ha2.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2),
    fun k hk => ha.2 k (by omega)⟩
  have ha1 : ContDiff ℝ 1 a := ha2.of_le (by norm_num)
  rw [sa12z3_pd_one hZ1 l, sa12z3_pd_one hZ1 j]
  have hf : ∀ k, ContDiff ℝ 1 (D1 k Z) := fun k => D1_contDiff hZ2 k
  have hfc : ∀ k, HasCompactSupport (D1 k Z) := fun k => D1_supp hZc k
  have hTc : ∀ k, Continuous (firstRiesz d s i (D1 k Z)) := fun k =>
    sa12z3_fr_cont hs0 hsd i (hf k) (hfc k)
  refine ⟨?_, ?_⟩
  · exact Continuous.integrable_of_hasCompactSupport (f := fun x => D1 l Z x * a x *
      firstRiesz d s i (D1 j Z) x) (((hf l).continuous.mul ha1.continuous).mul (hTc j))
      ((hfc l).mul_right.mul_right)
  set cb : ℝ := cbNorm 2 a with hcb
  have hcb0 : 0 ≤ cb := sa12z3_cb_nonneg ha
  set E : ℝ := (∫ x, Z x ^ 2) + ∫ x, ‖fderiv ℝ Z x‖ ^ 2 with hE
  have hIG := sa12z3_gradsq_integrable hZ1 hZc
  have hZ0 : 0 ≤ ∫ x, Z x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hG0 : 0 ≤ ∫ x, ‖fderiv ℝ Z x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hE0 : 0 ≤ E := add_nonneg hZ0 hG0
  have hfsq : ∀ k, ∫ x, D1 k Z x ^ 2 ≤ E := fun k => by
    have : ∫ x, D1 k Z x ^ 2 ≤ ∫ x, ‖fderiv ℝ Z x‖ ^ 2 :=
      integral_mono (sa12z3_sq_integrable (hf k).continuous (hfc k)) hIG fun x => by
        have := sa12z3_D1_le k Z x
        rw [← sq_abs (D1 k Z x)]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
    linarith
  -- the symmetric part
  have hsum := sa12z3_comm_bound hd hs0 hsd hs1 i (hf l) (hfc l) (hf j) (hfc j) ha1'
  have hsum' : |(∫ x, D1 l Z x * a x * firstRiesz d s i (D1 j Z) x) +
      ∫ x, D1 j Z x * a x * firstRiesz d s i (D1 l Z) x| ≤
      movtr_sigma s * (∫ z, sa12z3_kap d s z) * (cb * E) := by
    refine hsum.trans ?_
    have h1 : cbNorm 1 a ≤ cb := sa12z3_cb_mono ha
    have h2 : ((∫ x, D1 l Z x ^ 2) + ∫ x, D1 j Z x ^ 2) / 2 ≤ E := by linarith [hfsq l, hfsq j]
    calc movtr_sigma s * cbNorm 1 a * ((∫ z, sa12z3_kap d s z) *
          ((∫ x, D1 l Z x ^ 2) + ∫ x, D1 j Z x ^ 2) / 2)
        = movtr_sigma s * cbNorm 1 a * ((∫ z, sa12z3_kap d s z) *
          (((∫ x, D1 l Z x ^ 2) + ∫ x, D1 j Z x ^ 2) / 2)) := by ring
      _ ≤ movtr_sigma s * cb * ((∫ z, sa12z3_kap d s z) * E) := by
          have hc1 : 0 ≤ cbNorm 1 a := sa12z3_cb_nonneg ha1'
          gcongr
      _ = _ := by ring
  -- the antisymmetric part
  have hdiff := sa12z3_diff hd hs0 hsd i hZ2 hZc ha1 l j
  have hd1 := sa12z3_delta_term hd hs0 hsd hCT0 hCT i j l hZ2 hZc ha
  have hd2 := sa12z3_delta_term hd hs0 hsd hCT0 hCT i l j hZ2 hZc ha
  have hdiff' : |(∫ x, D1 l Z x * a x * firstRiesz d s i (D1 j Z) x) -
      ∫ x, D1 j Z x * a x * firstRiesz d s i (D1 l Z) x| ≤ 6 * CT * cb * E := by
    have e : (∫ x, D1 l Z x * a x * firstRiesz d s i (D1 j Z) x) -
        ∫ x, D1 j Z x * a x * firstRiesz d s i (D1 l Z) x =
        (∫ x, (Z x * D1 j a x) * firstRiesz d s i (D1 l Z) x) -
        ∫ x, (Z x * D1 l a x) * firstRiesz d s i (D1 j Z) x := hdiff
    rw [e]
    refine (abs_sub _ _).trans ?_
    linarith
  -- combine
  set A : ℝ := ∫ x, D1 l Z x * a x * firstRiesz d s i (D1 j Z) x with hA
  set B : ℝ := ∫ x, D1 j Z x * a x * firstRiesz d s i (D1 l Z) x with hB
  have hAeq : A = ((A + B) + (A - B)) / 2 := by ring
  have h1 := abs_le.1 hsum'
  have h2 := abs_le.1 hdiff'
  have hcE : 0 ≤ cb * E := mul_nonneg hcb0 hE0
  have hK : 0 ≤ movtr_sigma s * (∫ z, sa12z3_kap d s z) := mul_nonneg hσ hK0
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hK hcE, mul_nonneg hCT0 hcE]

end HRS.MH.AdjointRd.Phase2SA12Near
