import HRS.MS.SA16SEn8

/-!
# S.A.16 (SA16S) En9: the transport term of the energy (packet P7, step 10)

`sa16sz_transport`: for `φ ∈ C_c^∞` and smooth `b` with `‖D^i b_l‖ ≤ B` for `i ≤ m+1`,
`∫ sa16sz_dens m p φ (b·∇φ) ≤ cTr · ∑_j ∫ |D^jφ|^p`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section En9
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the constant of the transport estimate of the energy -/
def sa16sz_cTr (d m : ℕ) (p B : ℝ) : ℝ :=
  (d : ℝ) * B / p + (∑ j : Fin (m + 1), (Fintype.card (Fin (j : ℕ) → Fin d) : ℝ)) *
    ((d : ℝ) * (2 ^ m * (B * ((d : ℝ) + 1) ^ m)))

theorem sa16sz_transport (m : ℕ) {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef (m + 1) B bc)
    (φ : ccSub d) :
    ∫ x, sa16sz_dens m p φ.1 (sa16so_transportFun bc φ.1) x ≤
      sa16sz_cTr d m p B * ∑ j : Fin (m + 1), ∫ x, sa16sz_vn φ.1 j x ^ p := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp0 : 0 < p := by linarith
  have hB0 := hb.nonneg
  set cR : ℝ := (d : ℝ) * (2 ^ m * (B * ((d : ℝ) + 1) ^ m)) with hcR
  have hcR0 : 0 ≤ cR := by rw [hcR]; positivity
  have hW : ∀ (j : ℕ) (idx : Fin j → Fin d), IsCcInfty (partialDeriv idx φ.1) :=
    fun j idx => sa16s_cc_partialDeriv φ.2 idx
  have hTs : ContDiff ℝ ∞ (sa16so_transportFun bc φ.1) := sa16so_transportFun_smooth hb φ.2.1
  -- the remainder
  set R : (j : ℕ) → (Fin j → Fin d) → Euc d → ℝ := fun j idx x =>
    partialDeriv idx (sa16so_transportFun bc φ.1) x -
      ∑ l, bc l x * fderiv ℝ (partialDeriv idx φ.1) x (EuclideanSpace.single l 1) with hR
  have hRc : ∀ j idx, Continuous (R j idx) := by
    intro j idx
    have h1 := (sa16j_pd_smooth hTs idx).continuous
    have h2 : Continuous (fun x => ∑ l, bc l x * fderiv ℝ (partialDeriv idx φ.1) x (EuclideanSpace.single l 1)) :=
      continuous_finsetSum _ fun l _ => (hb.smooth l).continuous.mul
        (((sa16j_pd_smooth φ.2.1 idx).continuous_fderiv (by simp)).clm_apply continuous_const)
    exact h1.sub h2
  have hRle : ∀ (j : Fin (m + 1)) idx x, |R j idx x| ≤ cR * ‖wJet j φ.1 x‖ := by
    intro j idx x
    have hj : (j : ℕ) ≤ m + 1 := by omega
    have h := sa16sy_transport_split hb φ.2.1 (j := j) hj idx x
    refine h.trans ?_
    have hj2 : (j : ℕ) ≤ m := by have := j.2; omega
    have h1 : (2 : ℝ) ^ (j : ℕ) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hj2
    have h2 : ((d : ℝ) + 1) ^ (j : ℕ) ≤ ((d : ℝ) + 1) ^ m :=
      pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) hj2
    have hJ := norm_nonneg (wJet (j : ℕ) φ.1 x)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    rw [hcR]
    calc (d : ℝ) * (2 ^ (j : ℕ) * (B * ((d : ℝ) + 1) ^ (j : ℕ)) * ‖wJet (j : ℕ) φ.1 x‖)
        ≤ (d : ℝ) * (2 ^ m * (B * ((d : ℝ) + 1) ^ m) * ‖wJet (j : ℕ) φ.1 x‖) := by
          gcongr
      _ = _ := by ring
  -- pointwise decomposition of the `j`-th term
  set e : Fin d → Euc d := fun l => EuclideanSpace.single l 1 with he
  set term : Fin (m + 1) → Euc d → ℝ := fun j x =>
    sa16sz_vn φ.1 j x ^ (p - 2) * ∑ idx : Fin (j : ℕ) → Fin d,
      partialDeriv idx φ.1 x * partialDeriv idx (sa16so_transportFun bc φ.1) x with hterm
  have hdens : ∀ x, sa16sz_dens m p φ.1 (sa16so_transportFun bc φ.1) x = ∑ j : Fin (m + 1), term j x := fun x => rfl
  have hdec : ∀ (j : Fin (m + 1)) x, term j x = ∑ l : Fin d, ∑ idx : Fin (j : ℕ) → Fin d,
      sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l)) +
      ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * R j idx x := by
    intro j x
    have h1 : ∀ idx : Fin (j : ℕ) → Fin d, partialDeriv idx (sa16so_transportFun bc φ.1) x =
        ∑ l, bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l) + R j idx x := fun idx => by
      simp only [hR, he]; ring
    have e1 : ∑ l : Fin d, ∑ idx : Fin (j : ℕ) → Fin d,
        sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l)) =
        ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
          ∑ l, bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun idx _ => by rw [Finset.mul_sum]
    rw [e1, ← Finset.sum_add_distrib]
    simp only [hterm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun idx _ => ?_
    rw [h1 idx]; ring
  -- integrability
  have hcont_j : ∀ j : Fin (m + 1), Continuous (fun x => sa16sz_vn φ.1 j x ^ (p - 2)) :=
    fun j => sa16sz_vn_pow_cont φ.1 φ.2.1 j (by linarith)
  have hintf : ∀ (j : Fin (m + 1)) (l : Fin d), Integrable (fun x => ∑ idx : Fin (j : ℕ) → Fin d,
      sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
        (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l))) := by
    intro j l
    refine integrable_finsetSum _ fun idx _ => ?_
    have hc : Continuous (fun x => sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
        (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l))) :=
      ((hcont_j j).mul (hW j idx).1.continuous).mul ((hb.smooth l).continuous.mul
        ((sa16s_cc_fderiv (hW j idx) (e l)).1.continuous))
    exact hc.integrable_of_hasCompactSupport (((hW j idx).2.mul_left).mul_right)
  have hintg : ∀ j : Fin (m + 1), Integrable (fun x => ∑ idx : Fin (j : ℕ) → Fin d,
      sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * R j idx x) := by
    intro j
    refine integrable_finsetSum _ fun idx _ => ?_
    have hc : Continuous (fun x => sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * R j idx x) :=
      ((hcont_j j).mul (hW j idx).1.continuous).mul (hRc j idx)
    exact hc.integrable_of_hasCompactSupport (((hW j idx).2.mul_left).mul_right)
  have hintvn : ∀ j : Fin (m + 1), Integrable (fun x => sa16sz_vn φ.1 j x ^ p) := fun j =>
    (sa16sz_vn_pow_cont φ.1 φ.2.1 j hp0.le).integrable_of_hasCompactSupport (sa16sz_vn_pow_cs φ.2 j hp0)
  have hintE : Integrable (sa16sz_E m p φ.1) :=
    integrable_finsetSum _ fun j _ => hintvn j
  have hintE' : ∫ x, sa16sz_E m p φ.1 x = ∑ j : Fin (m + 1), ∫ x, sa16sz_vn φ.1 j x ^ p := by
    unfold sa16sz_E; exact integral_finsetSum _ fun j _ => hintvn j
  -- the bound for each `j`
  have hj : ∀ j : Fin (m + 1), ∫ x, term j x ≤ (d : ℝ) * B / p * (∫ x, sa16sz_vn φ.1 j x ^ p) +
      (Fintype.card (Fin (j : ℕ) → Fin d) : ℝ) * cR * (∫ x, sa16sz_E m p φ.1 x) := by
    intro j
    have hj2 : (j : ℕ) ≤ m := by have := j.2; omega
    have hrw : ∫ x, term j x = ∑ l : Fin d, (∫ x, ∑ idx : Fin (j : ℕ) → Fin d,
        sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
          (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l))) +
        ∫ x, ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * R j idx x := by
      have h1 : (fun x => term j x) = fun x => (∑ l : Fin d, ∑ idx : Fin (j : ℕ) → Fin d,
          sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
            (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l))) +
          ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * R j idx x :=
        funext (hdec j)
      rw [h1, integral_add (integrable_finsetSum _ fun l _ => hintf j l) (hintg j),
        integral_finsetSum _ fun l _ => hintf j l]
    -- the transport part
    have hl : ∀ l : Fin d, (∫ x, ∑ idx : Fin (j : ℕ) → Fin d,
        sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
          (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l))) ≤ B / p * ∫ x, sa16sz_vn φ.1 j x ^ p := by
      intro l
      have h := sa16sy_transport (W := fun idx : Fin (j : ℕ) → Fin d => partialDeriv idx φ.1) (hW j)
        hp2 (hb.smooth l) (e l)
      have h' : (∫ x, ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
          (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l))) =
          -(1 / p) * ∫ x, fderiv ℝ (bc l) x (e l) * sa16sz_vn φ.1 j x ^ p := h
      rw [h']
      have hbl : ∀ x, |fderiv ℝ (bc l) x (e l)| ≤ B := by
        intro x
        have h1 := hb.bound l 1 (by omega) x
        rw [norm_iteratedFDeriv_one] at h1
        have h2 := (fderiv ℝ (bc l) x).le_opNorm (e l)
        rw [he, PiLp.norm_single, norm_one, mul_one] at h2
        rw [← Real.norm_eq_abs]
        exact h2.trans h1
      have hint1 : Integrable (fun x => fderiv ℝ (bc l) x (e l) * sa16sz_vn φ.1 j x ^ p) :=
        (((hb.smooth l).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul
          (sa16sz_vn_pow_cont φ.1 φ.2.1 j hp0.le)).integrable_of_hasCompactSupport
          (sa16sz_vn_pow_cs φ.2 j hp0).mul_left
      have hle : -∫ x, fderiv ℝ (bc l) x (e l) * sa16sz_vn φ.1 j x ^ p ≤ B * ∫ x, sa16sz_vn φ.1 j x ^ p := by
        rw [← integral_neg, ← integral_const_mul]
        refine integral_mono hint1.neg ((hintvn j).const_mul B) fun x => ?_
        have hv : 0 ≤ sa16sz_vn φ.1 j x ^ p := Real.rpow_nonneg (sa16sz_vn_nonneg φ.1 j x) _
        have := hbl x
        have h3 := neg_abs_le (fderiv ℝ (bc l) x (e l))
        nlinarith [mul_nonneg (sub_nonneg.2 this) hv, mul_nonneg (sub_nonneg.2 (neg_le_of_abs_le this)) hv]
      calc -(1 / p) * ∫ x, fderiv ℝ (bc l) x (e l) * sa16sz_vn φ.1 j x ^ p
          = (1 / p) * (-∫ x, fderiv ℝ (bc l) x (e l) * sa16sz_vn φ.1 j x ^ p) := by ring
        _ ≤ (1 / p) * (B * ∫ x, sa16sz_vn φ.1 j x ^ p) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = B / p * (∫ x, sa16sz_vn φ.1 j x ^ p) := by ring
    -- the remainder part
    have hg : (∫ x, ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
        R j idx x) ≤ (Fintype.card (Fin (j : ℕ) → Fin d) : ℝ) * cR * ∫ x, sa16sz_E m p φ.1 x := by
      rw [← integral_const_mul]
      refine integral_mono (hintg j) (hintE.const_mul _) fun x => ?_
      refine (le_abs_self _).trans ?_
      exact sa16sz_remainder_le (p := p) m φ.1 x hj2 (fun idx => R j idx x) (fun idx => hRle j idx x) hcR0
    rw [hrw]
    calc ∑ l : Fin d, (∫ x, ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
          (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l))) + _
        ≤ ∑ l : Fin d, (B / p * ∫ x, sa16sz_vn φ.1 j x ^ p) + _ :=
          add_le_add (Finset.sum_le_sum fun l _ => hl l) hg
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- sum over `j`
  have hsum : ∫ x, sa16sz_dens m p φ.1 (sa16so_transportFun bc φ.1) x = ∑ j : Fin (m + 1), ∫ x, term j x := by
    have h1 : (fun x => sa16sz_dens m p φ.1 (sa16so_transportFun bc φ.1) x) = fun x => ∑ j : Fin (m + 1), term j x :=
      funext hdens
    rw [h1]
    refine integral_finsetSum _ fun j _ => ?_
    rw [show term j = fun x => (∑ l : Fin d, ∑ idx : Fin (j : ℕ) → Fin d,
          sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x *
            (bc l x * fderiv ℝ (partialDeriv idx φ.1) x (e l))) +
          ∑ idx : Fin (j : ℕ) → Fin d, sa16sz_vn φ.1 j x ^ (p - 2) * partialDeriv idx φ.1 x * R j idx x
        from funext (hdec j)]
    exact (integrable_finsetSum _ fun l _ => hintf j l).add (hintg j)
  rw [hsum]
  refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h2 : ∑ j : Fin (m + 1), (Fintype.card (Fin (j : ℕ) → Fin d) : ℝ) * cR * (∫ x, sa16sz_E m p φ.1 x) =
      (∑ j : Fin (m + 1), (Fintype.card (Fin (j : ℕ) → Fin d) : ℝ)) * cR * (∫ x, sa16sz_E m p φ.1 x) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  rw [h2, hintE']
  unfold sa16sz_cTr
  rw [hcR]
  ring_nf
  exact le_refl _

end En9

end HRS.Whole.AppendixA.Phase2SA16R
