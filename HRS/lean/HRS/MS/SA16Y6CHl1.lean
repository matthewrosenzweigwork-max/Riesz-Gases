import HRS.MS.SA16Y6CEr1
import HRS.MS.SA16Y3Sk3
import HRS.MS.SA16Y3Op1
import HRS.MS.SA16Y3Hk4
import HRS.MS.SA16Y6C1
import HRS.MS.SA16Y5Hl1

/-! # SA16Y6 critical-case copy of SA16Y5Hl1 (s = d-1) -/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Hl1
variable {d : ℕ} {s : ℝ}
lemma sa16y6c_PA_deriv (hs0 : 0 ≤ s) (hsd : s < d) (A : Matrix (Fin d) (Fin d) ℝ) {a ψ : Euc d → ℝ}
    (ha : ContDiff ℝ ∞ a) (hψ : IsCcInfty ψ) (l : Fin d) (x : Euc d) :
    sa16z_dm (sa16y3_PA s A a ψ) l x =
      sa16y3_PA s A (sa16z_dm a l) ψ x + sa16y3_PA s A a (sa16z_dm ψ l) x := by
  have hQs : ∀ i j, ContDiff ℝ ∞ (sa16y3_Q s i (sa16z_src a ψ j)) := fun i j =>
    sa16y3_Q_smooth hs0 hsd (sa16z_src_cc ha hψ j) i
  have hPA : sa16y3_PA s A a ψ = fun y => ∑ i : Fin d, ∑ j : Fin d, A j i * sa16y3_Q s i (sa16z_src a ψ j) y := rfl
  have e1 : sa16z_dm (sa16y3_PA s A a ψ) l x = ∑ i : Fin d, ∑ j : Fin d,
      A j i * fderiv ℝ (sa16y3_Q s i (sa16z_src a ψ j)) x (sa16z_e l) := by
    show fderiv ℝ (sa16y3_PA s A a ψ) x (sa16z_e l) = _
    rw [← sa16y5_pd1, hPA, sa16sy_pd_sum _ (fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (hQs i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sa16sy_pd_sum _ (fun j _ => contDiff_const.mul (hQs i j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sa16sy_pd_cmul (hQs i j), sa16y5_pd1]
  rw [e1]
  simp only [sa16y3_PA, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sa16y5_Q_src_deriv hs0 hsd ha hψ i j l x]
  ring

theorem sa16y6c_PA_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hs1 : s = (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) (AB : ℝ) (hAB : 0 ≤ AB) :
    ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ {A : Matrix (Fin d) (Fin d) ℝ}, (∀ i j, |A i j| ≤ AB) → A.transpose = -A →
      ∀ {a φ : Euc d → ℝ}, ContDiff ℝ ∞ a → IsCcInfty φ → sa16y5_Dec (j + 2) W a →
      ∀ idx : Fin j → Fin d, eLpNorm (partialDeriv idx (sa16y3_PA s A a φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal K * sa16z_S p φ j := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (1 : ℝ) ≤ p)
  obtain ⟨K0, hK00, hK0⟩ := sa16y6c_D0 hd hs0 hs1 hp hfar hW
  intro j
  induction j with
  | zero =>
    refine ⟨(d : ℝ) * d * (AB * K0), by positivity, fun {A} hA hskew {a φ} ha hφ hdec idx => ?_⟩
    have hz : partialDeriv idx (sa16y3_PA s A a φ) = sa16y3_PA s A a φ := funext fun y => sa16j_pd_zero idx _ y
    rw [hz]
    have hfun : sa16y3_PA s A a φ = ∑ i : Fin d, ∑ j : Fin d, (-(A j i)) • (fun x => fderiv ℝ
        (convFun (rieszKernel d s) (fun y => sa16z_dm a j y * φ y)) x (sa16z_e i)) := by
      funext x
      rw [sa16y3_PA_skew hs0 hsd hskew ha hφ x]
      simp [Finset.sum_apply, sa16y3_Q, neg_mul, Finset.sum_neg_distrib]
    have hφS : eLpNorm φ (ENNReal.ofReal p) volume ≤ sa16z_S p φ 0 := by
      have := sa16y5_w_le_S (p := p) hφ.1 (fun l : Fin 0 => l.elim0)
      have hz0 : partialDeriv (fun l : Fin 0 => l.elim0 : Fin 0 → Fin d) φ = φ :=
        funext fun y => sa16j_pd_zero _ φ y
      rwa [hz0] at this
    have hterm : ∀ i j : Fin d, eLpNorm ((-(A j i)) • (fun x => fderiv ℝ
        (convFun (rieszKernel d s) (fun y => sa16z_dm a j y * φ y)) x (sa16z_e i))) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (AB * K0) * sa16z_S p φ 0 := by
      intro i j
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_neg]
      refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (hA j i))
        ((hK0 (sa16z_dm_smooth ha j) (sa16y5_Dec_dm ha (sa16y5_Dec_mono (by omega) hdec) j) hφ i).trans
          (mul_le_mul' le_rfl hφS))) ?_
      exact le_of_eq (by rw [ENNReal.ofReal_mul hAB, mul_assoc])
    rw [hfun]
    refine (eLpNorm_sum_le hp1).trans ((Finset.sum_le_sum fun i _ => eLpNorm_sum_le hp1).trans
      ((Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j).trans (le_of_eq ?_)))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (d : ℝ) * d), ENNReal.ofReal_mul (Nat.cast_nonneg d),
      ENNReal.ofReal_natCast]
    ring
  | succ j ih =>
    obtain ⟨K, hK0', hK⟩ := ih
    refine ⟨2 * K, by positivity, fun {A} hA hskew {a φ} ha hφ hdec idx => ?_⟩
    obtain ⟨l, idx', rfl⟩ : ∃ (l : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons l idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    have hPAs : ContDiff ℝ ∞ (sa16y3_PA s A a φ) := sa16y3_PA_smooth hs0 hsd A ha hφ
    have hA1 : ContDiff ℝ ∞ (sa16y3_PA s A (sa16z_dm a l) φ) := sa16y3_PA_smooth hs0 hsd A (sa16z_dm_smooth ha l) hφ
    have hA2 : ContDiff ℝ ∞ (sa16y3_PA s A a (sa16z_dm φ l)) := sa16y3_PA_smooth hs0 hsd A ha (sa16z_dm_cc hφ l)
    have hfun : partialDeriv (Fin.cons l idx' : Fin (j + 1) → Fin d) (sa16y3_PA s A a φ) =
        partialDeriv idx' (sa16y3_PA s A (sa16z_dm a l) φ) + partialDeriv idx' (sa16y3_PA s A a (sa16z_dm φ l)) := by
      rw [sa16z_pd_cons_eq hPAs]
      have : sa16z_dm (sa16y3_PA s A a φ) l = fun y => sa16y3_PA s A (sa16z_dm a l) φ y +
          sa16y3_PA s A a (sa16z_dm φ l) y := funext fun y => sa16y6c_PA_deriv hs0 hsd A ha hφ l y
      rw [this]
      funext x
      rw [sa16sy_pd_add hA1 hA2]
      rfl
    rw [hfun]
    have e2 := hK hA hskew (sa16z_dm_smooth ha l) hφ (sa16y5_Dec_dm ha hdec l) idx'
    have e3 := hK hA hskew ha (sa16z_dm_cc hφ l) (sa16y5_Dec_mono (by omega) hdec) idx'
    have hS2 : sa16z_S p (sa16z_dm φ l) j ≤ sa16z_S p φ (j + 1) := sa16z_S_dm_le hφ.1 l j
    have hS1 : sa16z_S p φ j ≤ sa16z_S p φ (j + 1) := sa16z_S_mono φ (by omega)
    refine (eLpNorm_add_le hp1).trans ?_
    calc _ ≤ ENNReal.ofReal K * sa16z_S p φ (j + 1) + ENNReal.ofReal K * sa16z_S p φ (j + 1) :=
          add_le_add (e2.trans (by gcongr)) (e3.trans (by gcongr))
      _ = ENNReal.ofReal (2 * K) * sa16z_S p φ (j + 1) := by
          rw [← add_mul, ← ENNReal.ofReal_add hK0' hK0']
          congr 2; ring

end Hl1

end HRS.Whole.AppendixA.Phase2SA16R
