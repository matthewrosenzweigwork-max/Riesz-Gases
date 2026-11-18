import HRS.MS.MainRdPathAux8

/-!
# S.A.9, packet P3c: the tail function of the transported initial field

`sa9_Gt h Cf t m Lc x = ∑_{i ≤ m} d^i ∑_{α, |α| = i} ∑_{ℓ ≥ Lc} (∂^α U^{0,t}φ_ℓ(x))²` (in `ℝ≥0∞`), the pointwise
dominating function of `∑_ℓ |D^{≤m}(U^{0,t}φ_{ℓ+Lc})(x)|²`.  `sa9_Gt_cmp`: the comparison of the tail functions of two
propagators through the `C_b^{m+1}` distance of their images; `sa9_mriG_le`: the domination.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit

variable {d : ℕ}

/-- The tail function. -/
def sa9_Gt (h : ℕ → mhn_Hc d) (Cf : WholeCoeff d) (t : ℝ) (m Lc : ℕ) (x : Euc d) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d,
    ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW Cf 0 t (mhn_phi (h (l + Lc)))) x) ^ 2)

/-- The dimensional constant of the comparison. -/
def sa9_Cdim (d m : ℕ) : ℝ := ∑ i ∈ Finset.range (m + 1), (d : ℝ) ^ i * (d : ℝ) ^ i

theorem sa9_Cdim_nonneg (d m : ℕ) : 0 ≤ sa9_Cdim d m :=
  Finset.sum_nonneg fun i _ => by positivity

theorem sa9_const_sum (m : ℕ) (D : ℝ) :
    ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) *
      ∑ _idx : Fin i → Fin d, ENNReal.ofReal (D ^ 2) = ENNReal.ofReal (sa9_Cdim d m * D ^ 2) := by
  unfold sa9_Cdim
  rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  ring

theorem sa9_partial_cont {i : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ i f) (idx : Fin i → Fin d) :
    Continuous (partialDeriv idx f) := by
  have h1 : Continuous (iteratedFDeriv ℝ i f) := hf.continuous_iteratedFDeriv le_rfl
  have h2 : (partialDeriv idx f) = fun x => iteratedFDeriv ℝ i f x (fun l => EuclideanSpace.single (idx l) 1) := rfl
  rw [h2]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin i => Euc d) ℝ
    (fun l => EuclideanSpace.single (idx l) 1)).continuous.comp h1

section Cmp

variable {q : ℕ} {m : ℕ} {T K₁ K₂ : ℝ} {CfN CfL : WholeCoeff d}

theorem sa9_Gt_cmp (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    (hN : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) CfN T K₁) (hL : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) CfL T K₂)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {D : ℝ}
    (hdiff : ∀ g : mhn_Hc d,
      MemCb (m + 1) (fun x => propagatorW CfN 0 t (mhn_phi g) x - propagatorW CfL 0 t (mhn_phi g) x) ∧
        cbNorm (m + 1) (fun x => propagatorW CfN 0 t (mhn_phi g) x - propagatorW CfL 0 t (mhn_phi g) x) ≤
          D * HRS.Whole.sobolevNorm ((q : ℕ) : ℝ) (mhn_phi g)) (Lc : ℕ) (x : Euc d) :
    sa9_Gt h CfN t m Lc x ≤ 2 * sa9_Gt h CfL t m Lc x + 2 * ENNReal.ofReal (sa9_Cdim d m * D ^ 2) := by
  have hcdN : ∀ g : mhn_Hc d, ContDiff ℝ (m + 1 : ℕ) (propagatorW CfN 0 t (mhn_phi g)) := fun g =>
    (hN 0 t le_rfl ht0 htT _ (mhn_isSobolevTest_phi _ g)).2.1
  have hcdL : ∀ g : mhn_Hc d, ContDiff ℝ (m + 1 : ℕ) (propagatorW CfL 0 t (mhn_phi g)) := fun g =>
    (hL 0 t le_rfl ht0 htT _ (mhn_isSobolevTest_phi _ g)).2.1
  set P : (Euc d → ℝ) → (Euc d → ℝ) := fun f y => propagatorW CfN 0 t f y - propagatorW CfL 0 t f y with hPdef
  have hadd : ∀ a b : mhn_Hc d, P (mhn_phi (a + b)) = P (mhn_phi a) + P (mhn_phi b) := by
    intro a b
    funext y
    simp only [hPdef, mri_phi_add, mri_prop_add hN ht0 htT (mhn_isSobolevTest_phi _ a)
      (mhn_isSobolevTest_phi _ b), mri_prop_add hL ht0 htT (mhn_isSobolevTest_phi _ a)
      (mhn_isSobolevTest_phi _ b), Pi.add_apply]
    ring
  have hsmul : ∀ (c : ℝ) (a : mhn_Hc d), P (mhn_phi (c • a)) = c • P (mhn_phi a) := by
    intro c a
    funext y
    simp only [hPdef, mri_phi_smul, mri_prop_smul hN ht0 htT (mhn_isSobolevTest_phi _ a),
      mri_prop_smul hL ht0 htT (mhn_isSobolevTest_phi _ a), Pi.smul_apply, smul_eq_mul]
    ring
  have hcd : ∀ a : mhn_Hc d, ContDiff ℝ (m + 1 : ℕ) (P (mhn_phi a)) := fun a => (hcdN a).sub (hcdL a)
  have per : ∀ i ∈ Finset.range (m + 1), ∀ idx : Fin i → Fin d,
      ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW CfN 0 t (mhn_phi (h (l + Lc)))) x) ^ 2) ≤
        2 * ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW CfL 0 t (mhn_phi (h (l + Lc)))) x) ^ 2) +
          2 * ENNReal.ofReal (D ^ 2) := by
    intro i hi idx
    have hi' : i ≤ m + 1 := by have := Finset.mem_range.1 hi; omega
    have hD : ∀ n, ∑ l ∈ Finset.range n, (partialDeriv idx (propagatorW CfN 0 t (mhn_phi (h l))) x -
        partialDeriv idx (propagatorW CfL 0 t (mhn_phi (h l))) x) ^ 2 ≤ D ^ 2 := by
      intro n
      have hb := sa9_bessel (q := q) h hP (i := i) P idx x hadd hsmul (fun a => (hcd a).of_le (by exact_mod_cast hi'))
        (C := D) (fun g => ?_) n
      · refine le_of_eq_of_le (Finset.sum_congr rfl fun l _ => ?_) hb
        simp only [hPdef]
        rw [mri_partialDeriv_sub ((hcdN _).of_le (by exact_mod_cast hi')) ((hcdL _).of_le (by exact_mod_cast hi'))]
      · exact (sa9_partial_le_cb (hdiff g).1 hi' idx x).trans (hdiff g).2
    exact sa9_tail_cmp _ _ Lc hD
  unfold sa9_Gt
  calc ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d,
        ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW CfN 0 t (mhn_phi (h (l + Lc)))) x) ^ 2)
      ≤ ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d,
        (2 * ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW CfL 0 t (mhn_phi (h (l + Lc)))) x) ^ 2) +
          2 * ENNReal.ofReal (D ^ 2)) :=
        Finset.sum_le_sum fun i hi => mul_le_mul' le_rfl (Finset.sum_le_sum fun idx _ => per i hi idx)
    _ = ∑ i ∈ Finset.range (m + 1), (2 * (ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d,
          ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW CfL 0 t (mhn_phi (h (l + Lc)))) x) ^ 2)) +
        2 * (ENNReal.ofReal ((d : ℝ) ^ i) * ∑ _idx : Fin i → Fin d, ENNReal.ofReal (D ^ 2))) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
    _ = 2 * ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) * ∑ idx : Fin i → Fin d,
        ∑' l, ENNReal.ofReal ((partialDeriv idx (propagatorW CfL 0 t (mhn_phi (h (l + Lc)))) x) ^ 2) +
        2 * ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ((d : ℝ) ^ i) *
          ∑ _idx : Fin i → Fin d, ENNReal.ofReal (D ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [sa9_const_sum]

end Cmp

end HRS.MS.MainRdPath
