import HRS.Commutator.Torus.NRSTAux47

/-!
# NRS-T, part 48: the expansion of `Jf`, and the limit of the pairing
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_adv_coeff (V : Fin d → NRST.TPA d) (h : NRST.TPA d) (m : Lattice d) :
    (NRST.adv V h).coeff m = ∑ c, ∑ j ∈ (V c).coeff.support, (V c).coeff j *
      ((2 * Real.pi * Complex.I * (((-j + m) c : ℤ) : ℂ)) * h.coeff (-j + m)) := by
  unfold NRST.adv
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [AddMonoidAlgebra.coeff_mul_apply_left]
  simp only [Finsupp.sum, NRST.coeff_dd]

lemma nrstr_Jf_eq (V : Fin d → NRST.TPA d) (σ' : ℝ) (h : NRST.TPA d) :
    NRST.Jf V σ' h = ∑ k ∈ h.coeff.support, ((NRST.lw σ' k : ℝ) : ℂ) * h.coeff k *
      ∑ c, ∑ j ∈ (V c).coeff.support, (V c).coeff j *
        ((2 * Real.pi * Complex.I * (((-j + -k) c : ℤ) : ℂ)) * h.coeff (-j + -k)) := by
  unfold NRST.Jf
  rw [NRST.pr_eq_sum_of_subset (NRST.lam σ' h) (NRST.adv V h) (NRST.supp_mulSeq_subset _ h)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [nrstr_adv_coeff]
  simp [NRST.lam]

lemma nrstr_pair_tendsto {σ : ℝ} (hσ : 0 < σ) (V : Fin d → NRST.TPA d)
    (hVr : ∀ j x, (NRST.ev (V j) x).im = 0) (h : NRST.TPA d) :
    Tendsto (fun n : ℕ => HRS.Commutator.Whole.XNRS.xpair (2 * σ)
        (nrstr_W h ((n : ℝ) + 1) (by positivity))
        (HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) (nrstr_W h ((n : ℝ) + 1) (by positivity))) /
        ((((n : ℝ) + 1) ^ d : ℝ) : ℂ)) atTop
      (𝓝 (((nrstr_m0 d : ℝ) : ℂ) * NRST.Jf V (2 * σ) h)) := by
  classical
  have hN1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hNpos : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by linarith [hN1 n]
  set coef : Lattice d → Fin d → Lattice d → ℂ := fun k c j =>
    h.coeff k * (V c).coeff j * h.coeff (-j - k) * (2 * Real.pi * Complex.I) with hcoef
  have heq : ∀ n : ℕ, HRS.Commutator.Whole.XNRS.xpair (2 * σ)
        (nrstr_W h ((n : ℝ) + 1) (by positivity))
        (HRS.Commutator.Whole.XNRS.xadv (nrstr_v V) (nrstr_W h ((n : ℝ) + 1) (by positivity))) /
        ((((n : ℝ) + 1) ^ d : ℝ) : ℂ) =
      ∑ k ∈ h.coeff.support, ∑ c, ∑ j ∈ (V c).coeff.support,
        coef k c j * nrstr_S σ ((n : ℝ) + 1) k (-j - k) c := by
    intro n
    have hNd : ((((n : ℝ) + 1) ^ d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (((n : ℝ) + 1) ^ d : ℝ) ≠ 0)
    rw [nrstr_pair_eq hσ V hVr h (hN1 n), div_eq_iff hNd, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [nrstr_tm_integral σ h V (hNpos n) k c j]
    simp only [hcoef]
    ring
  simp_rw [heq]
  have hlim : Tendsto (fun n : ℕ => ∑ k ∈ h.coeff.support, ∑ c, ∑ j ∈ (V c).coeff.support,
      coef k c j * nrstr_S σ ((n : ℝ) + 1) k (-j - k) c) atTop
      (𝓝 (∑ k ∈ h.coeff.support, ∑ c, ∑ j ∈ (V c).coeff.support,
        coef k c j * ((((2 * Real.pi * ‖Lattice.toEuc k‖) ^ (2 * σ) * (((-j - k) c : ℤ) : ℝ) : ℝ) : ℂ) *
          ((nrstr_m0 d : ℝ) : ℂ)))) := by
    refine tendsto_finset_sum _ fun k _ => tendsto_finset_sum _ fun c _ => tendsto_finset_sum _ fun j _ => ?_
    exact (nrstr_S_tendsto hσ k (-j - k) c).const_mul _
  convert hlim using 2
  rw [nrstr_Jf_eq]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  have hlw : ((NRST.lw (2 * σ) k : ℝ) : ℂ) = (((2 * Real.pi * ‖Lattice.toEuc k‖) ^ (2 * σ) : ℝ) : ℂ) := by
    rw [← nrstr_rpow_lw (by linarith : (2 * σ) ≠ 0)]; rfl
  have hl : -j + -k = -j - k := by abel
  rw [hlw, hl]
  simp only [hcoef]
  push_cast
  ring

end HRS.Commutator.TorusNote
