import HRS.Commutator.Torus.NRSTAux6
import HRS.Commutator.Torus.Defs

/-!
# NRS-T, part 7: `𝒞_g(v,a) = 2 Re pr A (v·∇(g*A))` for real trigonometric polynomials
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- `v_j(x) e_j`. -/
def vj (V : Fin d → TPA d) (j : Fin d) (x : Torus d) : Euc d :=
  (ev (V j) x).re • EuclideanSpace.single j (1 : ℝ)

lemma commKernel_sum (G : Torus d → Euc d) (V : Fin d → TPA d) (x y : Torus d) :
    commKernel G (vOf V) x y = ∑ j, commKernel G (vj V j) x y := by
  unfold commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [ite_eq_right_iff, hxy, false_implies, if_false]
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [vj, vOf, ← sub_smul, real_inner_smul_left, EuclideanSpace.inner_single_left,
      PiLp.sub_apply, PiLp.toLp_apply]
    simp [mul_comm]

lemma isLip_vj (V : Fin d → TPA d) {L : ℝ} (hLip : IsLipschitzVF L (vOf V)) (j : Fin d) :
    IsLipschitzVF L (vj V j) := by
  intro x y
  have h1 : vj V j x - vj V j y = ((ev (V j) x).re - (ev (V j) y).re) • EuclideanSpace.single j (1 : ℝ) := by
    simp [vj, sub_smul]
  rw [h1, norm_smul, PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs]
  refine le_trans ?_ (hLip x y)
  have := PiLp.norm_apply_le (vOf V x - vOf V y) j
  simpa [vOf, Real.norm_eq_abs] using this

lemma isLip_scalar (V : Fin d → TPA d) {L : ℝ} (hLip : IsLipschitzVF L (vOf V)) (j : Fin d) :
    KernelGrad.IsLipschitz L (fun x => (ev (V j) x).re) := by
  intro x y
  refine le_trans ?_ (hLip x y)
  have := PiLp.norm_apply_le (vOf V x - vOf V y) j
  simpa [vOf, Real.norm_eq_abs] using this

lemma comm_pointwise (G : Torus d → Euc d) (V : Fin d → TPA d) (j : Fin d) (w : Torus d → ℝ)
    (p : Torus d × Torus d) :
    commKernel G (vj V j) p.1 p.2 * w p.1 * w p.2 =
      -(inner ℝ (EuclideanSpace.single j (1 : ℝ)) (G (p.1 - p.2)) * w p.1 * w p.2 *
        ((ev (V j) p.2).re - (ev (V j) p.1).re)) := by
  unfold commKernel
  by_cases hxy : p.1 = p.2
  · simp [hxy]
  · simp only [ite_eq_right_iff, hxy, false_implies, if_false]
    simp only [vj, ← sub_smul, real_inner_smul_left]
    ring

lemma prod_real_cast (V A : TPA d) (hV : ∀ x, (ev V x).im = 0) (hA : ∀ x, (ev A x).im = 0) :
    (fun x => (ev V x).re * aOf A x) = fun x => (ev (V * A) x).re := by
  funext x
  rw [ev_mul, Pi.mul_apply, Complex.mul_re, hV, hA]
  simp [aOf]

theorem comm_eq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (V : Fin d → TPA d) (A : TPA d)
    {L : ℝ} (hL0 : 0 ≤ L) (hVr : ∀ j x, (ev (V j) x).im = 0) (hAr : ∀ x, (ev A x).im = 0)
    (hLip : IsLipschitzVF L (vOf V)) :
    CcommFunT (periodicRieszGrad d s) (vOf V) (aOf A) = 2 * (pr A (adv V (Rg d s A))).re := by
  have hd1 : 1 ≤ d := by omega
  have hd2 : 2 ≤ d := by omega
  have hsd' : s < (d : ℝ) := by linarith
  obtain ⟨B, hB0, hB⟩ := KernelGrad.isCk_bounded (isCk_aOf A 1)
  have hwm : Measurable (aOf A) := (KernelGrad.isCk_continuous (isCk_aOf A 1)).measurable
  set G := periodicRieszGrad d s with hG
  have hint : ∀ j, Integrable (fun p : Torus d × Torus d =>
      commKernel G (vj V j) p.1 p.2 * aOf A p.1 * aOf A p.2) (volume.prod volume) := fun j =>
    integrable_commProd hd1 hs0 hsd' hL0 (isLip_vj V hLip j) hwm hB
  have hintV := integrable_commProd hd1 hs0 hsd' hL0 hLip hwm hB
  have hB1 : CcommFunT G (vOf V) (aOf A) = ∫ p : Torus d × Torus d,
      commKernel G (vOf V) p.1 p.2 * aOf A p.1 * aOf A p.2 ∂(volume.prod volume) := by
    unfold CcommFunT
    rw [integral_prod _ hintV]
  have hB2 : ∫ p : Torus d × Torus d, commKernel G (vOf V) p.1 p.2 * aOf A p.1 * aOf A p.2
      ∂(volume.prod volume) = ∑ j, ∫ p : Torus d × Torus d,
        commKernel G (vj V j) p.1 p.2 * aOf A p.1 * aOf A p.2 ∂(volume.prod volume) := by
    rw [← integral_finset_sum _ (fun j _ => hint j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [commKernel_sum, Finset.sum_mul]
  have hj : ∀ j, ∫ p : Torus d × Torus d, commKernel G (vj V j) p.1 p.2 * aOf A p.1 * aOf A p.2
      ∂(volume.prod volume) = 2 * (pr A (V j * dd j (Rg d s A))).re := by
    intro j
    obtain ⟨n, hn⟩ := isTrigPoly_aOf A hAr
    have key := KernelGrad.rieszGrad_pairing_symmetrized hd2 s hs0 hsd' (EuclideanSpace.single j (1 : ℝ))
      L (fun x => (ev (V j) x).re) (isLip_scalar V hLip j) n (aOf A) (isCk_aOf A 1) hn
    have hcoef1 : KernelGrad.coeffOf (fun x => (ev (V j) x).re * aOf A x) =
        fun k => (V j * A).coeff k := by
      rw [prod_real_cast (V j) A (hVr j) hAr]
      funext k
      exact coeffOf_re_ev (V j * A) (ev_mul_real _ _ (hVr j) hAr) k
    have hcoef2 : ∀ k, (starRingEnd ℂ) (KernelGrad.coeffOf (aOf A) k) = A.coeff (-k) := by
      intro k
      unfold aOf
      rw [coeffOf_re_ev A hAr]
      exact conj_coeff_of_real A hAr k
    have hsum : (∑' k : Lattice d, ((2 * Real.pi * Complex.I *
        ((inner ℝ (EuclideanSpace.single j (1 : ℝ)) (Lattice.toEuc k) : ℝ) : ℂ)) *
        ((rieszCoeff d s k : ℝ) : ℂ)) *
        (KernelGrad.coeffOf (fun x => (ev (V j) x).re * aOf A x) k *
          (starRingEnd ℂ) (KernelGrad.coeffOf (aOf A) k))) = - pr A (V j * dd j (Rg d s A)) := by
      rw [← fourier_side_j s j (V j) A]
      rw [tsum_eq_sum (s := (V j * A).coeff.support)]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [hcoef1, hcoef2]
        have : (inner ℝ (EuclideanSpace.single j (1 : ℝ)) (Lattice.toEuc k) : ℝ) = ((k j : ℤ) : ℝ) := by
          simp [EuclideanSpace.inner_single_left, Lattice.toEuc]
        rw [this]
        push_cast
        ring
      · intro k hk
        rw [hcoef1]
        have : (V j * A).coeff k = 0 := by simpa using hk
        simp [this]
    have key2 : (-(pr A (V j * dd j (Rg d s A)))).re = (1 / 2) * ∫ p : Torus d × Torus d,
        inner ℝ (EuclideanSpace.single j (1 : ℝ)) (G (p.1 - p.2)) * aOf A p.1 * aOf A p.2 *
          ((ev (V j) p.2).re - (ev (V j) p.1).re) ∂(volume.prod volume) := by
      rw [← hsum]
      rw [Measure.volume_eq_prod] at key
      exact key
    have e : ∫ p : Torus d × Torus d, commKernel G (vj V j) p.1 p.2 * aOf A p.1 * aOf A p.2
        ∂(volume.prod volume) = -∫ p : Torus d × Torus d,
        inner ℝ (EuclideanSpace.single j (1 : ℝ)) (G (p.1 - p.2)) * aOf A p.1 * aOf A p.2 *
          ((ev (V j) p.2).re - (ev (V j) p.1).re) ∂(volume.prod volume) := by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => comm_pointwise G V j (aOf A) p)
    rw [e]
    rw [Complex.neg_re] at key2
    linarith
  rw [hB1, hB2, Finset.sum_congr rfl fun j _ => hj j, ← Finset.mul_sum]
  congr 1
  unfold adv
  rw [pr_sum_right, Complex.re_sum]

end HRS.Commutator.TorusNote.NRST
