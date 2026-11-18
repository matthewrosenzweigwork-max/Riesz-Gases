import HRS.MC.QRPHdAux4
import HRS.MC.WCI
import HRS.Equilibrium.FieldSingAux

/-!
# Packet HD, part 5: complex expansion of `hTransport` and the Wick coefficient formula
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped BigOperators ComplexConjugate

namespace HRS.MC.QRSpec.Hd

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

theorem hd_grad_expand (κ : NonzeroLattice d) (x : Torus d) (i : Fin d) :
    (((Torus.grad (Torus.realMode κ) x) i : ℝ) : ℂ) =
      ∑ b : Bool, hdcf κ.1 b * (2 * Real.pi * Complex.I * (((hdsg b • κ.1) i : ℤ) : ℂ)) *
        Torus.mode (hdsg b • κ.1) x := by
  rw [Fintype.sum_bool, hd_sg_smul_true, hd_sg_smul_false, hd_grad_real]
  have hneg : (((-κ.1) i : ℤ) : ℂ) = -((κ.1 i : ℤ) : ℂ) := by simp
  rw [hneg, Torus.mode_neg]
  simp only [hdcf, if_true, ite_false, Bool.false_eq_true]
  by_cases hp : Lattice.IsPosHalf κ.1
  · simp only [hp, if_true]
    rw [Torus.realCoef_pos hp]
    simp only [Torus.sinMode]
    rw [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_mul, Complex.im_eq_sub_conj]
    simp only [Complex.conj_ofReal]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  · simp only [hp, ite_false]
    rw [Torus.realCoef_neg hp]
    simp only [Torus.cosMode]
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.re_eq_add_conj]
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring

theorem hd_hT_expand (κ : NonzeroLattice d) (x y : Torus d) :
    ((hTransport d s (Torus.realMode κ) x y : ℝ) : ℂ) =
      ∑ b : Bool, hdcf κ.1 b * hdH d s (hdsg b • κ.1) x y := by
  unfold hTransport
  simp only [PiLp.inner_apply, PiLp.sub_apply]
  push_cast
  have h1 : ∀ i : Fin d, (((inner ℝ ((Torus.grad (Torus.realMode κ) x).ofLp i - (Torus.grad (Torus.realMode κ) y).ofLp i)
      ((periodicRieszGrad d s (x - y)).ofLp i) : ℝ)) : ℂ) =
      ((((Torus.grad (Torus.realMode κ) x) i : ℝ) : ℂ) - (((Torus.grad (Torus.realMode κ) y) i : ℝ) : ℂ)) *
        hdGc d s i (x - y) := by
    intro i
    simp only [RCLike.inner_apply, conj_trivial, hdGc]
    push_cast
    ring
  simp_rw [h1, hd_grad_expand]
  unfold hdH
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hd_integrable_H (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (lam β : Lattice d) (x : Torus d) :
    Integrable (fun y => hdH d s lam x y * Torus.mode β y) := by
  set c : Fin d → ℂ := fun i => 2 * Real.pi * Complex.I * ((lam i : ℤ) : ℂ) with hc
  have e : ∀ y, hdH d s lam x y * Torus.mode β y = ∑ i, c i *
      (Torus.mode lam x * (hdGc d s i (x - y) * Torus.mode β y) -
        hdGc d s i (x - y) * Torus.mode (lam + β) y) := by
    intro y
    unfold hdH
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Torus.mode_add]
    simp only [hc]
    ring
  simp_rw [e]
  exact integrable_finsetSum _ fun i _ =>
    (((hd_integrable_Gmode hd hs0 hs1 i β x).const_mul _).sub
      (hd_integrable_Gmode hd hs0 hs1 i (lam + β) x)).const_mul _

theorem hd_inner_formula (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) (κ b : NonzeroLattice d) (x : Torus d) :
    ((∫ y, hTransport d s (Torus.realMode κ) x y * Torus.realMode b y : ℝ) : ℂ) =
      ∑ ε : Bool, ∑ τ : Bool, hdcf κ.1 ε * hdcf b.1 τ *
        (hdK d s (hdsg ε • κ.1) (hdsg τ • b.1) * Torus.mode (hdsg ε • κ.1 + hdsg τ • b.1) x) := by
  rw [← integral_complex_ofReal]
  have e : ∀ y, (((hTransport d s (Torus.realMode κ) x y * Torus.realMode b y : ℝ)) : ℂ) =
      ∑ ε : Bool, ∑ τ : Bool, hdcf κ.1 ε * hdcf b.1 τ *
        (hdH d s (hdsg ε • κ.1) x y * Torus.mode (hdsg τ • b.1) y) := by
    intro y
    rw [Complex.ofReal_mul, hd_hT_expand, hd_realMode_expand, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun τ _ => ?_
    ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun ε _ => integrable_finsetSum _ fun τ _ =>
    (hd_integrable_H hd hs0 hs1 _ _ x).const_mul _)]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [integral_finsetSum _ (fun τ _ => (hd_integrable_H hd hs0 hs1 _ _ x).const_mul _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, hdJ hd hs0 hs1]

/-- The Wick coefficient of `h_{∇e_κ}` in the real basis, as a signed sum of the multipliers `K`. -/
theorem hd_wick_formula (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) (κ a b : NonzeroLattice d) :
    ((Sec7.wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode κ)) a b : ℝ) : ℂ) =
      ∑ σ : Bool, ∑ ε : Bool, ∑ τ : Bool, hdcf a.1 σ * hdcf κ.1 ε * hdcf b.1 τ *
        (if hdsg σ • a.1 + hdsg ε • κ.1 + hdsg τ • b.1 = 0 then
          hdK d s (hdsg ε • κ.1) (hdsg τ • b.1) else 0) := by
  rw [WCI.wci_wick_eq hs0 (by linarith) (HRS.FieldSingAux.isSmooth_realMode κ) hΛ a b,
    ← integral_complex_ofReal]
  have e : ∀ x, (((Torus.realMode a x * ∫ y, hTransport d s (Torus.realMode κ) x y * Torus.realMode b y : ℝ)) : ℂ) =
      ∑ σ : Bool, ∑ ε : Bool, ∑ τ : Bool, hdcf a.1 σ * hdcf κ.1 ε * hdcf b.1 τ * hdK d s (hdsg ε • κ.1) (hdsg τ • b.1) *
        Torus.mode (hdsg σ • a.1 + hdsg ε • κ.1 + hdsg τ • b.1) x := by
    intro x
    rw [Complex.ofReal_mul, hd_realMode_expand, hd_inner_formula hd hs0 hs1, Finset.sum_mul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [add_assoc, Torus.mode_add (hdsg σ • a.1) (hdsg ε • κ.1 + hdsg τ • b.1)]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ fun ε _ => integrable_finsetSum _ fun τ _ =>
    (Torus.integrable_mode _).const_mul _)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [integral_finsetSum _ (fun ε _ => integrable_finsetSum _ fun τ _ =>
    (Torus.integrable_mode _).const_mul _)]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [integral_finsetSum _ (fun τ _ => (Torus.integrable_mode _).const_mul _)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [integral_const_mul, Torus.integral_mode]
  split_ifs <;> ring

end HRS.MC.QRSpec.Hd

end
