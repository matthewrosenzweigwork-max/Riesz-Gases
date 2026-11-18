import HRS.MS.MfeConfAux23

/-!
# S.B.1, packet F3 (part 5): the flux `J = ρ u_V` and `∂_t ρ = Div J`: regularity and decay

* `sb1J D h k y = h(y) (u_V)_k(y)`; `sb1_J_eq`: `J_k = β⁻¹ ∂_k h + Flux_k`; `sb1_J_contDiff`: `J_k ∈ C¹`.
* `Sb1Tr3.J_bound`, `dJ_bound`, `A_bound`: `|J_k| ≤ C_J w₂`, `|∂_k J_k| ≤ C_dJ w₂`, `|A(ρ_r)| ≤ d C_dJ w₂`, `w₂ = (1+|y|)^{-(d+2)}`.
* `sb1_A_eq_sumJ`: `A(h) = ∑_k ∂_k J_k`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- the flux component `J_k = h (u_V)_k` -/
def sb1J (D : Whole.WholeDyn d) (h : Euc d → ℝ) (k : Fin d) (y : Euc d) : ℝ :=
  h y * (Whole.mfeTransportW D h y) k

theorem sb1w_32 (y : Euc d) : sb1w ((d : ℝ) + 3) y * (1 + ‖y‖) = sb1w ((d : ℝ) + 2) y := by
  have := sb1w_succ ((d : ℝ) + 2) y
  rwa [show (d : ℝ) + 2 + 1 = (d : ℝ) + 3 by ring] at this

section Flux

variable {D : Whole.WholeDyn d} {B C : ℝ} {h : Euc d → ℝ}

theorem sb1_J_eq (hS : Sb1Slice d C h) (hpos : ∀ y, 0 < h y) (k : Fin d) :
    sb1J D h k = fun y => D.invβ * fderiv ℝ h y (sb1e k) + sb1Flux D h k y :=
  funext fun y => sb1_transport_apply D ((sb1_slice_facts hS).1.differentiable (by norm_num)) hpos k y

theorem sb1_J_contDiff (P : Sb1Pot D.V B) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hS : Sb1Slice d C h) (hpos : ∀ y, 0 < h y) (k : Fin d) : ContDiff ℝ 1 (sb1J D h k) := by
  rw [sb1_J_eq hS hpos k]
  have hh : ContDiff ℝ 3 h := (sb1_slice_facts hS).1
  have h1 : ContDiff ℝ 1 (fun y => fderiv ℝ h y (sb1e k)) :=
    ((hh.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).of_le (by norm_num)
  exact (contDiff_const.mul h1).add (sb1_flux_contDiff D P hd hs0 hsd hS k)

theorem sb1_fderiv_J (P : Sb1Pot D.V B) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hS : Sb1Slice d C h) (hpos : ∀ y, 0 < h y) (k : Fin d) (x : Euc d) :
    fderiv ℝ (sb1J D h k) x (sb1e k) =
      D.invβ * fderiv ℝ (fun y => fderiv ℝ h y (sb1e k)) x (sb1e k) + fderiv ℝ (sb1Flux D h k) x (sb1e k) := by
  rw [sb1_J_eq hS hpos k]
  have hh : ContDiff ℝ 3 h := (sb1_slice_facts hS).1
  have hd1 : DifferentiableAt ℝ (fun y => fderiv ℝ h y (sb1e k)) x :=
    (((hh.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const).differentiable (by norm_num)) x
  have hd2 : DifferentiableAt ℝ (sb1Flux D h k) x :=
    ((sb1_flux_contDiff D P hd hs0 hsd hS k).differentiable (by norm_num)) x
  rw [fderiv_fun_add (hd1.const_mul _) hd2, fderiv_const_mul hd1]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem sb1_A_eq_sumJ (P : Sb1Pot D.V B) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hS : Sb1Slice d C h) (hpos : ∀ y, 0 < h y) (x : Euc d) :
    sb1A D h x = ∑ k, fderiv ℝ (sb1J D h k) x (sb1e k) :=
  sb1A_eq_div D P hd hs0 hsd hS hpos x

end Flux

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ}

def sb1CJ (D : Whole.WholeDyn d) (B C C3 : ℝ) : ℝ :=
  C3 * (|D.invβ| + ‖fderiv ℝ D.V 0‖ + sb1BF d D.s C + B)

def sb1CdJ (D : Whole.WholeDyn d) (B C C3 : ℝ) : ℝ :=
  C3 * (|D.invβ| + ‖fderiv ℝ D.V 0‖ + 2 * sb1BF d D.s C + 2 * B)

theorem Sb1Tr3.CJ_nonneg (H : Sb1Tr3 D T C B C3 ρ) : 0 ≤ sb1CJ D B C C3 := by
  have hB := H.tr.V.B_nonneg
  have hBF := sb1BF_nonneg (d := d) H.tr.hs0 H.tr.hC
  unfold sb1CJ
  have := H.C3nn
  positivity

theorem Sb1Tr3.CdJ_nonneg (H : Sb1Tr3 D T C B C3 ρ) : 0 ≤ sb1CdJ D B C C3 := by
  have hB := H.tr.V.B_nonneg
  have hBF := sb1BF_nonneg (d := d) H.tr.hs0 H.tr.hC
  unfold sb1CdJ
  have := H.C3nn
  positivity

/-- pointwise ingredients -/
theorem Sb1Tr3.ingr (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (k : Fin d) (y : Euc d) :
    |fderiv ℝ (ρ r) y (sb1e k)| ≤ C3 * sb1w ((d : ℝ) + 3) y ∧ |ρ r y| ≤ C3 * sb1w ((d : ℝ) + 3) y ∧
    |fderiv ℝ D.V y (sb1e k)| ≤ ‖fderiv ℝ D.V 0‖ + B * ‖y‖ ∧
    |sb1F d D.s (ρ r) k y| ≤ sb1BF d D.s C ∧
    |fderiv ℝ (fun z => fderiv ℝ (ρ r) z (sb1e k)) y (sb1e k)| ≤ C3 * sb1w ((d : ℝ) + 3) y ∧
    |fderiv ℝ (fun z => fderiv ℝ D.V z (sb1e k)) y (sb1e k)| ≤ B ∧
    |fderiv ℝ (sb1F d D.s (ρ r) k) y (sb1e k)| ≤ sb1BF d D.s C := by
  have S := H.tr.slice r hr
  have P := H.tr.V
  have hh : DifferentiableAt ℝ (fderiv ℝ (ρ r)) y :=
    (((sb1_slice_facts S).1.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) y
  refine ⟨(sb1_apply_single_le _ k).trans (H.drho_le hr y), ?_, (sb1_apply_single_le _ k).trans (sb1_gradV_bound P y), ?_,
    ?_, sb1_ddV_k_le P k y, ?_⟩
  · rw [abs_of_pos (H.pos r hr y)]; exact H.rho_le hr y
  · have := (sb1F_contDiff H.tr.hd H.tr.hs0 H.tr.hsd S k).2 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · refine (sb1_ddk_le (ρ r) hh k).trans ?_
    rw [sb1_norm_fderiv_fderiv]
    have := H.dec r hr 2 (by norm_num) y
    exact this
  · have := (sb1F_contDiff H.tr.hd H.tr.hs0 H.tr.hsd S k).2 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at this
    exact (sb1_apply_single_le _ k).trans this

theorem Sb1Tr3.J_bound (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (k : Fin d) (y : Euc d) :
    |sb1J D (ρ r) k y| ≤ sb1CJ D B C C3 * sb1w ((d : ℝ) + 2) y := by
  have S := H.tr.slice r hr
  rw [show sb1J D (ρ r) k y = D.invβ * fderiv ℝ (ρ r) y (sb1e k) + sb1Flux D (ρ r) k y from
    congrFun (sb1_J_eq S (H.pos r hr) k) y]
  unfold sb1Flux
  obtain ⟨a1, a2, a3, a4, -, -, -⟩ := H.ingr hr k y
  have hB := H.tr.V.B_nonneg
  have hBF := sb1BF_nonneg (d := d) H.tr.hs0 H.tr.hC
  have hw3 := (sb1w_pos ((d : ℝ) + 3) y).le
  have e := sb1w_32 y
  have hC3 := H.C3nn
  set q := C3 * sb1w ((d : ℝ) + 3) y with hq
  have hq0 : 0 ≤ q := mul_nonneg hC3 hw3
  set G0 := ‖fderiv ℝ D.V 0‖ with hG0
  set BF := sb1BF d D.s C with hBFd
  have hG00 : 0 ≤ G0 := norm_nonneg _
  have hn := norm_nonneg y
  have h1 : |D.invβ * fderiv ℝ (ρ r) y (sb1e k) + ρ r y * (fderiv ℝ D.V y (sb1e k) + sb1F d D.s (ρ r) k y)| ≤
      |D.invβ| * q + q * (G0 + B * ‖y‖ + BF) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left a1 (abs_nonneg _)
    · rw [abs_mul]
      refine mul_le_mul a2 ?_ (abs_nonneg _) hq0
      exact (abs_add_le _ _).trans (by linarith)
  refine h1.trans ?_
  have : sb1CJ D B C C3 * sb1w ((d : ℝ) + 2) y = q * ((|D.invβ| + G0 + BF + B) * (1 + ‖y‖)) := by
    unfold sb1CJ
    rw [← e, hq]
    ring
  rw [this]
  have hν := abs_nonneg D.invβ
  nlinarith [mul_nonneg hq0 (mul_nonneg (add_nonneg (add_nonneg hν hG00) hBF) hn), mul_nonneg hq0 hB]

theorem Sb1Tr3.dJ_bound (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (k : Fin d) (y : Euc d) :
    |fderiv ℝ (sb1J D (ρ r) k) y (sb1e k)| ≤ sb1CdJ D B C C3 * sb1w ((d : ℝ) + 2) y := by
  have S := H.tr.slice r hr
  rw [sb1_fderiv_J H.tr.V H.tr.hd H.tr.hs0 H.tr.hsd S (H.pos r hr) k y, sb1_flux_deriv D H.tr.V H.tr.hd H.tr.hs0
    H.tr.hsd S k y]
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := H.ingr hr k y
  have hB := H.tr.V.B_nonneg
  have hBF := sb1BF_nonneg (d := d) H.tr.hs0 H.tr.hC
  have hw3 := (sb1w_pos ((d : ℝ) + 3) y).le
  have e := sb1w_32 y
  have hC3 := H.C3nn
  set q := C3 * sb1w ((d : ℝ) + 3) y with hq
  have hq0 : 0 ≤ q := mul_nonneg hC3 hw3
  set G0 := ‖fderiv ℝ D.V 0‖ with hG0
  set BF := sb1BF d D.s C with hBFd
  have hG00 : 0 ≤ G0 := norm_nonneg _
  have hn := norm_nonneg y
  have hν := abs_nonneg D.invβ
  have h1 : |D.invβ * fderiv ℝ (fun z => fderiv ℝ (ρ r) z (sb1e k)) y (sb1e k) +
      (fderiv ℝ (ρ r) y (sb1e k) * (fderiv ℝ D.V y (sb1e k) + sb1F d D.s (ρ r) k y) +
        ρ r y * (fderiv ℝ (fun z => fderiv ℝ D.V z (sb1e k)) y (sb1e k) +
          fderiv ℝ (sb1F d D.s (ρ r) k) y (sb1e k)))| ≤
      |D.invβ| * q + (q * (G0 + B * ‖y‖ + BF) + q * (B + BF)) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul_of_nonneg_left a5 (abs_nonneg _)
    · refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]
        refine mul_le_mul a1 ?_ (abs_nonneg _) hq0
        exact (abs_add_le _ _).trans (by linarith)
      · rw [abs_mul]
        refine mul_le_mul a2 ?_ (abs_nonneg _) hq0
        exact (abs_add_le _ _).trans (by linarith)
  refine h1.trans ?_
  have : sb1CdJ D B C C3 * sb1w ((d : ℝ) + 2) y = q * ((|D.invβ| + G0 + 2 * BF + 2 * B) * (1 + ‖y‖)) := by
    unfold sb1CdJ
    rw [← e, hq]
    ring
  rw [this]
  nlinarith [mul_nonneg hq0 (mul_nonneg (add_nonneg (add_nonneg hν hG00) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hBF)) hn),
    mul_nonneg hq0 hB, mul_nonneg hq0 (mul_nonneg hB hn), mul_nonneg hq0 hBF, mul_nonneg hq0 hν, mul_nonneg hq0 hG00]

theorem Sb1Tr3.A_bound (H : Sb1Tr3 D T C B C3 ρ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) (y : Euc d) :
    |sb1A D (ρ r) y| ≤ (d * sb1CdJ D B C C3) * sb1w ((d : ℝ) + 2) y := by
  rw [sb1_A_eq_sumJ H.tr.V H.tr.hd H.tr.hs0 H.tr.hsd (H.tr.slice r hr) (H.pos r hr) y]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k, |fderiv ℝ (sb1J D (ρ r) k) y (sb1e k)| ≤ ∑ _k : Fin d, sb1CdJ D B C C3 * sb1w ((d : ℝ) + 2) y :=
        Finset.sum_le_sum fun k _ => H.dJ_bound hr k y
    _ = (d * sb1CdJ D B C C3) * sb1w ((d : ℝ) + 2) y := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end HRS.MS.MfeConf
