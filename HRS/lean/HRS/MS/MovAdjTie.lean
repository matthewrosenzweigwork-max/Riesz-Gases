import HRS.MS.MovAdjAux25
import HRS.Whole.MovingDyn

/-!
# S6.7 (stationary case): tie `mov_global_adjoint_stationary_proof`

Namespace `HRS.MS.MovAdj`.  Assembly of the packets `MovAdjAux1..25`:
spectral decay of `ψ_r` (`s67_spectral`), the bound of `J f_r` (`s67_J_bound`), the Duhamel formula and the derivative bound for
`f_r` (`s67_core`), and the `cbNormVecE` bookkeeping (`s67_cb_fin`, `s67_cb_le`).  The nonlinear row
`mov_global_adjoint_nonlinear` is NOT proved here (see `MovAdjAux1` for the plan).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.PoisKolm HRS.MS.PoisHigh HRS.MS.Mov63 HRS.MS.FlowB HRS.MS.PoisSg HRS.MS.PoisFlow
  HRS.MS.PoisMax

set_option maxHeartbeats 3200000 in
theorem mov_global_adjoint_stationary_proof :
    type_of% @HRS.Whole.mov_global_adjoint_stationary := by
  intro d s hd hs0 hsd β q hβ hq ρ₀ hρ j M hM
  have H : Mov2dTh d s β q ρ₀ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  obtain ⟨cs, hcs, hspec⟩ := s67_spectral hd hs0 hsd β q hβ hq ρ₀ hρ
  have hMA : movA d s ≤ (M : ℝ) := by
    have h0 : (0 : ℝ) ≤ (d : ℝ) / 2 + j := by positivity
    unfold movA
    refine max_le (by linarith) (by linarith)
  obtain ⟨Csp, hCsp0, hCsp⟩ := hspec (M : ℝ) hMA
  obtain ⟨KJ, hKJ0, hKJ⟩ := s67_J_bound H j M hM
  obtain ⟨B, hBeq, hR, hcbB⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  obtain ⟨-, hgrad, -⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq' hR
  obtain ⟨Mb, hBm⟩ := hcbB (max 2 (j + 1))
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (hBm.2 0 (Nat.zero_le _) 0)
  obtain ⟨Ω, mΩ, P, hP, ℱ, W, hW⟩ := exists_isBrownianFiltration_type (Fin d)
  obtain ⟨Csg, Cd, hCsg0, hCd0, hcore⟩ := s67_core hd hs0 hsd hq hβ hρ hgrad j M (mp := max 2 (j + 1))
    rfl hBm hMb hW hcs hCsp0 hKJ0 hKJ hCsp
  have hc0pos : 0 < pm_c0 (β * q) Mb := by
    unfold pm_c0 pm_kappa
    exact mul_pos (Real.exp_pos _) (lt_min zero_lt_one (by positivity))
  set μ := min (pm_c0 (β * q) Mb) (cs * β) with hμ
  have hμpos : 0 < μ := lt_min hc0pos (mul_pos hcs hβ)
  set m1 := max Csg (Cd * (β * KJ * Csp)) with hm1
  have hm10 : 0 ≤ m1 := hCsg0.trans (le_max_left _ _)
  set C := max 1 (((j : ℝ) + 1) * m1) with hC
  have hC1 : 1 ≤ C := le_max_left _ _
  refine ⟨C, μ / (2 * β), by positivity, ?_⟩
  intro t φ f ht hf hφ hosc r hr
  have hosc' : MemOsc (M : ℝ) (s67psi ρ₀ φ) := hosc
  have hNeq : (fun x => Real.sqrt (ρ₀ x) * (φ x - ∫ y, φ y * ρ₀ y)) = s67psi ρ₀ φ := rfl
  rw [hNeq]
  have hφ' : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) φ := by exact_mod_cast hφ
  set N := oscNorm (M : ℝ) (s67psi ρ₀ φ) with hN
  have hN0 : 0 ≤ N := Real.sqrt_nonneg _
  have hfr : ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) (f r) :=
    (hKJ (f r) (hf.isC12TestRd.memCb hr) ((hCsp t φ f ht hf hosc' r hr).1)).1
  have hgr : ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient (f r) x) :=
    s67_grad_contDiff (hfr.of_le (s67_cast_le (by omega : j + 1 ≤ j + 4)))
  refine ⟨hgr, ?_⟩
  by_cases htop : cbNormVecE j (fun x => gradient φ x) = ⊤
  · have hne : ENNReal.ofReal (C * Real.exp (-(μ / (2 * β)) * (t - r))) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    rw [htop, top_add, ENNReal.mul_top hne]
    exact le_top
  rcases eq_or_lt_of_le hr.2 with hrt | hrt
  · -- `r = t`
    subst hrt
    rw [hf.terminal]
    rw [sub_self, mul_zero, Real.exp_zero, mul_one]
    have h1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal C := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hC1
    calc cbNormVecE j (fun x => gradient φ x) = 1 * cbNormVecE j (fun x => gradient φ x) :=
          (one_mul _).symm
      _ ≤ ENNReal.ofReal C * cbNormVecE j (fun x => gradient φ x) := by gcongr
      _ ≤ ENNReal.ofReal C * (cbNormVecE j (fun x => gradient φ x) + ENNReal.ofReal N) := by
          gcongr; exact le_self_add
  · have htpos : 0 < t := hr.1.trans_lt hrt
    obtain ⟨Y, hY0, hYb, hYeq⟩ := s67_cb_fin htop
    have hYφ : ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ (i + 1) φ x‖ ≤ Y i := by
      intro i hi x
      have := hYb i hi x
      rwa [s67_norm_iter_grad (hφ'.of_le (s67_cast_le (by omega : i + 1 ≤ j + 1))) x] at this
    obtain ⟨-, hbound⟩ := hcore t φ f htpos hf hφ' hosc' r hr hrt Y hY0 hYφ
    set SY := ∑ i ∈ Finset.range (j + 1), Y i with hSY
    have hSY0 : 0 ≤ SY := Finset.sum_nonneg fun i _ => hY0 i
    set E := (Csg * SY + Cd * (β * KJ * Csp * N)) *
      Real.exp (-(μ / 2) * ((t - r) / β)) with hE
    have hcb : cbNormVecE j (fun x => gradient (f r) x) ≤ ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), E) := by
      refine s67_cb_le fun i hi x => ?_
      rw [s67_norm_iter_grad (hfr.of_le (s67_cast_le (by omega : i + 1 ≤ j + 4))) x]
      exact hbound (i + 1) (by omega) (by omega) x
    refine hcb.trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, hYeq,
      ← ENNReal.ofReal_add hSY0 hN0]
    have hex : 0 ≤ C * Real.exp (-(μ / (2 * β)) * (t - r)) := by positivity
    rw [← ENNReal.ofReal_mul hex]
    refine ENNReal.ofReal_le_ofReal ?_
    have he : Real.exp (-(μ / 2) * ((t - r) / β)) = Real.exp (-(μ / (2 * β)) * (t - r)) := by
      congr 1; field_simp
    have hexp0 : 0 ≤ Real.exp (-(μ / (2 * β)) * (t - r)) := (Real.exp_pos _).le
    have h1 : Csg * SY + Cd * (β * KJ * Csp * N) ≤ m1 * SY + m1 * N := by
      have a1 : Csg * SY ≤ m1 * SY := mul_le_mul_of_nonneg_right (le_max_left _ _) hSY0
      have a2 : Cd * (β * KJ * Csp * N) = (Cd * (β * KJ * Csp)) * N := by ring
      have a3 : (Cd * (β * KJ * Csp)) * N ≤ m1 * N := mul_le_mul_of_nonneg_right (le_max_right _ _) hN0
      linarith
    have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
    have hKC : ((j : ℝ) + 1) * m1 ≤ C := le_max_right _ _
    calc ((j : ℝ) + 1) * E = ((j : ℝ) + 1) * (Csg * SY + Cd * (β * KJ * Csp * N)) *
          Real.exp (-(μ / (2 * β)) * (t - r)) := by rw [hE, he]; ring
      _ ≤ ((j : ℝ) + 1) * (m1 * SY + m1 * N) * Real.exp (-(μ / (2 * β)) * (t - r)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hj0) hexp0
      _ = ((j : ℝ) + 1) * m1 * (SY + N) * Real.exp (-(μ / (2 * β)) * (t - r)) := by ring
      _ ≤ C * (SY + N) * Real.exp (-(μ / (2 * β)) * (t - r)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC (by positivity)) hexp0
      _ = C * Real.exp (-(μ / (2 * β)) * (t - r)) * (SY + N) := by ring

end HRS.MS.MovAdj

