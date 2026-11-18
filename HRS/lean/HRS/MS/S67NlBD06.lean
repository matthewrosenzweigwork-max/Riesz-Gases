import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovThermAux2
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD04
import HRS.MS.S67NlBD05

/-!
# S6.7nl.06: actual classical weighted `Σ²` membership and finite bound
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.

`ψ_r = √ρ₀ (f_r - m_r)` with the constant mean `m_r = ∫ f_r ρ₀`.  The classical bounds `hf.bdd` at
orders `0,1,2` are uniform on `[0,T]`; `mv0_sqrt_gauss_thermal` gives a common Gaussian rate for
`D^k √ρ₀`; the Leibniz bound gives one Gaussian envelope for `D^k ψ_r` (`k ≤ 2`), and packet 05
at `n = 2` returns membership and the finite bound.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Subtracting a constant changes only the order-zero jet, by at most `|m|`. -/
theorem s67bd_sig2_const_sub {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (m : ℝ) (k : ℕ) (hk : k ≤ 2)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => u y - m) x‖ ≤ ‖iteratedFDeriv ℝ k u x‖ + |m| := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [norm_iteratedFDeriv_zero, norm_iteratedFDeriv_zero]
    calc ‖u x - m‖ ≤ ‖u x‖ + ‖m‖ := norm_sub_le _ _
      _ = ‖u x‖ + |m| := by rw [Real.norm_eq_abs m]
  · have hcd : ContDiffAt ℝ (k : ℕ) u x :=
      (hu.of_le (by exact_mod_cast hk)).contDiffAt
    have hcc : ContDiffAt ℝ (k : ℕ) (fun _ : Euc d => m) x := contDiffAt_const
    have hsub : (fun y => u y - m) = u - fun _ : Euc d => m := rfl
    rw [hsub, iteratedFDeriv_sub_apply hcd hcc, iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, sub_zero]
    exact le_add_of_nonneg_right (abs_nonneg _)

/-- Leibniz bound through order two for a product with a Gaussian-bounded factor. -/
theorem s67bd_sig2_prod_jet {w g : Euc d → ℝ} (hw : ContDiff ℝ 2 w) (hg : ContDiff ℝ 2 g)
    {c Cw G : ℝ} (hCw : 0 ≤ Cw) (hG : 0 ≤ G)
    (hwb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k w x‖ ≤ Cw * Real.exp (-c * ‖x‖ ^ 2))
    (hgb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ G) (k : ℕ) (hk : k ≤ 2) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => w y * g y) x‖ ≤ 4 * Cw * G * Real.exp (-c * ‖x‖ ^ 2) := by
  have h1 := norm_iteratedFDeriv_mul_le hw hg x (n := k) (by exact_mod_cast hk)
  refine h1.trans ?_
  have hE := (Real.exp_pos (-c * ‖x‖ ^ 2)).le
  have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i w x‖ *
      ‖iteratedFDeriv ℝ (k - i) g x‖ ≤ (k.choose i : ℝ) * (Cw * G * Real.exp (-c * ‖x‖ ^ 2)) := by
    intro i hi
    have hik : i ≤ 2 := by have := Finset.mem_range.1 hi; omega
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖iteratedFDeriv ℝ i w x‖ * ‖iteratedFDeriv ℝ (k - i) g x‖
        ≤ (Cw * Real.exp (-c * ‖x‖ ^ 2)) * G :=
          mul_le_mul (hwb i hik x) (hgb (k - i) (by omega) x) (norm_nonneg _)
            (mul_nonneg hCw hE)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [← Finset.sum_mul, hsum]
  have hX : 0 ≤ Cw * G * Real.exp (-c * ‖x‖ ^ 2) := mul_nonneg (mul_nonneg hCw hG) hE
  have h2k : (2 : ℝ) ^ k ≤ 4 := by
    interval_cases k <;> norm_num
  calc (2 : ℝ) ^ k * (Cw * G * Real.exp (-c * ‖x‖ ^ 2))
      ≤ 4 * (Cw * G * Real.exp (-c * ‖x‖ ^ 2)) := mul_le_mul_of_nonneg_right h2k hX
    _ = _ := by ring

theorem s67bd_classical_sigma2 (H : Mov2dTh d s β q ρ₀)
    (ρ : ℝ → Euc d → ℝ) (T : ℝ) (φ : Euc d → ℝ)
    (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc (0 : ℝ) T,
      MemOsc 2 (s67psi ρ₀ (f r)) ∧ oscNorm 2 (s67psi ρ₀ (f r)) ≤ B ∧
      ContDiff ℝ 2 (s67psi ρ₀ (f r)) ∧
      ∀ i : Fin d, MemLp (s67bd_D i (s67psi ρ₀ (f r))) 2 volume := by
  obtain ⟨hws, -, c, hc, hk⟩ :=
    HRS.MS.Mov0.mv0_sqrt_gauss_thermal H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨Bq, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨C0, h0⟩ := hk 0
  obtain ⟨C1, h1⟩ := hk 1
  obtain ⟨C2, h2⟩ := hk 2
  obtain ⟨Cw, hCw0, hCw⟩ : ∃ Cw : ℝ, 0 ≤ Cw ∧ |C0| ≤ Cw ∧ |C1| ≤ Cw ∧ |C2| ≤ Cw :=
    ⟨|C0| + |C1| + |C2|, by positivity, by linarith [abs_nonneg C1, abs_nonneg C2],
      by linarith [abs_nonneg C0, abs_nonneg C2], by linarith [abs_nonneg C0, abs_nonneg C1]⟩
  have hwb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ₀ y)) x‖ ≤
      Cw * Real.exp (-c * ‖x‖ ^ 2) := by
    intro k hk x
    have hE := (Real.exp_pos (-c * ‖x‖ ^ 2)).le
    interval_cases k
    · exact (h0 x).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCw.1) hE)
    · exact (h1 x).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCw.2.1) hE)
    · exact (h2 x).trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans hCw.2.2) hE)
  have hw2 : ContDiff ℝ 2 (fun y => Real.sqrt (ρ₀ y)) := hws.of_le (by simp)
  -- `ρ₀` is integrable
  have hρnn : ∀ x, 0 ≤ ρ₀ x := fun x => (hR.pos x).le
  have hρint : Integrable ρ₀ volume := by
    refine Integrable.mono' ((s67bd_poly_gauss_integrable d 0 (c := 2 * c)
      (by linarith)).const_mul (Cw ^ 2)) hR.smooth.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    have hs := hwb 0 (by norm_num) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hs
    have hsq : ρ₀ x = Real.sqrt (ρ₀ x) ^ 2 := (Real.sq_sqrt (hρnn x)).symm
    have hE2 : Real.exp (-c * ‖x‖ ^ 2) ^ 2 = Real.exp (-(2 * c) * ‖x‖ ^ 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [Real.norm_of_nonneg (hρnn x), hsq, pow_zero, one_mul, ← hE2, ← mul_pow]
    have hb0 : 0 ≤ Cw * Real.exp (-c * ‖x‖ ^ 2) := mul_nonneg hCw0 (Real.exp_pos _).le
    have ha0 : 0 ≤ Real.sqrt (ρ₀ x) := Real.sqrt_nonneg _
    exact sq_le_sq' (by linarith) (le_trans (le_abs_self _) hs)
  set P : ℝ := ∫ y, ρ₀ y with hP
  have hP0 : 0 ≤ P := integral_nonneg hρnn
  -- classical bounds, uniform on the horizon
  obtain ⟨B0, hB0⟩ := hf.bdd 0 (by norm_num)
  obtain ⟨B1, hB1⟩ := hf.bdd 1 (by norm_num)
  obtain ⟨B2, hB2⟩ := hf.bdd 2 (by norm_num)
  set Ff : ℝ := |B0| + |B1| + |B2| with hFf
  have hFf0 : 0 ≤ Ff := by positivity
  have hfb : ∀ r ∈ Icc (0 : ℝ) T, ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (f r) x‖ ≤ Ff := by
    intro r hr k hk x
    interval_cases k
    · exact (hB0 r hr x).trans ((le_abs_self _).trans (by linarith [abs_nonneg B1, abs_nonneg B2]))
    · exact (hB1 r hr x).trans ((le_abs_self _).trans (by linarith [abs_nonneg B0, abs_nonneg B2]))
    · exact (hB2 r hr x).trans ((le_abs_self _).trans (by linarith [abs_nonneg B0, abs_nonneg B1]))
  set Gb : ℝ := Ff + Ff * P with hGb
  have hGb0 : 0 ≤ Gb := by positivity
  set A : ℝ := 4 * Cw * Gb with hA
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨C, hC0, hC⟩ := s67bd_gaussian_osc d 2 c hc
  obtain ⟨CL, -, hCL⟩ := s67bd_gaussian_L2 d 0 c hc
  refine ⟨C * A, mul_nonneg hC0 hA0, fun r hr => ?_⟩
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = ∫ y, f r y * ρ₀ y := ⟨_, rfl⟩
  have hm : |m| ≤ Ff * P := by
    rw [hmdef, ← Real.norm_eq_abs]
    have hb : ‖∫ y, f r y * ρ₀ y‖ ≤ ∫ y, Ff * ρ₀ y := by
      refine norm_integral_le_of_norm_le (hρint.const_mul Ff) (ae_of_all _ fun y => ?_)
      rw [norm_mul, Real.norm_of_nonneg (hρnn y)]
      have := hfb r hr 0 (by norm_num) y
      rw [norm_iteratedFDeriv_zero] at this
      exact mul_le_mul_of_nonneg_right this (hρnn y)
    rwa [integral_const_mul] at hb
  have hfc : ContDiff ℝ 2 (f r) := hf.c2 r hr
  have hgcd : ContDiff ℝ 2 (fun y => f r y - m) := hfc.sub contDiff_const
  have hgb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (fun y => f r y - m) x‖ ≤ Gb := by
    intro k hk x
    exact (s67bd_sig2_const_sub hfc m k hk x).trans (by linarith [hfb r hr k hk x])
  have hψdef : s67psi ρ₀ (f r) = fun x => Real.sqrt (ρ₀ x) * (f r x - m) := by
    funext x; rw [hmdef]; rfl
  have hψcd : ContDiff ℝ 2 (s67psi ρ₀ (f r)) := by
    rw [hψdef]; exact hw2.mul hgcd
  have hψb : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k (s67psi ρ₀ (f r)) x‖ ≤
      A * Real.exp (-c * ‖x‖ ^ 2) := by
    intro k hk x
    rw [hψdef]
    exact s67bd_sig2_prod_jet hw2 hgcd hCw0 hGb0 hwb hgb k hk x
  obtain ⟨hmo, hno⟩ := hC A hA0 (s67psi ρ₀ (f r)) (by exact_mod_cast hψcd)
    (fun k hk x => hψb k (by exact_mod_cast hk) x)
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  rw [e2] at hmo hno
  refine ⟨hmo, hno, hψcd, fun i => ?_⟩
  have hdc : Continuous (fun x => s67bd_D i (s67psi ρ₀ (f r)) x) :=
    (hψcd.continuous_fderiv (by simp)).clm_apply continuous_const
  refine (hCL A hA0 _ hdc.aestronglyMeasurable (fun x => ?_)).1
  have h1' := hψb 1 (by norm_num) x
  rw [norm_iteratedFDeriv_one] at h1'
  have hop := (fderiv ℝ (s67psi ρ₀ (f r)) x).le_opNorm (EuclideanSpace.single i (1 : ℝ))
  rw [Real.norm_eq_abs] at hop
  simp only [s67bd_D, pow_zero, mul_one]
  have hn1 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [hn1, mul_one] at hop
  exact hop.trans h1'

end HRS.MS.BreakdownS67
