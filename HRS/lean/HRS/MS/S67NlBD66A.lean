import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux3
import HRS.MS.S67NlBD14

/-!
# S6.7 nonlinear breakdown, packet 66A: uniform jets of the moving transport source alone

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4757-4770 area, nonlinear part of
`S:W:lem:r2mov-global-adjoint`. No owned definitions. Route: `mn_force_bound` (with the frozen
margin `d/2 + j + 2 < m`) gives `F ∈ C^{j+1}` with `cbNormVecE (j+1) F ≤ C0 ‖v‖_m ≤ C0 R0`; the
finite `cbNormVecE j ∇u` bounds every jet of `∇u`; the bilinear Leibniz bound for the inner product
and `∑ choose = 2^i` finish, with constant `C0 * 2^j`.
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

/-- a bound on `cbNormVecE K v` bounds every jet up to order `K` -/
lemma s67bd66_jet_le {K : ℕ} {v : Euc d → Euc d} {E : ℝ} (hE : 0 ≤ E)
    (h : cbNormVecE K v ≤ ENNReal.ofReal E) :
    ∀ k ≤ K, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ E := by
  intro k hk x
  unfold cbNormVecE at h
  have h1 : (⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ k v y‖) ≤
      ∑ j ∈ Finset.range (K + 1), ⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v y‖ :=
    Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v y‖)
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  have h2 : ENNReal.ofReal ‖iteratedFDeriv ℝ k v x‖ ≤ ENNReal.ofReal E :=
    (le_iSup (fun y : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ k v y‖) x).trans (h1.trans h)
  exact (ENNReal.ofReal_le_ofReal_iff hE).1 h2

theorem s67bd_transport_source_jets (H : Mov2dTh d s β q ρ₀)
    (j M m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M)
    (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R0 c0 : ℝ, 0 ≤ R0 → R0 ≤ 1 → 0 ≤ c0 →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ →
      ∀ r : ℝ, 0 ≤ r → ∀ u : Euc d → ℝ,
      ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) u → cbNormVecE j (fun x => gradient u x) < ⊤ →
      ContDiff ℝ (j : WithTop ℕ∞)
        (fun x => inner ℝ (s67bd_F d s ρ₀ (movV ρ₀ ρ r) x) (gradient u x)) ∧
      ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i
        (fun y => inner ℝ (s67bd_F d s ρ₀ (movV ρ₀ ρ r) y) (gradient u y)) x‖ ≤
          C * R0 * (cbNormVecE j (fun y => gradient u y)).toReal := by
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hmj : (d : ℝ) / 2 + j + 2 < m := by linarith
  obtain ⟨C0, hC0, hforce⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ₀ H.hρ j m hmj
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  refine ⟨C0 * 2 ^ j, by positivity, fun R0 c0 hR0 hR01 hc0 f0 ρ hcls r hr u hu hcb => ?_⟩
  set v : Euc d → ℝ := movV ρ₀ ρ r with hvdef
  have hρ0c : Continuous ρ₀ := hρsm.continuous
  have hcont : Continuous v := by
    show Continuous (fun x => (ρ r x - ρ₀ x) / Real.sqrt (ρ₀ x))
    refine ((hcls.regular r hr).sub hρ0c).div (hρ0c.sqrt) (fun x => ?_)
    exact (Real.sqrt_pos.2 (hρpos x)).ne'
  obtain ⟨hvmem, hvnorm⟩ := hcls.weighted r hr
  have hvR : oscNorm (m : ℝ) v ≤ R0 := by
    refine hvnorm.trans ?_
    have : Real.exp (-c0 * r) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith
  obtain ⟨-, -, hFc, -, hcbF⟩ := hforce v hcont hvmem
  have hosc : 0 ≤ oscNorm (m : ℝ) v := Real.sqrt_nonneg _
  have hE : 0 ≤ C0 * oscNorm (m : ℝ) v := mul_nonneg hC0 hosc
  have hFb : ∀ k ≤ j + 1, ∀ x, ‖iteratedFDeriv ℝ k (s67bd_F d s ρ₀ v) x‖ ≤ C0 * R0 := by
    intro k hk x
    have := s67bd66_jet_le (K := j + 1) (v := s67bd_F d s ρ₀ v) hE
      (le_trans le_self_add hcbF) k hk x
    exact this.trans (mul_le_mul_of_nonneg_left hvR hC0)
  have hFcd : ContDiff ℝ (j : WithTop ℕ∞) (s67bd_F d s ρ₀ v) :=
    (show ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (s67bd_F d s ρ₀ v) by exact_mod_cast hFc).of_le
      (by exact_mod_cast Nat.le_succ j)
  have hGc : ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient u x) := s67_grad_contDiff hu
  have hcbtop := hcb.ne
  have hGb : ∀ k ≤ j, ∀ x, ‖iteratedFDeriv ℝ k (fun y => gradient u y) x‖ ≤
      (cbNormVecE j (fun y => gradient u y)).toReal :=
    s67bd66_jet_le ENNReal.toReal_nonneg (by rw [ENNReal.ofReal_toReal hcbtop])
  refine ⟨hFcd.inner ℝ hGc, fun i hi x => ?_⟩
  have hfun : (fun y => inner ℝ (s67bd_F d s ρ₀ v y) (gradient u y)) =
      fun y => innerSL ℝ (s67bd_F d s ρ₀ v y) (gradient u y) := by
    funext y; simp
  rw [hfun]
  have hleib := (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    hFcd hGc x (n := i) (by exact_mod_cast hi) (norm_innerSL_le ℝ)
  set cb : ℝ := (cbNormVecE j (fun y => gradient u y)).toReal with hcbdef
  have hcb0 : 0 ≤ cb := ENNReal.toReal_nonneg
  have hR : 0 ≤ C0 * R0 * cb := by positivity
  refine hleib.trans ?_
  calc ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
        ‖iteratedFDeriv ℝ k (s67bd_F d s ρ₀ v) x‖ *
        ‖iteratedFDeriv ℝ (i - k) (fun y => gradient u y) x‖
      ≤ ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * (C0 * R0 * cb) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk' : k ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact mul_le_mul (hFb k (by omega) x) (hGb (i - k) (by omega) x) (norm_nonneg _)
          (mul_nonneg hC0 hR0)
    _ = 2 ^ i * (C0 * R0 * cb) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose i
    _ ≤ 2 ^ j * (C0 * R0 * cb) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) hR
    _ = C0 * 2 ^ j * R0 * cb := by ring

end HRS.MS.BreakdownS67
