import HRS.MS.R2WinOrbTRB5
import HRS.MS.R2WinOrbNLAux22

/-!
# S10.3 packet [A], part 1: the gradient estimate at a high jet order and bounded jets of the adjoint solutions

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `S103cGrad d s a β ρβ ρ k M Cg cg`: the gradient estimate of S6.7 (jet order `k`, oscillator index `M`) along the trajectory `ρ`
  (the shape of `S103nGrad`, with free orders).
* `s103c_radius`: for every `k` there are `R*, Cg, cg` such that every trajectory of the small class of radius `r ≤ R*` has `S103cGrad ρ k (k+d+6) Cg cg`
  (`s67bd_uniform_gradient`).  The radius is imposed through the `Rs` argument of `s103n_setup2`, so the constants of the orbit claims
  (`s103n_orbits_nonlinear`) and of the higher-order estimate come from one common `ε_*`.
* `s103c_jets_of_bd`: a classical adjoint solution whose terminal datum has bounded jets `Bd (k+d+6) A` has all slices in `C^{k+1}` with jets of
  order `1..k+1` bounded by `C A` (uniformly in the horizon).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Ul HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.Who HRS.MS.BreakdownS67
  HRS.MS.MovAdj HRS.MS.R2WinOrb

variable {d : ℕ}

/-- The gradient estimate of S6.7 with jet order `k` and oscillator index `M` along a fixed trajectory `ρ`. -/
def S103cGrad (d : ℕ) (s a β : ℝ) (ρβ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (k M : ℕ) (Cg cg : ℝ) : Prop :=
  ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ T →
    IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) T φ f →
    ContDiff ℝ ((k : ℕ) + 1) φ → MemOsc (M : ℝ) (s67psi ρβ φ) →
    ∀ r' ∈ Icc (0 : ℝ) T,
      ContDiff ℝ (k : ℕ) (fun x => gradient (f r') x) ∧
      cbNormVecE k (fun x => gradient (f r') x) ≤
        ENNReal.ofReal (Cg * Real.exp (-cg * (T - r'))) *
          (cbNormVecE k (fun x => gradient φ x) + ENNReal.ofReal (oscNorm (M : ℝ) (s67psi ρβ φ)))

theorem s103c_radius {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (k : ℕ) (hk : k ≤ 100 * d + 1000) :
    ∃ Rstar Cg cg : ℝ, 0 < Rstar ∧ 1 ≤ Cg ∧ 0 < cg ∧ ∀ (r c₁ : ℝ), 0 ≤ r → r ≤ Rstar → 0 ≤ c₁ →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
        MovInSmallClass d s a β ρβ (102 * d + 1020) r c₁ f0 ρ → S103cGrad d s a β ρβ ρ k (k + d + 6) Cg cg := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hM : (d : ℝ) / 2 + k + 5 < ((k + d + 6 : ℕ) : ℝ) := by push_cast; linarith
  have hj' : 1 ≤ 100 * d + 1000 := by omega
  have hm : (d : ℝ) / 2 + ((100 * d + 1000 : ℕ) : ℝ) + 6 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast; linarith
  have hmM : ((k + d + 6 : ℕ) : ℝ) + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by
    have : (k : ℝ) ≤ 100 * d + 1000 := by exact_mod_cast hk
    push_cast; linarith
  obtain ⟨Rstar, Cg, cg, hR, hCg, hcg, hb⟩ :=
    s67bd_uniform_gradient H k (k + d + 6) hM (100 * d + 1000) (102 * d + 1020) hj' hm hmM
  refine ⟨Rstar, Cg, cg, hR, hCg, hcg, fun r c₁ hr hrR hc f0 ρ hρ T φ f hT hf hφ hosc r' hr' => ?_⟩
  exact hb r c₁ hr hrR hc f0 ρ hρ T φ f hT hf hφ hosc r' hr'

theorem s103c_jets_of_cb {w : Euc d → ℝ} {k : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hw : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) w)
    (h : cbNormVecE k (fun x => gradient w x) ≤ ENNReal.ofReal B) :
    ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x, ‖iteratedFDeriv ℝ i w x‖ ≤ B := by
  intro i hi1 hik x
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hj : j ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
  have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun y => gradient w y) x‖ ≤ cbNormVecE k (fun x => gradient w x) := by
    unfold cbNormVecE
    exact (le_iSup (fun x : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun y => gradient w y) x‖) x).trans
      (Finset.single_le_sum (f := fun j => ⨆ x : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j (fun y => gradient w y) x‖)
        (fun _ _ => zero_le') hj)
  have h2 := (ENNReal.ofReal_le_ofReal_iff hB).1 (h1.trans h)
  rwa [s67_norm_iter_grad (hw.of_le (by exact_mod_cast (by omega : j + 1 ≤ k + 1))) x] at h2

theorem s103c_jets_of_bd {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (k : ℕ) {Cg cg : ℝ}
    (hCg : 0 ≤ Cg) (hcg : 0 < cg) (hk : 1 ≤ k) :
    ∃ G0 : ℝ, 0 ≤ G0 ∧ ∀ (ρ : ℝ → Euc d → ℝ), S103cGrad d s a β ρβ ρ k (k + d + 6) Cg cg →
      ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (A : ℝ), 0 ≤ T → Bd (k + d + 6) A φ →
        IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) T φ f →
        ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (f r) ∧
          ∀ i, 1 ≤ i → i ≤ k + 1 → ∀ x, ‖iteratedFDeriv ℝ i (f r) x‖ ≤ G0 * A := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := s103n_psi_of_jets H (k + d + 6)
  refine ⟨Cg * (((k : ℝ) + 1) + Cψ), by positivity, fun ρ hG T φ f A hT hφ hf r hr => ?_⟩
  have hA := hφ.nonneg
  have hφk : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) φ :=
    hφ.1.of_le (by exact_mod_cast (by omega : k + 1 ≤ k + d + 6))
  have hcb := s103n_cb_of_jets (n := k) hφk (E := A)
    (fun l hl x => hφ.2 l (by omega) x)
  obtain ⟨hm1, hm2⟩ := hCψ A φ hφ
  obtain ⟨hg1, hg2⟩ := hG T φ f hT hf hφk hm1 r hr
  have hdiff : Differentiable ℝ (f r) := (hf.c2 r hr).differentiable (by norm_num)
  have hfr : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (f r) :=
    HRS.MS.R2WinOrb.s103_fderiv_contDiff hdiff hg1
  refine ⟨hfr, ?_⟩
  have hexle : Real.exp (-cg * (T - r)) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ T - r := sub_nonneg.2 hr.2
    nlinarith
  have hB : 0 ≤ Cg * (((k : ℝ) + 1) + Cψ) * A := by positivity
  refine s103c_jets_of_cb hB hfr (hg2.trans ?_)
  have hsum : cbNormVecE k (fun x => gradient φ x) + ENNReal.ofReal (oscNorm ((k + d + 6 : ℕ) : ℝ) (s67psi ρβ φ)) ≤
      ENNReal.ofReal (((k : ℝ) + 1) * A + Cψ * A) := by
    calc _ ≤ ENNReal.ofReal (((k : ℝ) + 1) * A) + ENNReal.ofReal (Cψ * A) := by
          refine add_le_add ?_ (ENNReal.ofReal_le_ofReal hm2)
          have := hcb
          convert this using 3
      _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  calc ENNReal.ofReal (Cg * Real.exp (-cg * (T - r))) * (cbNormVecE k (fun x => gradient φ x) +
        ENNReal.ofReal (oscNorm ((k + d + 6 : ℕ) : ℝ) (s67psi ρβ φ)))
      ≤ ENNReal.ofReal (Cg * 1) * ENNReal.ofReal (((k : ℝ) + 1) * A + Cψ * A) := by
        gcongr
    _ = ENNReal.ofReal (Cg * (((k : ℝ) + 1) + Cψ) * A) := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

/-- The datum class: `C^N`, jets bounded by `A`, and the derivatives of order `≥ 1` decay like `(1+‖x‖)⁻²`. -/
def DatD (N : ℕ) (A : ℝ) (ψ : Euc d → ℝ) : Prop :=
  ContDiff ℝ (N : WithTop ℕ∞) ψ ∧ (∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ ≤ A) ∧
    ∀ j, 1 ≤ j → j ≤ N → ∀ x, ‖iteratedFDeriv ℝ j ψ x‖ * (1 + ‖x‖) ^ 2 ≤ A

theorem DatD.nonneg {N : ℕ} {A : ℝ} {ψ : Euc d → ℝ} (h : DatD N A ψ) : 0 ≤ A :=
  (norm_nonneg _).trans (h.2.1 0 (Nat.zero_le _) 0)

theorem DatD.bd {N : ℕ} {A : ℝ} {ψ : Euc d → ℝ} (h : DatD N A ψ) : Bd N A ψ := ⟨h.1, h.2.1⟩

theorem DatD.mono_N {N N' : ℕ} (hN : N' ≤ N) {A : ℝ} {ψ : Euc d → ℝ} (h : DatD N A ψ) : DatD N' A ψ :=
  ⟨h.1.of_le (by exact_mod_cast hN), fun j hj => h.2.1 j (hj.trans hN), fun j h1 hj => h.2.2 j h1 (hj.trans hN)⟩

theorem DatD.mono_A {N : ℕ} {A A' : ℝ} (hA : A ≤ A') {ψ : Euc d → ℝ} (h : DatD N A ψ) : DatD N A' ψ :=
  ⟨h.1, fun j hj x => (h.2.1 j hj x).trans hA, fun j h1 hj x => (h.2.2 j h1 hj x).trans hA⟩

/-- The decay `(1+‖x‖)⁻¹` of the derivatives (the form used by `s103b_weighted_decay`). -/
theorem DatD.decay1 {N : ℕ} {A : ℝ} {ψ : Euc d → ℝ} (h : DatD N A ψ) :
    ∀ i, 1 ≤ i → i ≤ N → ∀ y, ‖iteratedFDeriv ℝ i ψ y‖ ≤ A * (1 + ‖y‖)⁻¹ := by
  intro i hi1 hiN y
  have hx : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have h2 := h.2.2 i hi1 hiN y
  rw [← div_eq_mul_inv, le_div_iff₀ hx]
  have h3 : 1 + ‖y‖ ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
  calc ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖) ≤ ‖iteratedFDeriv ℝ i ψ y‖ * (1 + ‖y‖) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ A := h2

theorem s103c_phi_dat (n : ℕ) (hn : n ≤ 10 * d + 100) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α : MultiIndex d, DatD n (K * s103_b d α) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) := by
  have hj : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
      (1 + ‖x‖) ^ 2 * ‖iteratedFDeriv ℝ j f x‖ ≤ C * oscNorm ((2 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f :=
    fun j => HRS.MS.R2WinOrb.s103_weighted 2 j
  choose C hC0 hC using hj
  refine ⟨∑ j ∈ Finset.range (n + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun α => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun ((24 * d + 240 : ℕ) : ℝ) α := by
    have hmem : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α ∈ mo_Hspan d := by
      have : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α =
          (oscEigenvalue d α ^ (-(((24 * d + 240 : ℕ) : ℝ) / 2))) • hermiteFunD α := by
        funext x; simp [oscTestFun]
      rw [this]
      exact Submodule.smul_mem _ _ (mova3_hermite_mem α)
    exact mova3c_hspan_schwartz hmem
  rw [← hf]
  have hb0 := s103_b_nonneg (d := d) α
  have hK0 : 0 ≤ ∑ j ∈ Finset.range (n + 1), C j := Finset.sum_nonneg fun j _ => hC0 j
  -- the key bound for every `j ≤ n`
  have key : ∀ j ≤ n, ∀ x, (1 + ‖x‖) ^ 2 * ‖iteratedFDeriv ℝ j f x‖ ≤
      (∑ j ∈ Finset.range (n + 1), C j) * s103_b d α := by
    intro j hjn x
    refine (hC j f x).trans ?_
    have hjm : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
    have hle : C j ≤ ∑ j ∈ Finset.range (n + 1), C j :=
      Finset.single_le_sum (f := C) (fun i _ => hC0 i) hjm
    have hosc : oscNorm ((2 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤ s103_b d α := by
      rw [hf, HRS.MS.R2WinOrb.s103_oscNorm_test]
      unfold s103_b
      refine Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) ?_
      have hfl : (⌊(j : ℝ) + (d : ℝ) / 2⌋₊ : ℝ) ≤ (j : ℝ) + (d : ℝ) / 2 := Nat.floor_le (by positivity)
      have hjn' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
      have hn' : (n : ℝ) ≤ 10 * (d : ℝ) + 100 := by exact_mod_cast hn
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      push_cast
      linarith
    have hoscnn : 0 ≤ oscNorm ((2 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f := Real.sqrt_nonneg _
    calc C j * oscNorm ((2 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤
        C j * s103_b d α := mul_le_mul_of_nonneg_left hosc (hC0 j)
      _ ≤ _ := mul_le_mul_of_nonneg_right hle hb0
  refine ⟨(f.smooth _).of_le (s103_cast_le_infty _), fun j hj x => ?_, fun j _ hj x => ?_⟩
  · refine le_trans ?_ (key j hj x)
    have : 1 ≤ (1 + ‖x‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg x])
    nlinarith [norm_nonneg (iteratedFDeriv ℝ j f x)]
  · have := key j hj x
    linarith [mul_comm ((1 + ‖x‖) ^ 2) ‖iteratedFDeriv ℝ j f x‖]

end HRS.MS.R2WinOrbNL

end
