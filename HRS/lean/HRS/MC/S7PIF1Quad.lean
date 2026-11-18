import HRS.MC.S7PIF1Qc

/-!
# Packet piF1 (F2): the quadratic field evaluated on a smooth test function

`s7_PIF_quad_eval_proof`: `eval (ℬ̃_N) ψ = - N · flucInteraction D ψ x ρ`.  Route: `ℬ̃_N = ofSeq (N F^{h_{e_k}})`
(`quadFieldTilde`), `eval = ∑_k N F^{h_{e_k}} ψ̂_k`, the termwise expansion `F^{h_ψ} = ∑_k ψ̂_k F^{h_{e_k}}`
(`S7PIF1_modEnergy_hasSum` with `h_ψ = ∑ ψ̂_k h_{e_k}`, `S7PIF1_hT_hasSum`) and `flucInteraction = - F^{h_ψ}`
(`S7PIF1_fluc_eq`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF1

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

variable {d : ℕ}

theorem S7PIF1_coeff_summable {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    Summable fun k : NonzeroLattice d => |Torus.funRealCoeff ψ k| * Lattice.jp k.1 := by
  have hU : MemSobolev (((d + 3 : ℕ) : ℝ)) ψ := PDE.MFSemigroup.memSobolev_of_isSmooth hψ _
  have := S7PIDE.S7PIDE_coeff_summable hU 1 (by push_cast; linarith)
  simpa [Real.rpow_one] using this

/-- `modulatedEnergy` is homogeneous in the kernel. -/
theorem S7PIF1_modEnergy_const_mul {N : ℕ} (c : ℝ) (h : Torus d → Torus d → ℝ) (X : Config d N)
    (μ : Measure (Torus d)) :
    modulatedEnergy (fun x y => c * h x y) X μ = c * modulatedEnergy h X μ := by
  unfold modulatedEnergy
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

/-- **F2** (statement of `HRS.MC.Sec7.PIPlan.s7_PIF_quad_eval`, copied verbatim). -/
theorem s7_PIF_quad_eval_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) {N : ℕ} (hN : 1 ≤ N)
    (ρ : Torus d → ℝ) (hρ : Torus.IsSmooth ρ) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ) (x : Config d N)
    (hx : Function.Injective x) :
    NegSobolev.eval (quadFieldTilde m R.D.s (withDensityReal ρ) x) ψ = -(N : ℝ) * flucInteraction R.D ψ x ρ := by
  have hN0 : 0 < N := hN
  have hd : 2 ≤ d := R.hd
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ R.D.s := R.D.hs0
  have hsd : R.D.s < d := R.D.hsd
  have hs1 : R.D.s + 1 < d := by have := R.hs; linarith
  obtain ⟨C, hGood⟩ := HRS.KernelGrad.goodKernel_periodicRieszGrad hd hs0 hsd
  have hG : Integrable (periodicRieszGrad d R.D.s) := hGood.integrable_G hs1
  have hρ1 : Torus.IsCk 1 ρ := ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift ρ) from hρ)
    (by exact_mod_cast le_top)
  obtain ⟨B, hB0, hBabs⟩ := HRS.KernelGrad.isCk_bounded hρ1
  have hB : ∀ y, ρ y ≤ B := fun y => (le_abs_self _).trans (hBabs y)
  -- the series
  set a : NonzeroLattice d → ℝ := fun k => Torus.funRealCoeff ψ k with ha
  set c1 : ℝ := 2 * Real.sqrt 2 * d with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hjp := fun k : NonzeroLattice d => Torus.jp_pos k.1
  set w : NonzeroLattice d → ℝ := fun k => c1 * (|a k| * Lattice.jp k.1) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => mul_nonneg hc10 (mul_nonneg (abs_nonneg _) (hjp k).le)
  have hws : Summable w := (S7PIF1_coeff_summable hψ).mul_left c1
  set u : NonzeroLattice d → Torus d → Torus d → ℝ :=
    fun k x y => a k * hTransport d R.D.s (Torus.realMode k) x y with hu
  have hum : ∀ k, Measurable (fun p : Torus d × Torus d => u k p.1 p.2) := fun k =>
    (HRS.LocalDivAux.measurable_hTransport hsd (HRS.FieldSingAux.isSmooth_realMode k)).const_mul (a k)
  have hub : ∀ k x y, |u k x y| ≤ w k * ‖periodicRieszGrad d R.D.s (x - y)‖ := by
    intro k x y
    simp only [hu, abs_mul]
    calc |a k| * |hTransport d R.D.s (Torus.realMode k) x y|
        ≤ |a k| * (c1 * Lattice.jp k.1 * ‖periodicRieszGrad d R.D.s (x - y)‖) :=
          mul_le_mul_of_nonneg_left (S7PIF1_hT_mode_bound R.D.s k x y) (abs_nonneg _)
      _ = _ := by simp only [hw]; ring
  have hUs := S7PIF1_hT_hasSum R.D.s hψ
  have hbU : ∀ x y, |hTransport d R.D.s ψ x y| ≤ (∑' k, w k) * ‖periodicRieszGrad d R.D.s (x - y)‖ := by
    intro x y
    have h1 : HasSum (fun k => w k * ‖periodicRieszGrad d R.D.s (x - y)‖)
        ((∑' k, w k) * ‖periodicRieszGrad d R.D.s (x - y)‖) := hws.hasSum.mul_right _
    have := tsum_of_norm_bounded h1 (f := fun k => u k x y) (fun k => by
      rw [Real.norm_eq_abs]; exact hub k x y)
    rwa [(hUs x y).tsum_eq, Real.norm_eq_abs] at this
  have hsum := S7PIF1_modEnergy_hasSum hB hB0 hG u (hTransport d R.D.s ψ) w hw0 hws hum hub hUs x
  have hlin : ∀ k, modulatedEnergy (u k) x (withDensityReal ρ)
      = a k * modulatedEnergy (hTransport d R.D.s (Torus.realMode k)) x (withDensityReal ρ) :=
    fun k => S7PIF1_modEnergy_const_mul (a k) _ x _
  -- the coefficients of the quadratic field
  set F : NonzeroLattice d → ℝ := fun k =>
    modulatedEnergy (hTransport d R.D.s (Torus.realMode k)) x (withDensityReal ρ) with hF
  set cc : NonzeroLattice d → ℝ := fun k => (N : ℝ) * F k with hcc
  have hFb : ∀ k, |F k| ≤ (c1 * Lattice.jp k.1) * S7PIF1_Gamma (periodicRieszGrad d R.D.s) B ρ x := by
    intro k
    exact S7PIF1_modEnergy_bound hB hB0 hG (by have := hjp k; positivity)
      (HRS.LocalDivAux.measurable_hTransport hsd (HRS.FieldSingAux.isSmooth_realMode k))
      (S7PIF1_hT_mode_bound R.D.s k) x
  set Γ := S7PIF1_Gamma (periodicRieszGrad d R.D.s) B ρ x with hΓ
  have hcb : ∀ k, |cc k / Lattice.jp k.1| ≤ (N : ℝ) * c1 * Γ := by
    intro k
    have hj := hjp k
    simp only [hcc]
    rw [abs_div, abs_mul, abs_of_pos hj, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N), div_le_iff₀ hj]
    calc (N : ℝ) * |F k| ≤ (N : ℝ) * ((c1 * Lattice.jp k.1) * Γ) :=
          mul_le_mul_of_nonneg_left (hFb k) (by positivity)
      _ = _ := by ring
  have hm1 : (d : ℝ) < 2 * (m - 1) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hmem : Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * cc k) 2 := by
    have h1 := NegSobolev.memℓp_of_bounded hm1 (fun k => cc k / Lattice.jp k.1) ⟨_, hcb⟩
    have e : (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m) * cc k)
        = fun k => Lattice.jp k.1 ^ (-(m - 1)) * (cc k / Lattice.jp k.1) := by
      funext k
      have hj := hjp k
      rw [show -(m - 1) = -m + 1 by ring, Real.rpow_add hj, Real.rpow_one]
      field_simp
    rw [e]
    exact h1
  have hcoef : ∀ k, NegSobolev.fourierCoeff (quadFieldTilde m R.D.s (withDensityReal ρ) x) k = cc k := by
    intro k
    have hq : quadFieldTilde m R.D.s (withDensityReal ρ) x = NegSobolev.ofSeq m cc := rfl
    rw [hq]
    unfold NegSobolev.fourierCoeff
    rw [NegSobolev.coord_ofSeq_of_mem cc hmem k, ← mul_assoc, ← Real.rpow_add (hjp k)]
    simp
  have hev : NegSobolev.eval (quadFieldTilde m R.D.s (withDensityReal ρ) x) ψ
      = (N : ℝ) * modulatedEnergy (hTransport d R.D.s ψ) x (withDensityReal ρ) := by
    unfold NegSobolev.eval
    simp_rw [hcoef]
    have h2 : HasSum (fun k => a k * F k) (modulatedEnergy (hTransport d R.D.s ψ) x (withDensityReal ρ)) := by
      simpa only [hlin] using hsum
    have h3 := h2.mul_left (N : ℝ)
    rw [← h3.tsum_eq]
    refine tsum_congr fun k => ?_
    simp only [hcc, ha]
    ring
  rw [hev, S7PIF1_fluc_eq R.D R.hM hsd hψ hB hB0 hG (tsum_nonneg hw0) hbU hN0 x]
  ring

end HRS.MC.Sec7.S7PIF1

end
