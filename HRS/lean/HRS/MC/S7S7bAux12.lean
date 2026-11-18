import HRS.MC.S7S7bAux11
import HRS.MC.S7S7a
import HRS.MC.SEdgeB9sym

/-!
# Packet `s7_S7b_weighted_moments`, helper 12: the drift observable `w_{kl} = v_k . grad phi_l`
Smoothness, the sup bound `|w_{kl}| <= C b_k b_l` and `mu(w_{kl}) = mu(phi_l a_k)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge HRS.PDE HRS.PDE.ClassicalPart HRS.MC.Sec7.S7a
  HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg

variable {d : ℕ} {s : ℝ}

theorem s7b_isSmooth_sum {ι : Type*} (S : Finset ι) {f : ι → Torus d → ℝ}
    (h : ∀ i, Torus.IsSmooth (f i)) : Torus.IsSmooth (fun x => ∑ i ∈ S, f i x) := by
  unfold Torus.IsSmooth Torus.IsCk Torus.lift
  exact ContDiff.sum fun i _ => h i

theorem s7b_drift_smooth {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Torus.IsSmooth (sed_drift v φ) := by
  have := s7b_isSmooth_sum (Finset.univ : Finset (Fin d))
    (f := fun k x => v k x * Torus.partialDeriv k φ x)
    (fun k => HRS.Q66.q66_isSmooth_mul (hv k) (HRS.Q66.q66_isSmooth_partialDeriv hφ k))
  exact this

theorem s7b_phi_cb1 (r : ℝ) (k : NonzeroLattice d) :
    Torus.cbNorm 1 (s7_phi r k) ≤ 2 * Real.sqrt 2 * Lattice.jp k.1 ^ (1 - r) := by
  classical
  have hjp : 0 < Lattice.jp k.1 := Torus.jp_pos _
  set a : ℝ := (if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Lattice.jp k.1 ^ (-r) else 0) with ha
  set b : ℝ := (if Lattice.IsPosHalf k.1 then 0 else Real.sqrt 2 * Lattice.jp k.1 ^ (-r)) with hb
  have hab : |a| + |b| = Real.sqrt 2 * Lattice.jp k.1 ^ (-r) := by
    have h0 : 0 ≤ Real.sqrt 2 * Lattice.jp k.1 ^ (-r) := by positivity
    by_cases h : Lattice.IsPosHalf k.1
    · simp [ha, hb, h, abs_of_nonneg h0]
    · simp [ha, hb, h, abs_of_nonneg h0]
  have hcb := cbNorm_trigTerm_le a b k.1 1
  rw [← s7a_phi_eq_trig, hab] at hcb
  have hpow : Lattice.jp k.1 ^ 1 * Lattice.jp k.1 ^ (-r) = Lattice.jp k.1 ^ (1 - r) := by
    rw [sub_eq_add_neg, Real.rpow_add hjp, Real.rpow_one, pow_one]
  refine hcb.trans (le_of_eq ?_)
  push_cast
  rw [← hpow]
  ring

theorem s7b_drift_bound {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) {C₀ : ℝ}
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} (hv : ∀ k j, Torus.IsSmooth (v k j))
    (hb : ∀ k j, Torus.cbNorm 1 (v k j) ≤ C₀ * s7_b k) (k l : NonzeroLattice d) (x : Torus d) :
    |sed_drift (v k) (s7_phi r l) x| ≤ (d * max C₀ 0 * (2 * Real.sqrt 2)) * (s7_b k * s7_b l) := by
  have hjl : 1 ≤ Lattice.jp l.1 := Torus.jp_ge_one _
  have hφ1 : Torus.cbNorm 1 (s7_phi r l) ≤ 2 * Real.sqrt 2 * s7_b l := by
    refine (s7b_phi_cb1 r l).trans ?_
    unfold s7_b
    have : Lattice.jp l.1 ^ (1 - r) ≤ Lattice.jp l.1 ^ (-((d : ℝ) + 3)) :=
      Real.rpow_le_rpow_of_exponent_le hjl (by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)])
    nlinarith [Real.sqrt_nonneg 2]
  have hφsm := s7a_phi_smooth (d := d) r l
  have hφC : Torus.IsCk ((0 + 1 : ℕ) : WithTop ℕ∞) (s7_phi r l) :=
    HRS.Q66.q66_isCk_of_smooth hφsm _
  have hterm : ∀ j : Fin d, |v k j x * Torus.partialDeriv j (s7_phi r l) x| ≤
      max C₀ 0 * s7_b k * (2 * Real.sqrt 2 * s7_b l) := by
    intro j
    rw [abs_mul]
    have h1 : |v k j x| ≤ max C₀ 0 * s7_b k := by
      refine (HRS.PDE.R2Aux.abs_le_cbNorm (HRS.Q66.q66_isCk_of_smooth (hv k j) 1) x).trans ?_
      refine (hb k j).trans ?_
      have : 0 ≤ s7_b k := by unfold s7_b; have := Torus.jp_pos k.1; positivity
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
    obtain ⟨hC0, hCb⟩ := cbNorm_partialDeriv_le 0 (s7_phi r l) hφC j
    have h2 : |Torus.partialDeriv j (s7_phi r l) x| ≤ 2 * Real.sqrt 2 * s7_b l := by
      refine (HRS.PDE.R2Aux.abs_le_cbNorm hC0 x).trans (hCb.trans ?_)
      simpa using hφ1
    exact mul_le_mul h1 h2 (abs_nonneg _) (by
      have : 0 ≤ s7_b k := by unfold s7_b; have := Torus.jp_pos k.1; positivity
      positivity)
  unfold sed_drift
  calc |∑ j, v k j x * Torus.partialDeriv j (s7_phi r l) x|
      ≤ ∑ j, |v k j x * Torus.partialDeriv j (s7_phi r l) x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, max C₀ 0 * s7_b k * (2 * Real.sqrt 2 * s7_b l) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by simp; ring

/-- `mu(w_{kl}) = mu(phi_l a_k)`. -/
theorem s7b_drift_mean (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (r : ℝ) {a : NonzeroLattice d → Torus d → ℝ}
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ} (hmode : s7_ModeData d s γ ρ r a v C₀)
    (k l : NonzeroLattice d) :
    pair (withDensityReal ρ) (sed_drift (v k) (s7_phi r l)) = s7_Cmode r ρ a l k := by
  have h := HRS.MC.SEdge.B9sym.b9s_part1 hd (hρ := hρ) (s7a_phi_smooth r l) (hmode.smooth_a k)
    (hmode.smooth_v k) (hmode.div k)
  unfold pair s7_Cmode
  rw [h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

end HRS.MC.Sec7.S7b

end
