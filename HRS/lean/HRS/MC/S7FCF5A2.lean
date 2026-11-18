import HRS.MC.S7FCF5A1

/-!
# Block A2 of packet `fcf5`: the generator of the mode identity is bounded by `C₀ ⟨k⟩²`

Proof of `fcf5_A2_gen_bound` (`S7FCF5Plan.lean`).  For `u ≥ 0` and a mode `e_k`, the three terms of
`fcGen R u e_k x = β⁻¹ Δe_k(x) - ⟨∇V(x), ∇e_k(x)⟩ - ∫ h_{e_k}(x,y) ρ^u(y) dy` are bounded separately:
`|Δe_k| ≤ d ‖e_k‖_{C²}`, `|∇e_k| ≤ ‖e_k‖_{C²}`, `‖e_k‖_{C²} ≤ 3√2 ⟨k⟩²` (`eqrem_realMode_cb`), `|∇V| ≤ B_V`
(compactness), and the transport kernel envelope `|h_{e_k}(x,y)| ≤ (K d 3√2 + 1)⟨k⟩² (g(x-y)+c)` integrated
against `0 ≤ ρ^u ≤ M₀`.  Namespace `HRS.MC.Sec7.S7FCF5A`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCF5A

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCW7

variable {d : ℕ}

/-- Sum of three absolute values bounds the absolute value of a difference. -/
theorem S7FCF5A_abs_three (a b c : ℝ) : |a - b - c| ≤ |a| + |b| + |c| := by
  have h1 := abs_sub (a - b) c
  have h2 := abs_sub a b
  linarith

/-- The generator of the mode identity is bounded by `C₀ ⟨k⟩²` (proof of `fcf5_A2_gen_bound`). -/
theorem fcf5_A2_gen_bound_proof (R : Regime d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ u : ℝ, 0 ≤ u → ∀ (k : NonzeroLattice d) (x : Torus d),
      |fcGen R u (Torus.realMode k) x| ≤ C₀ * Lattice.jp k.1 ^ 2 := by
  obtain ⟨m₀, M₀, hm₀, hb⟩ := R.bounds
  obtain ⟨K0, c, hK0, hgc0, hwc, henv⟩ := HRS.MC.Sec7.S7b.s7b_envelope R.hd R.D.hs0 R.hs
  have hsd : R.D.s < (d : ℝ) := s7fcw7_sd R.hd R.hs
  have hgc : ∀ z : Torus d, 0 ≤ periodicRiesz d R.D.s z + c := by
    intro z
    by_cases hz : z = 0
    · subst hz; exact hgc0
    · linarith [hwc z hz]
  have hgI : Integrable (fun z : Torus d => periodicRiesz d R.D.s z + c) :=
    (HRS.KernelAux.integrable_periodicRiesz R.hd R.D.hs0 hsd).add (integrable_const c)
  have hI0 : 0 ≤ ∫ z : Torus d, (periodicRiesz d R.D.s z + c) := integral_nonneg hgc
  obtain ⟨BV, hBV⟩ : ∃ B : ℝ, ∀ x : Torus d, ‖Torus.grad R.D.V x‖ ≤ B := by
    obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn
      (HRS.Duality.grad_continuous (s7fcw7_isCk2 R.hV)).continuousOn
    exact ⟨C, fun x => hC x (Set.mem_univ x)⟩
  have hBV0 : 0 ≤ BV := (norm_nonneg _).trans (hBV 0)
  have hM₀0 : 0 ≤ M₀ := hm₀.le.trans ((hb 0 le_rfl 0).1.trans (hb 0 le_rfl 0).2)
  have hsq : 0 ≤ 3 * Real.sqrt 2 := by positivity
  have hKd : 0 ≤ K0 * d * (3 * Real.sqrt 2) :=
    mul_nonneg (mul_nonneg hK0 (Nat.cast_nonneg d)) hsq
  have hA0 : 0 ≤ K0 * d * (3 * Real.sqrt 2) + 1 := by linarith
  refine ⟨|R.D.invβ| * (d * (3 * Real.sqrt 2)) + BV * (3 * Real.sqrt 2) +
      M₀ * ((K0 * d * (3 * Real.sqrt 2) + 1) * ∫ z : Torus d, (periodicRiesz d R.D.s z + c)), ?_, ?_⟩
  · exact add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg d) hsq))
      (mul_nonneg hBV0 hsq)) (mul_nonneg hM₀0 (mul_nonneg hA0 hI0))
  intro u hu k x
  have hfs : Torus.IsSmooth (Torus.realMode k : Torus d → ℝ) := HRS.FieldSingAux.isSmooth_realMode k
  have hfck : Torus.IsCk 2 (Torus.realMode k : Torus d → ℝ) := s7fcw7_isCk2 hfs
  have hcb : Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ) ≤ 3 * Real.sqrt 2 * Lattice.jp k.1 ^ 2 :=
    HRS.MD.EQRem.eqrem_realMode_cb k
  -- the Laplacian term
  have h1 : |R.D.invβ * Torus.laplacian (Torus.realMode k : Torus d → ℝ) x| ≤
      |R.D.invβ| * (d * (3 * Real.sqrt 2)) * Lattice.jp k.1 ^ 2 := by
    rw [abs_mul]
    have hl : |Torus.laplacian (Torus.realMode k : Torus d → ℝ) x| ≤
        d * (3 * Real.sqrt 2) * Lattice.jp k.1 ^ 2 :=
      (HRS.abs_laplacian_le_cbNorm hfck x).trans
        ((mul_le_mul_of_nonneg_left hcb (Nat.cast_nonneg d)).trans (le_of_eq (by ring)))
    calc |R.D.invβ| * |Torus.laplacian (Torus.realMode k : Torus d → ℝ) x|
        ≤ |R.D.invβ| * (d * (3 * Real.sqrt 2) * Lattice.jp k.1 ^ 2) :=
          mul_le_mul_of_nonneg_left hl (abs_nonneg _)
      _ = _ := by ring
  -- the transport term of the gradient of V
  have h2 : |inner ℝ (Torus.grad R.D.V x) (Torus.grad (Torus.realMode k : Torus d → ℝ) x)| ≤
      BV * (3 * Real.sqrt 2) * Lattice.jp k.1 ^ 2 := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have hg : ‖Torus.grad (Torus.realMode k : Torus d → ℝ) x‖ ≤ Torus.cbNorm 2 (Torus.realMode k : Torus d → ℝ) :=
      HRS.norm_grad_le_cbNorm_two hfck x
    calc ‖Torus.grad R.D.V x‖ * ‖Torus.grad (Torus.realMode k : Torus d → ℝ) x‖
        ≤ BV * (3 * Real.sqrt 2 * Lattice.jp k.1 ^ 2) :=
          mul_le_mul (hBV x) (hg.trans hcb) (norm_nonneg _) hBV0
      _ = _ := by ring
  -- the interaction term
  have hρm : Measurable (R.ρ u) := (S7FCF5A_rho_cont_x R hu).measurable
  have hρ0 : ∀ y, 0 ≤ R.ρ u y := fun y => hm₀.le.trans (hb u hu y).1
  have hρM : ∀ y, R.ρ u y ≤ M₀ := fun y => (hb u hu y).2
  have hbd : ∀ y : Torus d, |hTransport d R.D.s (Torus.realMode k : Torus d → ℝ) x y| ≤
      (K0 * d * (3 * Real.sqrt 2) + 1) * Lattice.jp k.1 ^ 2 * (periodicRiesz d R.D.s (x - y) + c) :=
    fun y => HRS.MC.Sec7.S7FCW3.s7fcw3_hT_env hK0 k henv x y (hgc (x - y))
  have h3 : |∫ y, hTransport d R.D.s (Torus.realMode k : Torus d → ℝ) x y ∂(withDensityReal (R.ρ u))| ≤
      M₀ * ((K0 * d * (3 * Real.sqrt 2) + 1) * ∫ z : Torus d, (periodicRiesz d R.D.s z + c)) *
        Lattice.jp k.1 ^ 2 := by
    rw [HRS.PDE.MFPairing.integral_withDensityReal hρm hρ0, ← Real.norm_eq_abs]
    have hint : Integrable (fun y : Torus d => M₀ * ((K0 * d * (3 * Real.sqrt 2) + 1) * Lattice.jp k.1 ^ 2 *
        (periodicRiesz d R.D.s (x - y) + c))) :=
      ((hgI.comp_sub_left x).const_mul _).const_mul _
    calc ‖∫ y, R.ρ u y * hTransport d R.D.s (Torus.realMode k : Torus d → ℝ) x y‖
        ≤ ∫ y, M₀ * ((K0 * d * (3 * Real.sqrt 2) + 1) * Lattice.jp k.1 ^ 2 *
            (periodicRiesz d R.D.s (x - y) + c)) := by
          refine norm_integral_le_of_norm_le hint (Eventually.of_forall fun y => ?_)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 y)]
          exact mul_le_mul (hρM y) (hbd y) (abs_nonneg _) hM₀0
      _ = M₀ * ((K0 * d * (3 * Real.sqrt 2) + 1) * ∫ z : Torus d, (periodicRiesz d R.D.s z + c)) *
            Lattice.jp k.1 ^ 2 := by
          rw [integral_const_mul, integral_const_mul]
          have hsl : ∫ y : Torus d, (periodicRiesz d R.D.s (x - y) + c) =
              ∫ z : Torus d, (periodicRiesz d R.D.s z + c) :=
            integral_sub_left_eq_self (fun z : Torus d => periodicRiesz d R.D.s z + c) volume x
          rw [hsl]
          ring
  -- combine the three terms
  unfold fcGen
  have hsum := S7FCF5A_abs_three (R.D.invβ * Torus.laplacian (Torus.realMode k : Torus d → ℝ) x)
    (inner ℝ (Torus.grad R.D.V x) (Torus.grad (Torus.realMode k : Torus d → ℝ) x))
    (∫ y, hTransport d R.D.s (Torus.realMode k : Torus d → ℝ) x y ∂(withDensityReal (R.ρ u)))
  have e : (|R.D.invβ| * (d * (3 * Real.sqrt 2)) + BV * (3 * Real.sqrt 2) +
      M₀ * ((K0 * d * (3 * Real.sqrt 2) + 1) * ∫ z : Torus d, (periodicRiesz d R.D.s z + c))) *
        Lattice.jp k.1 ^ 2 =
      |R.D.invβ| * (d * (3 * Real.sqrt 2)) * Lattice.jp k.1 ^ 2 + BV * (3 * Real.sqrt 2) * Lattice.jp k.1 ^ 2 +
      M₀ * ((K0 * d * (3 * Real.sqrt 2) + 1) * ∫ z : Torus d, (periodicRiesz d R.D.s z + c)) *
        Lattice.jp k.1 ^ 2 := by ring
  rw [e]
  linarith [hsum, h1, h2, h3]

end HRS.MC.Sec7.S7FCF5A

end
