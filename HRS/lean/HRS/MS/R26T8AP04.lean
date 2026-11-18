import HRS.MS.R26T8AP03

/-!
# S8.2 local Newton layer, packet T8A.P04: separated annulus with small z
Separated annulus: truncate the Newton kernel (P03 parts a-e), bound the nested jet by `r26t8a_sep_bound` (part f) and the scale bound of the
kernel jets (part g).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_p04 (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (nu M sigma : ℝ)
    (hnu : 0 < nu) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ,
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z,
      z ≠ 0 → 2*‖z‖ ≤ R/2 → ∀ p q : ℕ, p+q ≤ k →
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularNewton nu chi R F Y) z) X‖ ≤
          C*A*jbracket X^(2*M) * (R^(2-sigma-q)) *
          (1+|Real.log R|)^b *
          (if d=2 ∧ q=0 then 1+|Real.log R|+|Real.log ‖z‖| else 1) := by
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_kernel_scale d hd nu hnu k
  obtain ⟨-, -, hK, -⟩ := r26t8a_newton_kernel_jets d hd nu hnu k
  obtain ⟨C3, hC30, hC3⟩ := r26t8a_sep_bound (d := d) (k := k) (b := b) hM hsigma hchi hK
  refine ⟨C3 * (C2 * 4 ^ ((d : ℝ) + k) * (1 + Real.log 4)), by positivity,
    fun A hA F hF R hR hR1 X z hz hRz p q hpq => ?_⟩
  have hq : q ≤ k := by omega
  have hgeo : ∀ w : Euc d, R / 2 ≤ ‖w‖ → ‖w‖ ≤ 2 * R → R / 4 ≤ ‖z - w‖ ∧ ‖z - w‖ ≤ 4 * R := by
    intro w hw1 hw2
    constructor
    · have := norm_sub_norm_le w z
      rw [norm_sub_rev] at this
      linarith
    · have := norm_sub_le z w
      linarith
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set B : ℝ := C2 * 4 ^ ((d : ℝ) + k) * (1 + Real.log 4) * R ^ (2 - (d : ℝ) - q) *
    (if d = 2 ∧ q = 0 then 1 + |Real.log R| else 1) with hBdef
  have hLnn : 0 ≤ (if d = 2 ∧ q = 0 then 1 + |Real.log R| else (1 : ℝ)) := by
    split_ifs
    · positivity
    · exact zero_le_one
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hBb : ∀ u : Euc d, R / 4 ≤ ‖u‖ → ‖u‖ ≤ 4 * R →
      ‖iteratedFDeriv ℝ q (newtonKernel d nu) u‖ ≤ B := fun u h1 h2 => by
    have := hC2 R hR 4 (by norm_num) q hq u (by linarith) h2
    rw [hBdef]; linarith
  have main := hC3 A hA F hF R hR hR1 (R / 4) (4 * R) (by positivity) (by linarith) z hgeo q B hB0 hBb p hpq X
  refine main.trans ?_
  have hif : (if d = 2 ∧ q = 0 then 1 + |Real.log R| else (1 : ℝ)) ≤
      (if d = 2 ∧ q = 0 then 1 + |Real.log R| + |Real.log ‖z‖| else 1) := by
    split_ifs
    · linarith [abs_nonneg (Real.log ‖z‖)]
    · exact le_rfl
  have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (by unfold jbracket; positivity) _
  have hRR : R ^ ((d : ℝ) - sigma) * R ^ (2 - (d : ℝ) - q) = R ^ (2 - sigma - (q : ℝ)) := by
    rw [← Real.rpow_add hR]; congr 1; ring
  have hpos : 0 ≤ C3 * (C2 * 4 ^ ((d : ℝ) + k) * (1 + Real.log 4)) * A * jbracket X ^ (2 * M) *
      R ^ (2 - sigma - (q : ℝ)) * (1 + |Real.log R|) ^ b := by positivity
  calc _ = C3 * (C2 * 4 ^ ((d : ℝ) + k) * (1 + Real.log 4)) * A * jbracket X ^ (2 * M) *
        (R ^ ((d : ℝ) - sigma) * R ^ (2 - (d : ℝ) - q)) * (1 + |Real.log R|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log R| else 1) := by rw [hBdef]; ring
    _ = C3 * (C2 * 4 ^ ((d : ℝ) + k) * (1 + Real.log 4)) * A * jbracket X ^ (2 * M) *
        R ^ (2 - sigma - (q : ℝ)) * (1 + |Real.log R|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log R| else 1) := by rw [hRR]
    _ ≤ _ := mul_le_mul_of_nonneg_left hif hpos

end HRS.MS.R26T8A
