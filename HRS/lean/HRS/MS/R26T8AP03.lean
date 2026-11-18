import HRS.MS.R26T8AP03g

/-!
# S8.2 local Newton layer, packet T8A.P03: small source annulus, differentiate only the Newton kernel
Separated annulus: truncate the Newton kernel (P03 parts a-e), bound the nested jet by `r26t8a_sep_bound` (part f) and the scale bound of the
kernel jets (part g).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_p03 (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (nu M sigma : ℝ)
    (hnu : 0 < nu) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ,
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z,
      z ≠ 0 → 2*R ≤ ‖z‖/2 → ∀ p q : ℕ, p+q ≤ k →
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularNewton nu chi R F Y) z) X‖ ≤
          C*A*jbracket X^(2*M) * (R^((d:ℝ)-sigma) * ‖z‖^(2-(d:ℝ)-q)) *
          (1+|Real.log R|)^b *
          (if d=2 ∧ q=0 then 1+|Real.log R|+|Real.log ‖z‖| else 1) := by
  obtain ⟨C2, hC20, hC2⟩ := r26t8a_kernel_scale d hd nu hnu k
  obtain ⟨-, -, hK, -⟩ := r26t8a_newton_kernel_jets d hd nu hnu k
  obtain ⟨C3, hC30, hC3⟩ := r26t8a_sep_bound (d := d) (k := k) (b := b) hM hsigma hchi hK
  refine ⟨C3 * (C2 * 2 ^ ((d : ℝ) + k) * (1 + Real.log 2)), by positivity,
    fun A hA F hF R hR hR1 X z hz hRz p q hpq => ?_⟩
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hq : q ≤ k := by omega
  have hgeo : ∀ w : Euc d, R / 2 ≤ ‖w‖ → ‖w‖ ≤ 2 * R → ‖z‖ / 2 ≤ ‖z - w‖ ∧ ‖z - w‖ ≤ 2 * ‖z‖ := by
    intro w _ hw
    constructor
    · have := norm_sub_norm_le z w
      linarith
    · have := norm_sub_le z w
      linarith
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set B : ℝ := C2 * 2 ^ ((d : ℝ) + k) * (1 + Real.log 2) * ‖z‖ ^ (2 - (d : ℝ) - q) *
    (if d = 2 ∧ q = 0 then 1 + |Real.log ‖z‖| else 1) with hBdef
  have hLnn : 0 ≤ (if d = 2 ∧ q = 0 then 1 + |Real.log ‖z‖| else (1 : ℝ)) := by
    split_ifs
    · positivity
    · exact zero_le_one
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  have hBb : ∀ u : Euc d, ‖z‖ / 2 ≤ ‖u‖ → ‖u‖ ≤ 2 * ‖z‖ →
      ‖iteratedFDeriv ℝ q (newtonKernel d nu) u‖ ≤ B := fun u h1 h2 => by
    have := hC2 ‖z‖ hzpos 2 one_le_two q hq u h1 h2
    rw [hBdef]; linarith
  have main := hC3 A hA F hF R hR hR1 (‖z‖ / 2) (2 * ‖z‖) (by positivity) (by linarith) z hgeo q B hB0 hBb p hpq X
  refine main.trans ?_
  have hif : (if d = 2 ∧ q = 0 then 1 + |Real.log ‖z‖| else (1 : ℝ)) ≤
      (if d = 2 ∧ q = 0 then 1 + |Real.log R| + |Real.log ‖z‖| else 1) := by
    split_ifs
    · linarith [abs_nonneg (Real.log R)]
    · exact le_rfl
  have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (by unfold jbracket; positivity) _
  have hpos : 0 ≤ C3 * (C2 * 2 ^ ((d : ℝ) + k) * (1 + Real.log 2)) * A * jbracket X ^ (2 * M) *
      (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ (2 - (d : ℝ) - q)) * (1 + |Real.log R|) ^ b := by positivity
  calc _ = C3 * (C2 * 2 ^ ((d : ℝ) + k) * (1 + Real.log 2)) * A * jbracket X ^ (2 * M) *
        (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ (2 - (d : ℝ) - q)) * (1 + |Real.log R|) ^ b *
        (if d = 2 ∧ q = 0 then 1 + |Real.log ‖z‖| else 1) := by rw [hBdef]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hif hpos

end HRS.MS.R26T8A
