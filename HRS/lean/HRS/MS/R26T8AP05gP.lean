import HRS.MS.R26T8AP05f
import HRS.MS.R26T8AP01p
import HRS.MS.R26T8AP05g

/-!
# S8.2 local Newton layer, packet T8A.P05 (part g): the comparable annulus bound
`r26t8a_conv_boundP`: for `|z| <= 4R` the nested jet of the annular Newton integral is `<= C A <X>^{2M} R^{2-sigma-q} (1+|log R|)^b`
times `(1+|log R|)` when `d = 2`, `q = 0`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_conv_boundP (hd : 2 ≤ d) {k b : ℕ} {M sigma : ℝ} (hM : 0 ≤ M) 
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (nu : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, ConormalP k b M sigma A F →
      ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ z : Euc d, ‖z‖ ≤ 4 * R → ∀ p q : ℕ, p + q ≤ k → ∀ X : Euc d,
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (r26t8a_annularNewton nu chi R F Y) z) X‖ ≤
          C * A * jbracket X ^ (2 * M) * R ^ (2 - sigma - (q : ℝ)) * (1 + |Real.log R|) ^ b *
            (if d = 2 ∧ q = 0 then 1 + |Real.log R| else 1) := by
  obtain ⟨C1, hC10, hC1⟩ := r26t8a_annular_sourceP k b M sigma hM chi hchi
  set JG : ℝ := ∫ v in Metric.ball (0 : Euc d) 7, r26t8a_p05_G d v with hJG
  have hJG0 : 0 ≤ JG :=
    setIntegral_nonneg Metric.isOpen_ball.measurableSet (fun v _ => r26t8a_G_nonneg d v)
  set V : ℝ := (volume (Metric.ball (0 : Euc d) 1)).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set cK : ℝ := r26t8a_cK d nu with hcKdef
  have hcK0 : 0 ≤ cK := r26t8a_cK_nonneg d nu
  refine ⟨C1 * cK * (JG + V * 7 ^ d), by positivity, fun A hA F hF R hR hR1 z hz p q hpq X => ?_⟩
  obtain ⟨hts, hsrc⟩ := hC1 A hA F hF R hR hR1
  rw [r26t8a_conv_formula hd hchi nu hR hF.1 hz hpq (r26t8a_kappa d nu R q)
    (fun hq => by simp [r26t8a_kappa, hq]) X]
  have hjb : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (by unfold jbracket; positivity) _
  set L : ℝ := (1 + |Real.log R|) ^ b with hL
  have hL0 : 0 ≤ L := by positivity
  set c0 : ℝ := C1 * A * jbracket X ^ (2 * M) * R ^ (-(sigma + ((q : ℕ) : ℝ))) * L with hc0def
  have hc0 : 0 ≤ c0 := by rw [hc0def]; positivity
  set ε : ℝ := if d = 2 ∧ q = 0 then |Real.log R| else 0 with hεdef
  have hε0 : 0 ≤ ε := by rw [hεdef]; split_ifs <;> positivity
  set a : ℝ := c0 * cK * R ^ (2 - (d : ℝ)) with hadef
  set bb : ℝ := c0 * cK * ε with hbbdef
  have hscale := r26t8a_scale_int (G := r26t8a_p05_G d) (r26t8a_G_integrableOn hd) hR
  have hint1 : Integrable ((Metric.ball (0 : Euc d) (7 * R)).indicator fun _ => (1 : ℝ)) :=
    (integrable_indicator_iff Metric.isOpen_ball.measurableSet).2
      (integrableOn_const (Metric.isBounded_ball.measure_lt_top.ne))
  have hpt : ∀ u : Euc d, u ≠ 0 →
      ‖r26t8a_Kk chi nu (r26t8a_kappa d nu R q) (6 * R + 1) u • iteratedFDeriv ℝ p
        (fun Y => iteratedFDeriv ℝ q (fun w => r26t8a_annulus chi R w * midPair F Y w) (z - u)) X‖ ≤
        a * (Metric.ball (0 : Euc d) (7 * R)).indicator (fun u => r26t8a_p05_G d (R⁻¹ • u)) u +
          bb * (Metric.ball (0 : Euc d) (7 * R)).indicator (fun _ => (1 : ℝ)) u := by
    intro u hu0
    by_cases hu7 : u ∈ Metric.ball (0 : Euc d) (7 * R)
    · rw [Set.indicator_of_mem hu7, Set.indicator_of_mem hu7]
      have hu7' : ‖u‖ < 7 * R := by simpa using hu7
      have hKk := r26t8a_Kk_eq hchi (nu := nu) (kappa := r26t8a_kappa d nu R q) (r1 := 6 * R + 1)
        (by positivity) (u := u) (by linarith)
      have hJ := hsrc p q hpq X (z - u)
      rw [norm_smul, hKk, Real.norm_eq_abs]
      have hK := r26t8a_K_sub_bound nu hR q hu0
      have hG0 := r26t8a_G_nonneg d (R⁻¹ • u)
      calc _ ≤ (cK * (R ^ (2 - (d : ℝ)) * r26t8a_p05_G d (R⁻¹ • u) + ε)) * c0 := by
            refine mul_le_mul hK ?_ (norm_nonneg _) (by positivity)
            exact hJ
        _ = _ := by rw [hadef, hbbdef]; ring
    · rw [Set.indicator_of_notMem hu7, Set.indicator_of_notMem hu7]
      have hu7' : 7 * R ≤ ‖u‖ := by simpa using hu7
      have hnot : z - u ∉ tsupport (r26t8a_annulus chi R) := by
        intro hmem
        obtain ⟨-, h2⟩ := hts hmem
        have : ‖u‖ ≤ ‖z‖ + ‖z - u‖ := by
          calc ‖u‖ = ‖z - (z - u)‖ := by congr 1; abel
            _ ≤ ‖z‖ + ‖z - u‖ := norm_sub_le _ _
        linarith
      rw [r26t8a_nested_zero hnot p q X]
      simp
  have hg : Integrable (fun u => a * (Metric.ball (0 : Euc d) (7 * R)).indicator
      (fun u => r26t8a_p05_G d (R⁻¹ • u)) u + bb * (Metric.ball (0 : Euc d) (7 * R)).indicator
      (fun _ => (1 : ℝ)) u) := (hscale.1.const_mul a).add (hint1.const_mul bb)
  have hI : ∫ u, (a * (Metric.ball (0 : Euc d) (7 * R)).indicator (fun u => r26t8a_p05_G d (R⁻¹ • u)) u +
      bb * (Metric.ball (0 : Euc d) (7 * R)).indicator (fun _ => (1 : ℝ)) u) =
      a * (R ^ d * JG) + bb * ((volume (Metric.ball (0 : Euc d) (7 * R))).toReal * 1) := by
    rw [integral_add (hscale.1.const_mul a) (hint1.const_mul bb), integral_const_mul, integral_const_mul,
      hscale.2, integral_indicator_const _ Metric.isOpen_ball.measurableSet, smul_eq_mul]
    rfl
  refine (norm_integral_le_of_norm_le hg ((r26t8a_ae_ne_zero hd).mono fun u hu => hpt u hu)).trans ?_
  rw [hI, r26t8a_ball_volume' hd hR]
  -- final algebra
  have hE1 : R ^ (-(sigma + ((q : ℕ) : ℝ))) * R ^ (2 - (d : ℝ)) * R ^ d = R ^ (2 - sigma - (q : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR, ← Real.rpow_add hR]; congr 1; ring
  set Rq : ℝ := R ^ (2 - sigma - (q : ℝ)) with hRq
  have hRq0 : 0 ≤ Rq := Real.rpow_nonneg hR.le _
  set X0 : ℝ := C1 * A * jbracket X ^ (2 * M) * Rq * L * cK with hX0
  have hX00 : 0 ≤ X0 := by rw [hX0]; positivity
  have hterm1 : a * (R ^ d * JG) = X0 * JG := by
    rw [hadef, hc0def, hX0, ← hE1]; ring
  have hW0 : 0 ≤ V * 7 ^ d := by positivity
  by_cases hε : d = 2 ∧ q = 0
  · obtain ⟨hd2, hq0⟩ := id hε
    have hεv : ε = |Real.log R| := by rw [hεdef]; simp [hd2, hq0]
    have hE2 : R ^ (-(sigma + ((q : ℕ) : ℝ))) * R ^ d = Rq := by
      have h1 : (d : ℝ) = 2 := by exact_mod_cast hd2
      have h2 : (q : ℝ) = 0 := by exact_mod_cast hq0
      rw [hRq, ← Real.rpow_natCast, ← Real.rpow_add hR]; congr 1; rw [h1, h2]; ring
    have hterm2 : bb * (V * (7 ^ d * R ^ d) * 1) = X0 * (|Real.log R| * (V * 7 ^ d)) := by
      rw [hbbdef, hc0def, hX0, hεv, ← hE2]; ring
    rw [hterm1, hterm2]
    rw [if_pos hε]
    have hl0 : 0 ≤ |Real.log R| := abs_nonneg _
    have key : JG + |Real.log R| * (V * 7 ^ d) ≤ (JG + V * 7 ^ d) * (1 + |Real.log R|) := by
      nlinarith [mul_nonneg hl0 hJG0]
    calc X0 * JG + X0 * (|Real.log R| * (V * 7 ^ d)) = X0 * (JG + |Real.log R| * (V * 7 ^ d)) := by ring
      _ ≤ X0 * ((JG + V * 7 ^ d) * (1 + |Real.log R|)) := mul_le_mul_of_nonneg_left key hX00
      _ = _ := by rw [hX0]; ring
  · have hεv : ε = 0 := by rw [hεdef]; simp [hε]
    have hbb0 : bb = 0 := by rw [hbbdef, hεv]; ring
    rw [hterm1, hbb0, if_neg hε]
    calc X0 * JG + 0 * ((V * (7 ^ d * R ^ d)) * 1) = X0 * JG := by ring
      _ ≤ X0 * (JG + V * 7 ^ d) := mul_le_mul_of_nonneg_left (by linarith) hX00
      _ = _ := by rw [hX0]; ring

end HRS.MS.R26T8A
