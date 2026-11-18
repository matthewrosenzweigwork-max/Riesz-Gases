import HRS.MS.R26T8AP11c
import HRS.MS.R26T8APot4

/-!
# S8.2 nonlocal layer, packet T8A.P11b: single annulus, kernel far from the shell (`|z| >= 4R`)
All derivatives fall on the smooth kernel (`r26t8a_far_conv`, jets from P11a); the source is bounded by P01 with `q = 0`
and the support volume is `omega_d (2R)^d`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_p11b (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z, z ≠ 0 → 2 * R ≤ ‖z‖ / 2 →
      ∀ p q : ℕ, p + q ≤ k →
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularRiesz alpha chi R F Y) z) X‖ ≤
          C * A * jbracket X ^ (2 * M) * (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ (alpha - (d : ℝ) - q)) *
            (1 + |Real.log R|) ^ b := by
  obtain ⟨CK, hCK0, hKsm, hKj, -⟩ := r26t8a_riesz_potential_jets d hd alpha halpha had k
  obtain ⟨C1, hC10, hP1⟩ := r26t8a_annular_source k b M sigma hM hsigma chi hchi
  set omg : ℝ := (volume : Measure (Euc d)).real (ball (0 : Euc d) 1) with homg
  have homg0 : 0 ≤ omg := measureReal_nonneg
  refine ⟨C1 * 3 ^ (2 * M) * CK * 2 ^ ((d : ℝ) + k) * 2 ^ d * omg, by positivity, ?_⟩
  intro F A hA hF R hR hR1 X z hz0 hz p q hpq
  obtain ⟨-, hbd⟩ := hP1 A hA F hF R hR hR1
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hSd : ContDiff ℝ (p : WithTop ℕ∞) (r26t8a_p11_src chi R F) :=
    (r26t8a_p11_src_contDiff hchi hR hF.1).of_le (by exact_mod_cast (by omega : p ≤ k))
  have hfun : (fun Y => iteratedFDeriv ℝ q (r26t8a_annularRiesz alpha chi R F Y) z) =
      fun Y => iteratedFDeriv ℝ q (fun z' => ∫ v, ‖z' - v‖ ^ (alpha - (d : ℝ)) *
        r26t8a_p11_src chi R F (Y, v)) z := by
    funext Y
    congr 1
    funext z'
    unfold r26t8a_annularRiesz
    congr 1
    funext v
    rw [mul_assoc, r26t8a_p11_src_eq hchi hR]
  rw [hfun]
  change ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ v, ‖Yw.2 - v‖ ^ (alpha - (d : ℝ)) *
    r26t8a_p11_src chi R F (Yw.1, v)) X z‖ ≤ _
  set L : ℝ := (1 + |Real.log R|) ^ b with hL
  have hL0 : 0 ≤ L := by positivity
  have hRs : 0 ≤ R ^ (-sigma) := Real.rpow_nonneg hR.le _
  have hjb0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
  set B : ℝ := C1 * A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) * R ^ (-sigma) * L with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBd : ∀ i ≤ p, ∀ Y : Euc d, ‖Y - X‖ < 1 → ∀ w : Euc d,
      ‖r26t8a_nest i 0 (r26t8a_p11_src chi R F) Y w‖ ≤ B := by
    intro i hi Y hY w
    have h1 := hbd i 0 (by omega) Y w
    rw [r26t8a_p11_src_nest hchi hR F i 0 Y w] at h1
    refine h1.trans ?_
    have hjb : jbracket Y ≤ 3 * jbracket X := by
      have := r26t8a_p01_jb_shift (x := X) (y := Y - X) (by simpa using hY.le)
      simpa using this
    have hjb2 : jbracket Y ^ (2 * M) ≤ 3 ^ (2 * M) * jbracket X ^ (2 * M) := by
      rw [← Real.mul_rpow (by norm_num) (s83_jb_pos X).le]
      exact Real.rpow_le_rpow (s83_jb_pos Y).le hjb (by positivity)
    have hexp : R ^ (-(sigma + ((0 : ℕ) : ℝ))) = R ^ (-sigma) := by simp
    rw [hexp, hB]
    have h1 : C1 * A * jbracket Y ^ (2 * M) ≤ C1 * A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) :=
      mul_le_mul_of_nonneg_left hjb2 (by positivity)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hRs) hL0
  -- kernel bounds
  set ρ0 : ℝ := ‖z‖ / 4 with hρ0
  set ρ1 : ℝ := ‖z‖ / 2 with hρ1
  have hρ0p : 0 < ρ0 := by rw [hρ0]; positivity
  have hρ1p : 0 < ρ1 := by rw [hρ1]; positivity
  have hneg : ∀ j : ℕ, alpha - (d : ℝ) - j ≤ 0 := fun j => by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hpow : ∀ (j : ℕ) (r x : ℝ), 0 < r → r ≤ x → x ^ (alpha - (d : ℝ) - j) ≤ r ^ (alpha - (d : ℝ) - j) :=
    fun j r x hr hrx => Real.rpow_le_rpow_of_nonpos hr hrx (hneg j)
  set BK : ℝ := CK * ∑ j ∈ Finset.range (q + 1), ρ0 ^ (alpha - (d : ℝ) - j) with hBK
  have hBKd : ∀ j ≤ q, ∀ x : Euc d, ρ0 ≤ ‖x‖ → ‖iteratedFDeriv ℝ j (fun v : Euc d => ‖v‖ ^ (alpha - (d : ℝ))) x‖ ≤ BK := by
    intro j hj x hx
    have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hx; linarith
    refine (hKj j (by omega) x hx0).trans ?_
    rw [hBK]
    refine mul_le_mul_of_nonneg_left ?_ hCK0
    refine (hpow j ρ0 ‖x‖ hρ0p hx).trans ?_
    exact Finset.single_le_sum (f := fun j : ℕ => ρ0 ^ (alpha - (d : ℝ) - j))
      (fun i _ => Real.rpow_nonneg hρ0p.le _) (Finset.mem_range.2 (by omega))
  have hBKd' : ∀ x : Euc d, ρ1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ q (fun v : Euc d => ‖v‖ ^ (alpha - (d : ℝ))) x‖ ≤ CK * ρ1 ^ (alpha - (d : ℝ) - q) := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hx; linarith
    refine (hKj q (by omega) x hx0).trans ?_
    exact mul_le_mul_of_nonneg_left (hpow q ρ1 ‖x‖ hρ1p hx) hCK0
  have hmain := r26t8a_far_conv (fun v : Euc d => ‖v‖ ^ (alpha - (d : ℝ))) p q
    (hKsm.of_le (by exact_mod_cast le_top)) (r26t8a_p11_src chi R F) hSd (2 * R)
    (fun Y w hw => r26t8a_p11_src_vanish hchi hR F Y w hw) X z ρ0 hρ0p ρ0 hρ0p
    (fun z' hz' v hv => by
      have h1 : ‖z'‖ > ‖z‖ - ρ0 := by
        have := norm_sub_norm_le z z'
        have h3 : ‖z - z'‖ < ρ0 := by simpa [dist_eq_norm, norm_sub_rev] using hz'
        linarith
      have h2 := norm_sub_norm_le z' v
      have : ‖z'‖ - ‖v‖ ≤ ‖z' - v‖ := h2
      rw [hρ0] at *
      linarith)
    BK hBKd ρ1 (CK * ρ1 ^ (alpha - (d : ℝ) - q))
    (fun v hv => by
      have h2 := norm_sub_norm_le z v
      rw [hρ1]; linarith)
    hBKd' B hBd
  refine hmain.trans ?_
  have hvol : (volume : Measure (Euc d)).real (closedBall (0 : Euc d) (2 * R)) = (2 * R) ^ d * omg := by
    rw [Measure.addHaar_real_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin]
  rw [hvol]
  set e : ℝ := alpha - (d : ℝ) - q with he
  have hzne : 0 ≤ ‖z‖ ^ e := Real.rpow_nonneg hzpos.le _
  have hρ1e : ρ1 ^ e ≤ 2 ^ ((d : ℝ) + k) * ‖z‖ ^ e := by
    rw [hρ1, Real.div_rpow hzpos.le (by norm_num)]
    have h2 : (2 : ℝ) ^ (-((d : ℝ) + k)) ≤ 2 ^ e := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (q : ℝ) ≤ k := by exact_mod_cast (by omega : q ≤ k)
      rw [he]; linarith
    have h3 : (0 : ℝ) < 2 ^ (-((d : ℝ) + k)) := by positivity
    calc ‖z‖ ^ e / 2 ^ e ≤ ‖z‖ ^ e / 2 ^ (-((d : ℝ) + k)) := div_le_div_of_nonneg_left hzne h3 h2
      _ = 2 ^ ((d : ℝ) + k) * ‖z‖ ^ e := by
        rw [Real.rpow_neg (by norm_num), div_inv_eq_mul, mul_comm]
  have hRd : R ^ d * R ^ (-sigma) = R ^ ((d : ℝ) - sigma) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]; congr 1
  have hfac : 0 ≤ B * ((2 * R) ^ d * omg) := by positivity
  calc CK * ρ1 ^ e * B * ((2 * R) ^ d * omg)
      = (CK * ρ1 ^ e) * (B * ((2 * R) ^ d * omg)) := by ring
    _ ≤ (CK * (2 ^ ((d : ℝ) + k) * ‖z‖ ^ e)) * (B * ((2 * R) ^ d * omg)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1e hCK0) hfac
    _ = C1 * 3 ^ (2 * M) * CK * 2 ^ ((d : ℝ) + k) * 2 ^ d * omg * A * jbracket X ^ (2 * M) *
          (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ e) * L := by
        rw [hB, ← hRd, mul_pow]; ring

end HRS.MS.R26T8A
