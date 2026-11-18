import HRS.MS.R26T8AP11f14
import HRS.MS.R26T8AP10a1

/-!
# S8.2 T8A P11f (part 15): the cut-off source `H(u,y) = θ(u-y) Stil ρ Q u y` is globally `C^k` with Gaussian jets
`θ` smooth, bounded jets, `θ = 0` on `|v| ≤ 1/4`.  This is the input hypothesis of `r26t8a_f6_pot_smooth`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem r26t8a_f15_Stheta {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ' c : ℝ) (hM : 0 ≤ M)
    (hc : 0 < c) :
    ∃ B0 : ℝ, 0 ≤ B0 ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {Q : Euc d → Euc d → ℝ}, Conormal (k + 2) b M σ' A Q →
      ∀ {ρ : Euc d → ℝ}, ContDiff ℝ ∞ ρ → ∀ {Cρ : ℝ}, 0 ≤ Cρ →
      (∀ j ≤ k + 1, ∀ u : Euc d, ‖iteratedFDeriv ℝ j ρ u‖ ≤ Cρ * Real.exp (-c * ‖u‖ ^ 2)) →
      ∀ {θ : Euc d → ℝ}, ContDiff ℝ (k : WithTop ℕ∞) θ → ∀ {Cθ : ℝ}, 0 ≤ Cθ →
      (∀ j ≤ k, ∀ v : Euc d, ‖iteratedFDeriv ℝ j θ v‖ ≤ Cθ) → (∀ v : Euc d, ‖v‖ ≤ 1 / 4 → θ v = 0) →
      ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry (fun u y => θ (u - y) * r26t8a_Stil ρ Q u y)) ∧
      ∀ j ≤ k, ∀ u y : Euc d,
        ‖iteratedFDeriv ℝ j (Function.uncurry (fun u y => θ (u - y) * r26t8a_Stil ρ Q u y)) (u, y)‖ ≤
          (B0 * Cθ * Cρ * A) * Real.exp (-(c / 2) * ‖u‖ ^ 2) * jbracket y ^ M := by
  obtain ⟨BS, hBS0, hBS⟩ := r26t8a_f14_Stil_jets hchi k b M σ' c (d := d)
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_p10a_poly_gauss M hc
  refine ⟨4 ^ k * BS * Cp, by positivity, ?_⟩
  intro A hA Q hQ ρ hρ Cρ hCρ hρb θ hθ Cθ hCθ hθb hθ0
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hQ1 : ContDiffOn ℝ ((k + 2 : ℕ) : WithTop ℕ∞) (Function.uncurry Q) {p | p.1 ≠ p.2} := hQ.1
  have hSt := r26t8a_f12_Stil_contDiffOn hQ1 hρ
  have hth : ContDiff ℝ (k : WithTop ℕ∞) (fun q : Euc d × Euc d => θ (q.1 - q.2)) :=
    hθ.comp (contDiff_fst.sub contDiff_snd)
  have hH : Function.uncurry (fun u y => θ (u - y) * r26t8a_Stil ρ Q u y) =
      fun q : Euc d × Euc d => θ (q.1 - q.2) * Function.uncurry (r26t8a_Stil ρ Q) q := rfl
  -- near the diagonal the function vanishes
  have hzero : ∀ u y : Euc d, ‖u - y‖ < 1 / 4 →
      Function.uncurry (fun u y => θ (u - y) * r26t8a_Stil ρ Q u y) =ᶠ[𝓝 (u, y)] fun _ => (0 : ℝ) := by
    intro u y huy
    have hopen' : IsOpen {q : Euc d × Euc d | ‖q.1 - q.2‖ < 1 / 4} :=
      isOpen_lt (continuous_norm.comp (continuous_fst.sub continuous_snd)) continuous_const
    filter_upwards [hopen'.mem_nhds huy] with q hq
    have hq' : ‖q.1 - q.2‖ < 1 / 4 := hq
    simp only [Function.uncurry, hθ0 _ hq'.le, zero_mul]
  refine ⟨?_, fun j hj u y => ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro q
    by_cases hq : ‖q.1 - q.2‖ < 1 / 4
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero q.1 q.2 hq)
    · have hqm : q ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := by
        show q.1 ≠ q.2
        intro h; rw [h, sub_self, norm_zero] at hq; apply hq; norm_num
      rw [hH]
      exact hth.contDiffAt.mul (hSt.contDiffAt (hopen.mem_nhds hqm))
  · have hnn : 0 ≤ (4 ^ k * BS * Cp * Cθ * Cρ * A) * Real.exp (-(c / 2) * ‖u‖ ^ 2) * jbracket y ^ M := by
      have : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
      positivity
    by_cases huy : ‖u - y‖ < 1 / 4
    · rw [((hzero u y huy).iteratedFDeriv ℝ j).self_of_nhds]
      have h0 : iteratedFDeriv ℝ j (fun _ : Euc d × Euc d => (0 : ℝ)) (u, y) = 0 := by simp
      rw [h0, norm_zero]
      exact hnn
    · have hy4 : 1 / 4 ≤ ‖u - y‖ := not_lt.1 huy
      have hqm : (u, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := by
        show u ≠ y
        intro h; rw [h, sub_self, norm_zero] at hy4; linarith
      rw [hH]
      set pw : ℝ := HRS.MS.Phase2S82.pairWeight M u y with hpw
      set g : ℝ := Real.exp (-c * ‖u‖ ^ 2) with hg
      have hjk : ∀ m ≤ k, ‖iteratedFDeriv ℝ m (fun q : Euc d × Euc d => θ (q.1 - q.2)) (u, y)‖ ≤ Cθ * 2 ^ k := by
        intro m hm
        have h1 := r26t8a_f4_jet_kernel (K := θ) (i := m) (hθ.of_le (by exact_mod_cast hm))
          (B := Cθ) (fun v => hθb m hm v) 0 (u, y)
        have e : (fun q : Euc d × Euc d => θ (q.1 - q.2)) = fun q : Euc d × Euc d => θ (q.1 - q.2 - 0) := by
          funext q; simp
        rw [e]
        refine h1.trans (mul_le_mul_of_nonneg_left ?_ hCθ)
        exact pow_le_pow_right₀ (by norm_num) hm
      have hSj : ∀ m ≤ k, ‖iteratedFDeriv ℝ m (Function.uncurry (r26t8a_Stil ρ Q)) (u, y)‖ ≤
          BS * Cρ * A * g * pw := fun m hm => hBS A hA hQ hρ hCρ hρb m hm u y hy4
      have hmul := r26t8a_f10_jet_mul_on hopen (hth.contDiffOn.of_le (by exact_mod_cast hj))
        (hSt.of_le (by exact_mod_cast hj)) hqm
        (fun m hm => hjk m (hm.trans hj)) (fun m hm => hSj m (hm.trans hj)) (n := j)
      refine hmul.trans ?_
      have h2j : (2 : ℝ) ^ j ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hj
      have hjb : jbracket u ^ M * Real.exp (-c * ‖u‖ ^ 2) ≤ Cp * Real.exp (-(c / 2) * ‖u‖ ^ 2) := by
        refine le_trans ?_ (hCp ‖u‖ (norm_nonneg _))
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (s83_jb_pos u).le (s83_jb_le_one_add u) hM)
          (Real.exp_pos _).le
      have hpw' : pw = jbracket u ^ M * jbracket y ^ M := rfl
      have hg0 : 0 ≤ g := (Real.exp_pos _).le
      have hpw0 : 0 ≤ pw := by
        rw [hpw']; exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
      have hX : 0 ≤ BS * Cρ * A := by positivity
      have hjy0 : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
      calc 2 ^ j * (Cθ * 2 ^ k * (BS * Cρ * A * g * pw))
          ≤ 2 ^ k * (Cθ * 2 ^ k * (BS * Cρ * A * g * pw)) := by
            refine mul_le_mul_of_nonneg_right h2j (by positivity)
        _ = 4 ^ k * Cθ * (BS * Cρ * A) * (jbracket u ^ M * g) * jbracket y ^ M := by
            rw [hpw']
            have : (4 : ℝ) ^ k = 2 ^ k * 2 ^ k := by rw [← mul_pow]; norm_num
            rw [this]; ring
        _ ≤ 4 ^ k * Cθ * (BS * Cρ * A) * (Cp * Real.exp (-(c / 2) * ‖u‖ ^ 2)) * jbracket y ^ M := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjb (by positivity)) hjy0
        _ = (4 ^ k * BS * Cp * Cθ * Cρ * A) * Real.exp (-(c / 2) * ‖u‖ ^ 2) * jbracket y ^ M := by ring

end HRS.MS.R26T8A
