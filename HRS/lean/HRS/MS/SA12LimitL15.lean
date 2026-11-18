import HRS.MS.SA12LimitL13
import HRS.MS.SA12LimitL14

/-!
# S.A.12 L15: continuity in every real order `m' < m` of the localized solution
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- Monotonicity of the (extended) Sobolev norm in the order. -/
theorem sa12y_sobE_mono {r r' : ℝ} (h : r' ≤ r) (u : Euc d → ℝ) :
    sobolevNormE r' u ≤ sobolevNormE r u := by
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev r u
  · have hu' := HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono h hu
    unfold sobolevNormE
    rw [if_pos hu, if_pos hu']
    exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (sa12l12_S_mono h hu))
  · unfold sobolevNormE
    rw [if_neg hu]
    exact le_top

/-- The order-`m` bound of the difference of two localized values. -/
theorem sa12y_diff_top (χ : Euc d → ℝ) {m : ℕ} {B' : ℝ} (hB'0 : 0 ≤ B') (z : Euc d)
    (G : ℝ → Euc d → ℝ) {τ τ₀ : ℝ}
    (hτ : sobolevNormE (m : ℝ) (fun x => χ (x - z) * G τ x) ≤ ENNReal.ofReal B')
    (hτ₀ : sobolevNormE (m : ℝ) (fun x => χ (x - z) * G τ₀ x) ≤ ENNReal.ofReal B') :
    HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => χ (x - z) * (G τ x - G τ₀ x)) ∧
      sobolevNormE (m : ℝ) (fun x => χ (x - z) * (G τ x - G τ₀ x)) ≤ ENNReal.ofReal (2 * B') := by
  obtain ⟨h1, h1'⟩ := sa12x_sobE_le hB'0 hτ
  obtain ⟨h2, h2'⟩ := sa12x_sobE_le hB'0 hτ₀
  obtain ⟨hmem, hS⟩ := sa12l12_sq_split (m : ℝ) h1 h2 (t := 1) one_pos
  have e : (fun x => χ (x - z) * (G τ x - G τ₀ x)) =
      fun x => χ (x - z) * G τ x - χ (x - z) * G τ₀ x := funext fun x => by ring
  rw [e]
  refine ⟨hmem, sa12x_sobE_of_le (by positivity) hmem ?_⟩
  refine hS.trans ?_
  norm_num
  nlinarith [h1', h2']

-- BEGIN SA12.L15
theorem real_order_continuity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ)
    (G : ℝ → Euc d → ℝ) (hG : IsForwardSolutionRd (D.coeff μ) t φ G) (B : ℝ)
    (hB : ∀ τ ∈ Icc (0 : ℝ) t, ulocNormE m χ (G τ) ≤ ENNReal.ofReal B) :
    ∀ m' : ℝ, m' < m → ∀ z : Euc d, ∀ τ₀ ∈ Icc (0 : ℝ) t, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc (0 : ℝ) t, |τ - τ₀| < δ →
        sobolevNormE m' (fun x => χ (x - z) * (G τ x - G τ₀ x)) ≤ ENNReal.ofReal ε := by
  intro m' hm' z τ₀ hτ₀ ε hε
  set q : ℝ := (mStar d : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; unfold mStar; positivity
  set B' : ℝ := max B 0 with hB'
  have hB'0 : 0 ≤ B' := le_max_right _ _
  obtain ⟨K, hK0, hK⟩ := localized_negative_time hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht
    φ G hG B hB z
  have hBm : ∀ τ ∈ Icc (0 : ℝ) t,
      sobolevNormE (m : ℝ) (fun x => χ (x - z) * G τ x) ≤ ENNReal.ofReal B' := fun τ hτ =>
    (le_iSup (fun w : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - w) * G τ x) z).trans
      ((hB τ hτ).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  have hdiff := fun τ (hτ : τ ∈ Icc (0 : ℝ) t) => sa12y_diff_top χ hB'0 z G (hBm τ hτ) (hBm τ₀ hτ₀)
  by_cases hlow : m' < -q
  · refine ⟨ε / (K + 1), by positivity, fun τ hτ hτd => ?_⟩
    calc sobolevNormE m' (fun x => χ (x - z) * (G τ x - G τ₀ x))
        ≤ sobolevNormE (-q) (fun x => χ (x - z) * (G τ x - G τ₀ x)) := sa12y_sobE_mono hlow.le _
      _ ≤ ENNReal.ofReal (K * |τ - τ₀|) := hK τ hτ τ₀ hτ₀
      _ ≤ ENNReal.ofReal ε := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : |τ - τ₀| * (K + 1) < ε := (lt_div_iff₀ (by positivity)).1 hτd
          nlinarith [abs_nonneg (τ - τ₀)]
  · push Not at hlow
    have hmq : 0 < (m : ℝ) + q := by positivity
    set a : ℝ := ((m : ℝ) - m') / ((m : ℝ) + q) with ha
    set b : ℝ := (m' + q) / ((m : ℝ) + q) with hb
    have ha0 : 0 < a := div_pos (by linarith) hmq
    have hb0 : 0 ≤ b := div_nonneg (by linarith) hmq.le
    set Y : ℝ := (2 * B') ^ b + 1 with hY
    have hY0 : 0 < Y := by rw [hY]; have := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 * B') b; linarith
    refine ⟨(ε / Y) ^ (1 / a) / (K + 1), by positivity, fun τ hτ hτd => ?_⟩
    have hint := fourier_interpolation hd q (m : ℝ) m' hq0 (Nat.cast_nonneg m) hlow hm'.le
      (fun x => χ (x - z) * (G τ x - G τ₀ x)) (hdiff τ hτ).1
    refine hint.trans ?_
    have h1 := hK τ hτ τ₀ hτ₀
    have hKd : 0 ≤ K * |τ - τ₀| := by positivity
    calc _ ≤ (ENNReal.ofReal (K * |τ - τ₀|)) ^ a * (ENNReal.ofReal (2 * B')) ^ b :=
          mul_le_mul' (ENNReal.rpow_le_rpow h1 ha0.le) (ENNReal.rpow_le_rpow (hdiff τ hτ).2 hb0)
      _ = ENNReal.ofReal ((K * |τ - τ₀|) ^ a * (2 * B') ^ b) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hKd ha0.le,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hb0,
            ENNReal.ofReal_mul (Real.rpow_nonneg hKd _)]
      _ ≤ ENNReal.ofReal ε := by
          refine ENNReal.ofReal_le_ofReal ?_
          set E : ℝ := (ε / Y) ^ (1 / a) with hE
          have hE0 : 0 ≤ E := Real.rpow_nonneg (by positivity) _
          have h2 : |τ - τ₀| * (K + 1) < E := (lt_div_iff₀ (by positivity)).1 hτd
          have h3 : K * |τ - τ₀| ≤ E := by nlinarith [abs_nonneg (τ - τ₀)]
          have h4 : (K * |τ - τ₀|) ^ a ≤ ε / Y := by
            calc (K * |τ - τ₀|) ^ a ≤ E ^ a := Real.rpow_le_rpow hKd h3 ha0.le
              _ = ε / Y := by
                  rw [hE, ← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ ha0.ne',
                    Real.rpow_one]
          have h5 : (2 * B') ^ b ≤ Y := by rw [hY]; linarith
          calc (K * |τ - τ₀|) ^ a * (2 * B') ^ b ≤ (ε / Y) * Y :=
                mul_le_mul h4 h5 (Real.rpow_nonneg (by positivity) _) (by positivity)
            _ = ε := by field_simp
-- END SA12.L15

end HRS.MH.AdjointRd.Phase2SA12Limit
