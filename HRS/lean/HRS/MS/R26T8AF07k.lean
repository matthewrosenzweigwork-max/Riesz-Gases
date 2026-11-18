import HRS.MS.R26T8AF07j
import HRS.MS.R26T8AF07h
import HRS.MS.R26T8AF07i

/-!
# S8.2 observed-time layer, packet T8A.F07: the generator iterates `LIter j f`, `j ≤ 2`

`r26t8a_generator_data`: there is `C` such that for every Schwartz `f` and `j ≤ 2`,
`LIter j f` is `SobSmooth` and `sobolevNormE r (LIter j f) ≤ ofReal (C · oscNorm (r + 2j) f)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07k_osc_nonneg (n : ℝ) (f : Euc d → ℝ) : 0 ≤ oscNorm n f := by
  unfold oscNorm
  exact Real.sqrt_nonneg _

theorem r26t8a_generator_data (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap (Euc d) ℝ, ∀ j : ℕ, j ≤ 2 →
      r26t8a_SobSmooth (r26t8a_LIter a beta rho j f) ∧
      sobolevNormE (r : ℝ) (r26t8a_LIter a beta rho j f) ≤
        ENNReal.ofReal (C * oscNorm ((r + 2 * j : ℕ) : ℝ) f) := by
  obtain ⟨C0, hC0, hf0⟩ := r26t8a_f06_sob (d := d) r
  obtain ⟨Cf', hCf0, hf2⟩ := r26t8a_f06_sob (d := d) (r + 2)
  obtain ⟨CJ0, hCJ0, hJ0⟩ := r26t8a_oneJ_sobolev d hd a beta ha hbeta rho hrho r
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_localP_osc d hd a beta ha hbeta rho hrho r
  obtain ⟨K2, hK2, hJ2⟩ := r26t8a_f07j_j2 d hd a beta ha hbeta rho hrho r
  have hF : ∀ j : Fin d, ContDiff ℝ ∞ (fun x => forceMean rho x j) := fun j =>
    contDiff_infty.2 fun N => ((r26t8a_f06_force_comp d hd a beta ha hbeta rho hrho).2 j N).1
  -- the first iterate: `LIter 1 f = p + oneJ f` with `p` Schwartz and `⇑p = localP f`
  have hU1 : ∀ f : SchwartzMap (Euc d) ℝ, ∃ p : SchwartzMap (Euc d) ℝ,
      ⇑p = r26t8a_localP a beta rho ⇑f ∧
      r26t8a_LIter a beta rho 1 f = fun y => ⇑p y + oneJ (critCoeff d a beta rho) ⇑f y := by
    intro f
    obtain ⟨⟨p, hp⟩, -, -⟩ := hCp f
    refine ⟨p, hp, funext fun y => ?_⟩
    show generatorW (critCoeff d a beta rho) 0 ⇑f y = _
    rw [r26t8a_f07b_generator_split, congrFun hp y]
  have hS1 : ∀ f : SchwartzMap (Euc d) ℝ, r26t8a_SobSmooth (r26t8a_LIter a beta rho 1 f) := by
    intro f
    obtain ⟨p, -, hp1⟩ := hU1 f
    rw [hp1]
    exact r26t8a_f07i_sobSmooth_add (r26t8a_f05c_schw_sob p) (hJ0 ⇑f (r26t8a_f05c_schw_sob f)).1
  have hL2 : ∀ f : SchwartzMap (Euc d) ℝ, r26t8a_LIter a beta rho 2 f =
      fun x => r26t8a_localP a beta rho (r26t8a_LIter a beta rho 1 f) x +
        oneJ (critCoeff d a beta rho) (r26t8a_LIter a beta rho 1 f) x := by
    intro f
    funext x
    have h := r26t8a_f07b_LIter_succ a beta rho 1 f
    rw [show (1 + 1 : ℕ) = 2 from rfl] at h
    rw [h, r26t8a_f07b_generator_split]
  have hS2 : ∀ f : SchwartzMap (Euc d) ℝ, r26t8a_SobSmooth (r26t8a_LIter a beta rho 2 f) := by
    intro f
    refine ⟨?_, fun m => ?_⟩
    · rw [hL2 f]
      exact (r26t8a_f07h_contDiff_localP a beta rho hF _ (hS1 f).1).add (hJ0 _ (hS1 f)).1.1
    · obtain ⟨K, -, hK⟩ := r26t8a_f07j_j2 d hd a beta ha hbeta rho hrho m
      exact r26t8a_f05c_mem_of_lt_top (lt_of_le_of_lt (hK f) ENNReal.ofReal_lt_top)
  set C1 : ℝ := Cp + CJ0 * Cf' with hC1
  have hC1nn : 0 ≤ C1 := by rw [hC1]; positivity
  refine ⟨C0 + C1 + K2, by positivity, fun f j hj => ?_⟩
  have hO := r26t8a_f07k_osc_nonneg ((r : ℝ)) f
  interval_cases j
  · -- j = 0
    refine ⟨r26t8a_f05c_schw_sob f, ?_⟩
    show sobolevNormE (r : ℝ) ⇑f ≤ _
    refine (hf0 f).trans ?_
    rw [show (r + 2 * 0 : ℕ) = r by norm_num]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hO)
  · -- j = 1
    refine ⟨hS1 f, ?_⟩
    obtain ⟨p, hpf, hp1⟩ := hU1 f
    rw [hp1]
    have hO2 := r26t8a_f07k_osc_nonneg ((r + 2 : ℕ) : ℝ) f
    have hpbd : sobolevNormE (r : ℝ) ⇑p ≤ ENNReal.ofReal (Cp * oscNorm ((r + 2 : ℕ) : ℝ) f) := by
      rw [hpf]
      exact (hCp f).2.1
    have hJbd := (hJ0 ⇑f (r26t8a_f05c_schw_sob f)).2.1
    have hJ' : sobolevNormE ((r + 1 : ℕ) : ℝ) ⇑f ≤
        ENNReal.ofReal (Cf' * oscNorm ((r + 2 : ℕ) : ℝ) f) :=
      (r26t8a_f05c_sob_mono (by push_cast; linarith) _).trans (hf2 f)
    have hsum := HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_sobolevNormE_add_le (r : ℝ)
      (fun y => ⇑p y) (fun y => oneJ (critCoeff d a beta rho) ⇑f y)
    refine le_trans hsum ?_
    refine le_trans (add_le_add hpbd (hJbd.trans (r26t8a_f05d_mulL hJ' _))) ?_
    rw [← ENNReal.ofReal_mul hCJ0,
      ← ENNReal.ofReal_add (mul_nonneg hCp0 hO2) (mul_nonneg hCJ0 (mul_nonneg hCf0 hO2))]
    rw [show (r + 2 * 1 : ℕ) = r + 2 by norm_num]
    refine ENNReal.ofReal_le_ofReal ?_
    have hC' : C1 * oscNorm ((r + 2 : ℕ) : ℝ) f ≤
        (C0 + C1 + K2) * oscNorm ((r + 2 : ℕ) : ℝ) f :=
      mul_le_mul_of_nonneg_right (by linarith) hO2
    have hexp : C1 * oscNorm ((r + 2 : ℕ) : ℝ) f =
        Cp * oscNorm ((r + 2 : ℕ) : ℝ) f + CJ0 * (Cf' * oscNorm ((r + 2 : ℕ) : ℝ) f) := by
      rw [hC1]
      ring
    linarith
  · -- j = 2
    refine ⟨hS2 f, ?_⟩
    rw [show (r + 2 * 2 : ℕ) = r + 4 by norm_num]
    refine (hJ2 f).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (by linarith) (r26t8a_f07k_osc_nonneg ((r + 4 : ℕ) : ℝ) f)

end HRS.MS.R26T8A

end
