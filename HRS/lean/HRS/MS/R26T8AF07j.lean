import HRS.MS.R26T8AF07i
import HRS.MS.R26T8AF07g
import HRS.MS.R26T8AF07f
import HRS.MS.R26T8AF07b

/-!
# S8.2 observed-time layer, packet T8A.F07 (helper 07j): the second iterate, Sobolev bound with oscillator norm

`sobolevNormE r (LIter 2 f) ≤ ofReal (K · oscNorm (r+4) f)` for Schwartz `f`, with `K` independent of `f`.
Route: `LIter 1 f = localP f + oneJ f = p + J` (`p` Schwartz, F06), `LIter 2 f = localP (p+J) + oneJ (p+J)`,
`localP (p+J) = localP p + localP J` (F07f), and the pieces are bounded by F06 (clause 3), F07g, and F05.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_f07j_j2 (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : SchwartzMap (Euc d) ℝ,
      sobolevNormE (r : ℝ) (r26t8a_LIter a beta rho 2 f) ≤
        ENNReal.ofReal (K * oscNorm ((r + 4 : ℕ) : ℝ) f) := by
  obtain ⟨Cp, hCp0, hCp⟩ := r26t8a_localP_osc d hd a beta ha hbeta rho hrho r
  obtain ⟨Cq, hCq0, hCq⟩ := r26t8a_localP_osc d hd a beta ha hbeta rho hrho (r + 2)
  obtain ⟨Cg, hCg0, hCg⟩ := r26t8a_f07g d hd a beta ha hbeta rho hrho r
  obtain ⟨CJ0, hCJ0, hJ0⟩ := r26t8a_oneJ_sobolev d hd a beta ha hbeta rho hrho r
  obtain ⟨CJ2, hCJ2, hJ2⟩ := r26t8a_oneJ_sobolev d hd a beta ha hbeta rho hrho (r + 2)
  obtain ⟨Cf, hCf0, hf06⟩ := r26t8a_f06_sob (d := d) (r + 4)
  refine ⟨Cp + Cg * (2 * CJ2 + CJ0) * Cf + CJ0 * Cq + CJ0 * CJ2 * Cf,
    by positivity, fun f => ?_⟩
  set O : ℝ := oscNorm ((r + 4 : ℕ) : ℝ) f with hO
  have hO0 : 0 ≤ O := by
    rw [hO]
    unfold oscNorm
    exact Real.sqrt_nonneg _
  have hfk : ∀ s : ℝ, s ≤ (r : ℝ) + 4 → sobolevNormE s ⇑f ≤ ENNReal.ofReal (Cf * O) := fun s hs => by
    refine (r26t8a_f05c_sob_mono hs _).trans ?_
    rw [show (r : ℝ) + 4 = ((r + 4 : ℕ) : ℝ) by push_cast; ring]
    exact hf06 f
  obtain ⟨⟨p, hp⟩, -, hcl3⟩ := hCp f
  obtain ⟨-, hq2, -⟩ := hCq f
  have hpS : r26t8a_SobSmooth ⇑p := r26t8a_f05c_schw_sob p
  obtain ⟨hJS, hJa, hJb⟩ := hJ0 ⇑f (r26t8a_f05c_schw_sob f)
  obtain ⟨-, hJ2a, -⟩ := hJ2 ⇑f (r26t8a_f05c_schw_sob f)
  have e2 : ((r + 2 : ℕ) : ℝ) = (r : ℝ) + 2 := by push_cast; ring
  rw [e2] at hJ2a
  -- the first iterate
  have hU1 : r26t8a_LIter a beta rho 1 f =
      fun y => ⇑p y + oneJ (critCoeff d a beta rho) ⇑f y := by
    funext y
    show generatorW (critCoeff d a beta rho) 0 ⇑f y = _
    rw [r26t8a_f07b_generator_split, congrFun hp y]
  have hU1S : r26t8a_SobSmooth (r26t8a_LIter a beta rho 1 f) := by
    rw [hU1]
    exact r26t8a_f07i_sobSmooth_add hpS hJS
  -- the second iterate splits
  have hL2 : r26t8a_LIter a beta rho 2 f =
      fun x => r26t8a_localP a beta rho (r26t8a_LIter a beta rho 1 f) x +
        oneJ (critCoeff d a beta rho) (r26t8a_LIter a beta rho 1 f) x := by
    funext x
    have h := r26t8a_f07b_LIter_succ a beta rho 1 f
    rw [show (1 + 1 : ℕ) = 2 from rfl] at h
    rw [h, r26t8a_f07b_generator_split]
  have hLU : (fun x => r26t8a_localP a beta rho (r26t8a_LIter a beta rho 1 f) x) =
      fun x => r26t8a_localP a beta rho ⇑p x + r26t8a_localP a beta rho
        (oneJ (critCoeff d a beta rho) ⇑f) x := by
    rw [hU1]
    funext x
    exact r26t8a_f07f_localP_add a beta rho ⇑p _ (r26t8a_f05c_schw_sob p).1 hJS.1 x
  have e1 : ((r + 1 : ℕ) : ℝ) = (r : ℝ) + 1 := by push_cast; ring
  have hX1 : 0 ≤ CJ2 * (Cf * O) := mul_nonneg hCJ2 (mul_nonneg hCf0 hO0)
  have hX2 : 0 ≤ CJ0 * (Cf * O) := mul_nonneg hCJ0 (mul_nonneg hCf0 hO0)
  have hY1 : 0 ≤ Cq * O := mul_nonneg hCq0 hO0
  have hJr2 : sobolevNormE ((r : ℝ) + 2) (oneJ (critCoeff d a beta rho) ⇑f) ≤
      ENNReal.ofReal (CJ2 * (Cf * O)) := by
    refine hJ2a.trans ?_
    rw [ENNReal.ofReal_mul hCJ2]
    exact r26t8a_f05d_mulL (hfk _ (by push_cast; linarith)) _
  have hJE : sobolevNormE (r : ℝ) (r26t8a_Euler (oneJ (critCoeff d a beta rho) ⇑f)) ≤
      ENNReal.ofReal (CJ0 * (Cf * O)) := by
    refine hJb.trans ?_
    rw [ENNReal.ofReal_mul hCJ0]
    exact r26t8a_f05d_mulL (hfk _ (by push_cast; linarith)) _
  have hJr1 : sobolevNormE ((r : ℝ) + 1) (oneJ (critCoeff d a beta rho) ⇑f) ≤
      ENNReal.ofReal (CJ2 * (Cf * O)) :=
    (r26t8a_f05c_sob_mono (by linarith) _).trans hJr2
  -- localP of p
  have hP1 : sobolevNormE (r : ℝ) (fun x => r26t8a_localP a beta rho ⇑p x) ≤
      ENNReal.ofReal (Cp * O) := by
    rw [hp]
    exact hcl3
  -- localP of the oneJ-part
  have hP2 : sobolevNormE (r : ℝ) (fun x => r26t8a_localP a beta rho
      (oneJ (critCoeff d a beta rho) ⇑f) x) ≤ ENNReal.ofReal Cg *
      (sobolevNormE ((r : ℝ) + 2) (oneJ (critCoeff d a beta rho) ⇑f) +
        sobolevNormE (r : ℝ) (r26t8a_Euler (oneJ (critCoeff d a beta rho) ⇑f)) +
        sobolevNormE ((r : ℝ) + 1) (oneJ (critCoeff d a beta rho) ⇑f)) :=
    hCg _ hJS
  have hT2 : sobolevNormE (r : ℝ) (fun x => r26t8a_localP a beta rho
      (oneJ (critCoeff d a beta rho) ⇑f) x) ≤ ENNReal.ofReal Cg *
      (ENNReal.ofReal (CJ2 * (Cf * O)) + ENNReal.ofReal (CJ0 * (Cf * O)) +
        ENNReal.ofReal (CJ2 * (Cf * O))) :=
    hP2.trans (r26t8a_f05d_mulL (add_le_add (add_le_add hJr2 hJE) hJr1) _)
  -- the first-iterate split
  have hloc := HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_sobolevNormE_add_le (r : ℝ)
    (fun x => r26t8a_localP a beta rho ⇑p x)
    (fun x => r26t8a_localP a beta rho (oneJ (critCoeff d a beta rho) ⇑f) x)
  have hB : sobolevNormE (r : ℝ) (fun x => r26t8a_localP a beta rho (r26t8a_LIter a beta rho 1 f) x) ≤
      sobolevNormE (r : ℝ) (fun x => r26t8a_localP a beta rho ⇑p x) +
        sobolevNormE (r : ℝ) (fun x => r26t8a_localP a beta rho
          (oneJ (critCoeff d a beta rho) ⇑f) x) := by
    rw [hLU]
    exact hloc
  -- the oneJ part of the second iterate
  obtain ⟨-, hUa, -⟩ := hJ0 _ hU1S
  have hpbd : sobolevNormE ((r + 1 : ℕ) : ℝ) ⇑p ≤ ENNReal.ofReal (Cq * O) := by
    rw [hp]
    exact (r26t8a_f05c_sob_mono (by push_cast; linarith) _).trans hq2
  have hU1bd : sobolevNormE ((r + 1 : ℕ) : ℝ) (r26t8a_LIter a beta rho 1 f) ≤
      ENNReal.ofReal (Cq * O) + ENNReal.ofReal (CJ2 * (Cf * O)) := by
    rw [hU1]
    refine le_trans (HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_sobolevNormE_add_le
      ((r + 1 : ℕ) : ℝ) ⇑p (oneJ (critCoeff d a beta rho) ⇑f)) ?_
    exact add_le_add hpbd (by rw [e1]; exact hJr1)
  have hT3 : sobolevNormE (r : ℝ) (oneJ (critCoeff d a beta rho) (r26t8a_LIter a beta rho 1 f)) ≤
      ENNReal.ofReal CJ0 * (ENNReal.ofReal (Cq * O) + ENNReal.ofReal (CJ2 * (Cf * O))) :=
    hUa.trans (r26t8a_f05d_mulL hU1bd _)
  have hK : ENNReal.ofReal (Cp * O) + ENNReal.ofReal Cg *
      (ENNReal.ofReal (CJ2 * (Cf * O)) + ENNReal.ofReal (CJ0 * (Cf * O)) +
        ENNReal.ofReal (CJ2 * (Cf * O))) +
      ENNReal.ofReal CJ0 * (ENNReal.ofReal (Cq * O) + ENNReal.ofReal (CJ2 * (Cf * O))) =
      ENNReal.ofReal ((Cp + Cg * (2 * CJ2 + CJ0) * Cf + CJ0 * Cq + CJ0 * CJ2 * Cf) * O) := by
    have h1 : ENNReal.ofReal Cg * (ENNReal.ofReal (CJ2 * (Cf * O)) + ENNReal.ofReal (CJ0 * (Cf * O)) +
        ENNReal.ofReal (CJ2 * (Cf * O))) = ENNReal.ofReal (Cg * (CJ2 * (Cf * O) + CJ0 * (Cf * O) +
        CJ2 * (Cf * O))) := by
      rw [ENNReal.ofReal_mul hCg0, ENNReal.ofReal_add (add_nonneg hX1 hX2) hX1,
        ENNReal.ofReal_add hX1 hX2]
    have h2 : ENNReal.ofReal CJ0 * (ENNReal.ofReal (Cq * O) + ENNReal.ofReal (CJ2 * (Cf * O))) =
        ENNReal.ofReal (CJ0 * (Cq * O + CJ2 * (Cf * O))) := by
      rw [ENNReal.ofReal_mul hCJ0, ENNReal.ofReal_add hY1 hX1]
    rw [h1, h2, ← ENNReal.ofReal_add (mul_nonneg hCp0 hO0)
      (mul_nonneg hCg0 (add_nonneg (add_nonneg hX1 hX2) hX1)),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hCp0 hO0)
        (mul_nonneg hCg0 (add_nonneg (add_nonneg hX1 hX2) hX1)))
        (mul_nonneg hCJ0 (add_nonneg hY1 hX1))]
    congr 1
    ring
  rw [hL2]
  refine le_trans (HRS.MH.AdjointRd.Phase2SA12V3.sa12v3_sobolevNormE_add_le (r : ℝ)
    (fun x => r26t8a_localP a beta rho (r26t8a_LIter a beta rho 1 f) x)
    (fun x => oneJ (critCoeff d a beta rho) (r26t8a_LIter a beta rho 1 f) x)) ?_
  refine le_trans (add_le_add hB le_rfl) ?_
  refine le_trans (add_le_add (add_le_add hP1 hT2) hT3) (le_of_eq hK)

end HRS.MS.R26T8A

end
