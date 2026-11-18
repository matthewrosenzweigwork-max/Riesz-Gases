import HRS.MS.R26T8AF09a
import HRS.MS.R26T8AF08
import HRS.MS.CritForceDefs
import HRS.MS.WsPrepAux7

/-!
# S8.2 observed-time layer, packet T8A.F09: exact finite data needed by the native stationary positive-jet estimate

For Schwartz `f` and `j ≤ 2`, the iterate `LIter j f` is `C^{testOrder}`; the weighted square-root projection
`√ρ · projMean (LIter j f)` lies in `MemOsc (Mstar)` with oscillator norm bounded by the Sobolev norm of order
`Mstar := s82FeatureOrder d` (F08), the Sobolev norm is bounded by `oscNorm (Mstar+4)` (F07), and the gradient jets up
to `testOrder d - 1` are bounded by the Sobolev norm of order `Mstar` (F09a, since `testOrder d + d/2 < Mstar`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.Phase2S82

theorem r26t8a_feature_terminal_data (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SchwartzMap (Euc d) ℝ, ∀ j : ℕ, j ≤ 2 →
      ContDiff ℝ (testOrder d) (r26t8a_LIter a beta rho j f) ∧
      MemOsc (HRS.MS.S82BD.s82FeatureOrder d : ℝ)
        (fun x => Real.sqrt (rho x) * HRS.Whole.projMean (HRS.Whole.withDensityReal rho)
          (r26t8a_LIter a beta rho j f) x) ∧
      cbNormVecE (testOrder d - 1) (fun x => gradient (r26t8a_LIter a beta rho j f) x) +
        ENNReal.ofReal (oscNorm (HRS.MS.S82BD.s82FeatureOrder d : ℝ)
          (fun x => Real.sqrt (rho x) * HRS.Whole.projMean (HRS.Whole.withDensityReal rho)
            (r26t8a_LIter a beta rho j f) x)) ≤
        ENNReal.ofReal (C * oscNorm ((HRS.MS.S82BD.s82FeatureOrder d + 4 : ℕ) : ℝ) f) := by
  obtain ⟨C07, hC07, h07⟩ := r26t8a_generator_data d hd a beta ha hbeta rho hrho
    (HRS.MS.S82BD.s82FeatureOrder d)
  obtain ⟨C8, hC8, h8⟩ := r26t8a_sqrt_projection d hd a beta ha hbeta rho hrho
    (HRS.MS.S82BD.s82FeatureOrder d)
  have hnat2 : 2 * (testOrder d - 1 + 1) + d < 2 * HRS.MS.S82BD.s82FeatureOrder d := by
    unfold HRS.MS.S82BD.s82FeatureOrder testOrder
    omega
  have hR : ((2 * (testOrder d - 1 + 1) + d : ℕ) : ℝ) < ((2 * HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) := by
    exact_mod_cast hnat2
  have hM : ((testOrder d - 1 : ℕ) : ℝ) + 1 + (d : ℝ) / 2 < ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) := by
    push_cast at hR
    linarith
  obtain ⟨Cgr, hCgr0, hgr⟩ := r26t8a_f09a_cb d (testOrder d - 1) _ hM
  refine ⟨(Cgr + C8) * C07, mul_nonneg (add_nonneg hCgr0 hC8) hC07, fun f j hj => ?_⟩
  have hsob := (h07 f j hj).2
  have hSS := (h07 f j hj).1
  set g := r26t8a_LIter a beta rho j f with hg
  have hMem : HRS.PDE.ToolboxRd.MemSobolev ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) g := hSS.2 _
  refine ⟨hSS.1.of_le (by first | simp | exact_mod_cast le_top | exact WithTop.coe_le_coe.2 le_top), ?_⟩
  obtain ⟨hmo, hosc⟩ := h8 g hSS
  refine ⟨hmo, ?_⟩
  -- the three estimates
  have hmono : oscNorm ((HRS.MS.S82BD.s82FeatureOrder d + 2 * j : ℕ) : ℝ) f ≤
      oscNorm ((HRS.MS.S82BD.s82FeatureOrder d + 4 : ℕ) : ℝ) f :=
    HRS.Whole.s21p_oscNorm_mono (by exact_mod_cast (by omega : HRS.MS.S82BD.s82FeatureOrder d + 2 * j ≤
      HRS.MS.S82BD.s82FeatureOrder d + 4)) (HRS.Whole.memOsc_schwartz _ f)
  have hO4 : 0 ≤ oscNorm ((HRS.MS.S82BD.s82FeatureOrder d + 4 : ℕ) : ℝ) f := by
    unfold oscNorm
    exact Real.sqrt_nonneg _
  have hsobE : sobolevNormE ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) g ≤
      ENNReal.ofReal (C07 * oscNorm ((HRS.MS.S82BD.s82FeatureOrder d + 4 : ℕ) : ℝ) f) :=
    hsob.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hmono hC07))
  have hcb := hgr g hSS.1 hMem
  have hcbE : cbNormVecE (testOrder d - 1) (fun x => gradient g x) ≤
      ENNReal.ofReal Cgr * sobolevNormE ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) g := by
    refine hcb.trans ?_
    have hE : sobolevNormE ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) g =
        ENNReal.ofReal (HRS.Whole.sobolevNorm ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) g) := by
      unfold sobolevNormE HRS.Whole.sobolevNorm
      rw [if_pos hMem]
    rw [hE, ← ENNReal.ofReal_mul hCgr0]
  calc cbNormVecE (testOrder d - 1) (fun x => gradient g x) +
        ENNReal.ofReal (oscNorm ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ)
          (fun x => Real.sqrt (rho x) * HRS.Whole.projMean (HRS.Whole.withDensityReal rho) g x))
      ≤ ENNReal.ofReal Cgr * sobolevNormE ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) g +
          ENNReal.ofReal C8 * sobolevNormE ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) g :=
        add_le_add hcbE hosc
    _ = ENNReal.ofReal (Cgr + C8) * sobolevNormE ((HRS.MS.S82BD.s82FeatureOrder d : ℕ) : ℝ) g := by
        rw [ENNReal.ofReal_add hCgr0 hC8, add_mul]
    _ ≤ ENNReal.ofReal (Cgr + C8) * ENNReal.ofReal (C07 * oscNorm ((HRS.MS.S82BD.s82FeatureOrder d + 4 : ℕ) : ℝ) f) :=
        r26t8a_f05d_mulL hsobE _
    _ = ENNReal.ofReal (((Cgr + C8) * C07) * oscNorm ((HRS.MS.S82BD.s82FeatureOrder d + 4 : ℕ) : ℝ) f) := by
        rw [← ENNReal.ofReal_mul (add_nonneg hCgr0 hC8)]
        congr 1
        ring

end HRS.MS.R26T8A

end
