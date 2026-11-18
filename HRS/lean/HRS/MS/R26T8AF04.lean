import HRS.MS.MovOscAux9
import HRS.MS.R26T8AF00
import HRS.MH.ScreenedS5a
import HRS.MS.MovOpAux1

/-!
# S8.2 observed-time layer, packet T8A.F04: rapidly decaying coefficient times a finite-order Sobolev input

`‖σ f‖_{H^r} + ‖σ f‖_{L¹} ≤ C ‖f‖_{H^r}` for `σ` Schwartz and `f` smooth with all Sobolev memberships, and `σ f` is Schwartz.
Route: the merged Sobolev algebra `mova4_sobolevNormE_algebra` (order `m = r + d`), `L¹ ≤ ‖σ‖₂ ‖f‖₂` and `‖f‖₂ ≤ ‖f‖_{H^r}`
(Plancherel), and `smulLeftCLM` with the temperate growth of `f` (Sobolev embedding `rg_sobolev_embedding`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_f04_l2_le {d : ℕ} {r : ℝ} (hr : 0 ≤ r) {u : Euc d → ℝ}
    (hu : HRS.PDE.ToolboxRd.MemSobolev r u) :
    eLpNorm u 2 volume ≤ sobolevNormE r u := by
  have h1 := HRS.MH.Screened.s5a_eLpNorm_sq hu.1
  have h2 := HRS.MH.Screened.s5a_sobolevNormE_sq hu
  have h3 : (eLpNorm u 2 volume) ^ 2 ≤ (sobolevNormE r u) ^ 2 := by
    rw [h1, h2]
    refine lintegral_mono fun ξ => ?_
    have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (HRS.PDE.ToolboxRd.FourierAux.wt ξ ^ r) := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal
        (Real.one_le_rpow (HRS.PDE.ToolboxRd.FourierAux.one_le_wt ξ) hr)
    calc _ = 1 * ENNReal.ofReal (‖HRS.PDE.ToolboxRd.fourierL2 u ξ‖ ^ 2) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' this le_rfl
  exact by
    by_contra hlt
    exact absurd h3 (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hlt)))

theorem r26t8a_rapid_product {d : ℕ} (sigma : SchwartzMap (Euc d) ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, r26t8a_SobSmooth f →
      (∃ h : SchwartzMap (Euc d) ℝ, ⇑h = fun x => sigma x * f x) ∧
      sobolevNormE (r : ℝ) (fun x => sigma x * f x) + eLpNorm (fun x => sigma x * f x) 1 volume ≤
        ENNReal.ofReal C * sobolevNormE (r : ℝ) f := by
  set m : ℝ := (r : ℝ) + d + 1 with hm
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdm : (d : ℝ) / 2 < m := by rw [hm]; linarith
  have hrm : (r : ℝ) ≤ m := by rw [hm]; linarith
  obtain ⟨Ca, hCa, hA⟩ := HRS.MS.MovA4.mova4_sobolevNormE_algebra (d := d) hdm hr0 hrm
  have hσm : HRS.PDE.ToolboxRd.MemSobolev m (⇑sigma) := HRS.MS.MovC1.movc1_memSob_schwartz sigma m
  have hS : sobolevNormE m (⇑sigma) ≠ ⊤ := by
    unfold sobolevNormE; rw [if_pos hσm]; exact ENNReal.ofReal_ne_top
  set S : ℝ := (sobolevNormE m (⇑sigma)).toReal with hSdef
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  have hSe : sobolevNormE m (⇑sigma) = ENNReal.ofReal S := (ENNReal.ofReal_toReal hS).symm
  have hs2 : eLpNorm (⇑sigma) 2 volume ≠ ⊤ := (sigma.memLp 2 volume).eLpNorm_lt_top.ne
  set S2 : ℝ := (eLpNorm (⇑sigma) 2 volume).toReal with hS2def
  have hS20 : 0 ≤ S2 := ENNReal.toReal_nonneg
  have hS2e : eLpNorm (⇑sigma) 2 volume = ENNReal.ofReal S2 := (ENNReal.ofReal_toReal hs2).symm
  refine ⟨Ca * S + S2, by positivity, fun f hf => ⟨?_, ?_⟩⟩
  · -- Schwartz product
    have htg : f.HasTemperateGrowth := by
      refine ⟨hf.1, fun n => ?_⟩
      have hq : (n : ℝ) + d / 2 < (n : ℝ) + d / 2 + 1 := by linarith
      obtain ⟨C, hC0, hC⟩ := HRS.MP.RdGen.rg_sobolev_embedding (d := d) n hq
      have hmem : HRS.PDE.ToolboxRd.MemSobolev ((n : ℝ) + d / 2 + 1) f :=
        HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono (s := ((n + d + 1 : ℕ) : ℝ))
          (by push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]) (hf.2 (n + d + 1))
      refine ⟨0, C * HRS.Whole.sobolevNorm ((n : ℝ) + d / 2 + 1) f, fun x => ?_⟩
      simpa using hC f hf.1 hmem x
    refine ⟨SchwartzMap.smulLeftCLM ℝ f sigma, ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply htg]
    funext x
    simp [mul_comm]
  · have hfm : HRS.PDE.ToolboxRd.MemSobolev (r : ℝ) f := hf.2 r
    have h1 := hA sigma f hσm hfm
    rw [hSe] at h1
    have h2 : eLpNorm (fun x => sigma x * f x) 1 volume ≤ ENNReal.ofReal S2 * sobolevNormE (r : ℝ) f := by
      have hH : eLpNorm ((⇑sigma) • f) 1 volume ≤ eLpNorm (⇑sigma) 2 volume * eLpNorm f 2 volume :=
        eLpNorm_smul_le_mul_eLpNorm (φ := ⇑sigma) (f := f) (p := 2) (q := 2) (r := 1) sigma.continuous.aestronglyMeasurable
          hfm.1.aestronglyMeasurable
      rw [hS2e] at hH
      refine (le_of_eq (by congr 1)).trans (hH.trans ?_)
      exact mul_le_mul' le_rfl (r26t8a_f04_l2_le hr0 hfm)
    calc _ ≤ ENNReal.ofReal Ca * (ENNReal.ofReal S * sobolevNormE (r : ℝ) f) +
          ENNReal.ofReal S2 * sobolevNormE (r : ℝ) f := add_le_add h1 h2
      _ = ENNReal.ofReal (Ca * S + S2) * sobolevNormE (r : ℝ) f := by
        rw [ENNReal.ofReal_add (by positivity) hS20, ENNReal.ofReal_mul hCa.le]; ring

end HRS.MS.R26T8A

end
