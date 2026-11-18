import HRS.MS.R26T8AF01a
import HRS.MS.R26T8AF04
import HRS.MS.MovBridgeAux6
import HRS.MS.ShiftFldAux1

/-!
# S8.2 observed-time layer, packet T8A.F08: the square-root projection maps `H^r` into `Σ^r`

`‖√ρ (f - ∫ f ρ)‖_{Σ^r} ≤ C ‖f‖_{H^r}` for `f` smooth with all Sobolev memberships.
Route: `√ρ` is Gaussian class (F01a), the merged duality bound `mo_bridge2` (`‖b w‖_{Σ^r} ≤ C A ‖w‖_{H^r}`), the mean
`|∫ f ρ| ≤ ‖ρ‖₂ ‖f‖₂ ≤ ‖ρ‖₂ ‖f‖_{H^r}` and the triangle inequality `movc1_osc_add`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.MovOsc HRS.MS.MovC1

theorem r26t8a_sqrt_projection (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, r26t8a_SobSmooth f →
      MemOsc (r : ℝ) (fun x => Real.sqrt (rho x) * HRS.Whole.projMean (HRS.Whole.withDensityReal rho) f x) ∧
      ENNReal.ofReal (oscNorm (r : ℝ) (fun x => Real.sqrt (rho x) *
        HRS.Whole.projMean (HRS.Whole.withDensityReal rho) f x)) ≤
        ENNReal.ofReal C * sobolevNormE (r : ℝ) f := by
  obtain ⟨σ, hσ, rate, hrate, hder⟩ := r26t8a_thermal_sqrt d hd a beta ha hbeta rho hrho
  have hσf : (⇑σ : Euc d → ℝ) = fun x => Real.sqrt (rho x) := funext hσ
  have hG : MovcG (⇑σ) := ⟨σ.smooth ⊤, rate, hrate, fun k => by
    obtain ⟨C, -, hC⟩ := hder k; exact ⟨C, hC⟩⟩
  obtain ⟨A0, hQ⟩ := movc1_G_Q hG r r
  have hA0 : 0 ≤ A0 := by
    have := mova3b2_Q_top hQ 0
    have h2 : 0 ≤ |σ 0| * (1 + ‖(0 : Euc d)‖) ^ r := by positivity
    linarith
  have hQ' : mova3b2_Q (max r ⌈-(r : ℝ)⌉₊) r A0 (⇑σ) := by
    have : max r ⌈-(r : ℝ)⌉₊ = r := by
      have : ⌈-(r : ℝ)⌉₊ = 0 := Nat.ceil_eq_zero.2 (by simp)
      rw [this]; exact max_eq_left (Nat.zero_le _)
    rw [this]; exact hQ
  obtain ⟨Cb, hCb, hbr⟩ := mo_bridge2 (d := d) (r : ℝ) r le_rfl
  -- the mean and the density in `L²`
  have hρS : IsSchwartzDensity rho := by
    rw [critical_thermal_eq d hd a beta ha hbeta hrho]
    have hd1 : 1 ≤ d := by omega
    exact HRS.MS.S85.s85_thermal_schwartz hd (HRS.MS.S82R.s82r_criticalS_pos hd1)
      (HRS.MS.S82R.s82r_criticalS_lt hd1) ha hbeta
  obtain ⟨hρp, ψ, hψ⟩ := hρS
  have hρ2 : eLpNorm rho 2 volume ≠ ⊤ := by
    rw [← hψ]; exact (ψ.memLp 2 volume).eLpNorm_lt_top.ne
  set R2 : ℝ := (eLpNorm rho 2 volume).toReal with hR2
  have hR20 : 0 ≤ R2 := ENNReal.toReal_nonneg
  have hσm : MemOsc (r : ℝ) (⇑σ) := memOsc_schwartz (r : ℝ) σ
  set Os : ℝ := oscNorm (r : ℝ) (⇑σ) with hOs
  have hOs0 : 0 ≤ Os := Real.sqrt_nonneg _
  refine ⟨Cb * A0 + R2 * Os, by positivity, fun f hf => ?_⟩
  have hfm : HRS.PDE.ToolboxRd.MemSobolev (r : ℝ) f := hf.2 r
  -- the sobolev norm as a real number
  have hSf : sobolevNormE (r : ℝ) f = ENNReal.ofReal (Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r : ℝ) f)) := by
    unfold sobolevNormE; rw [if_pos hfm]
  set S : ℝ := Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r : ℝ) f) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hl2 : eLpNorm f 2 volume ≤ ENNReal.ofReal S := by
    rw [← hSf]; exact r26t8a_f04_l2_le (Nat.cast_nonneg r) hfm
  have hf2 : (eLpNorm f 2 volume).toReal ≤ S := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl2
    rwa [ENNReal.toReal_ofReal hS0] at this
  -- the mean
  have hmean : |HRS.Whole.pair (HRS.Whole.withDensityReal rho) f| ≤ R2 * S := by
    unfold HRS.Whole.pair
    rw [HRS.Whole.S79.s79_integral_withDensityReal hρp f]
    have h1 : eLpNorm (fun x => rho x * f x) 1 volume ≤ eLpNorm rho 2 volume * eLpNorm f 2 volume :=
      eLpNorm_smul_le_mul_eLpNorm (φ := rho) (f := f) (p := 2) (q := 2) (r := 1)
        hρp.measurable.aestronglyMeasurable hfm.1.aestronglyMeasurable
    have hρmem : MemLp rho 2 volume := by rw [← hψ]; exact ψ.memLp 2 volume
    have hint : Integrable (fun x => rho x * f x) volume := hρmem.integrable_mul hfm.1
    have h2 : |∫ x, rho x * f x| ≤ (eLpNorm (fun x => rho x * f x) 1 volume).toReal := by
      rw [← Real.norm_eq_abs]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable, eLpNorm_one_eq_lintegral_enorm]
      exact hint.aestronglyMeasurable
    refine h2.trans ?_
    have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hρ2 hfm.1.eLpNorm_lt_top.ne) h1
    rw [ENNReal.toReal_mul] at h3
    exact h3.trans (mul_le_mul_of_nonneg_left hf2 hR20)
  -- the two pieces
  have hb := hbr A0 hA0 (⇑σ) σ.hasTemperateGrowth hQ' f hfm
  have hfun : (fun x => Real.sqrt (rho x) * HRS.Whole.projMean (HRS.Whole.withDensityReal rho) f x) =
      fun x => (σ x * f x) + ((-HRS.Whole.pair (HRS.Whole.withDensityReal rho) f) * σ x) := by
    funext x
    have := congrFun hσf x
    simp only [HRS.Whole.projMean]
    rw [← this]; ring
  have hsm := movc1_osc_smul (r : ℝ) (-HRS.Whole.pair (HRS.Whole.withDensityReal rho) f) hσm
  obtain ⟨hadd, hnorm⟩ := movc1_osc_add (d := d) (r : ℝ) (f := fun x => σ x * f x)
    (g := fun x => (-HRS.Whole.pair (HRS.Whole.withDensityReal rho) f) * σ x) hb.1 hsm.1
  rw [hfun]
  refine ⟨hadd, ?_⟩
  rw [hSf]
  have hnn : 0 ≤ Cb * A0 * S + R2 * S * Os := by positivity
  calc ENNReal.ofReal (oscNorm (r : ℝ) fun x => σ x * f x + (-HRS.Whole.pair (HRS.Whole.withDensityReal rho) f) * σ x)
      ≤ ENNReal.ofReal (Cb * A0 * S + R2 * S * Os) := by
        refine ENNReal.ofReal_le_ofReal (hnorm.trans ?_)
        rw [hsm.2, abs_neg]
        have := hb.2
        have h5 : |HRS.Whole.pair (HRS.Whole.withDensityReal rho) f| * Os ≤ R2 * S * Os :=
          mul_le_mul_of_nonneg_right hmean hOs0
        linarith
    _ = ENNReal.ofReal (Cb * A0 + R2 * Os) * ENNReal.ofReal S := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring

end HRS.MS.R26T8A

end
