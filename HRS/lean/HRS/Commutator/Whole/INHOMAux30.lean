import HRS.Commutator.Whole.INHOMAux29

/-!
# CMX-INHOM auxiliary 30: Lemma 4.2 for `a ∈ L²` (density)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ} {s : ℝ}

theorem inhom_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Euc d → Euc d) (K : ℝ), SubTransport d s v K →
      ∀ a : Euc d → ℝ, MemLp a 2 volume →
        ENNReal.ofReal |CcommFun (ghiForce s) v a| ≤
          ENNReal.ofReal (C * K) * sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a) := by
  obtain ⟨CS, hCS, hSch⟩ := inhom_schwartz hd hs0 hsd
  refine ⟨CS, hCS, fun v K hv a ha => ?_⟩
  have hK0 := inhom_subTransport_nonneg hv
  obtain ⟨L, F, hF0, hL, -, hK⟩ := id hv
  have hL0 : (0 : ℝ) ≤ L := L.coe_nonneg
  have hα : 0 < alphaE d s := by linarith [inhom_alpha_one hd hs0 hsd]
  obtain ⟨hWm, hW, hWn, hWe⟩ := inhom_W_props hd hs0 hsd (d := d)
  set W1 : ℝ := ∫ z, inhom_W (d := d) s z with hW1
  have hW10 : 0 ≤ W1 := integral_nonneg hWn
  have ham : AEStronglyMeasurable a volume := ha.aestronglyMeasurable
  have ha2 : Integrable (fun x => a x ^ 2) volume := (memLp_two_iff_integrable_sq ham).1 ha
  set B : ℝ := ∫ x, a x ^ 2 with hB
  have hB0 : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  -- the Sobolev norm of `a`
  set S := sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a) with hS
  have hStop : S < ⊤ :=
    lt_of_le_of_lt (inhom_sob_le_L2 ha (by linarith)) ENNReal.ofReal_lt_top
  have hSq : S ^ ((1 : ℝ) / 2) < ⊤ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hStop.ne
  set R : ℝ := (S ^ ((1 : ℝ) / 2)).toReal with hR
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  have hSR : S ^ ((1 : ℝ) / 2) = ENNReal.ofReal R := (ENNReal.ofReal_toReal hSq.ne).symm
  have hSeq : S = ENNReal.ofReal (R ^ 2) := by
    have := inhom_sqrt_mul_sqrt S
    rw [hSR, ← ENNReal.ofReal_mul hR0] at this
    rw [← this]; ring_nf
  -- the real inequality
  have hreal : |CcommFun (ghiForce s) v a| ≤ (CS * K) * R ^ 2 := by
    refine inhom_limit_aux (A := L * W1 * (4 + 3 * B) / 2) (by positivity) hR0 (by positivity) ?_
    intro η hη hη1
    obtain ⟨φ, a', hφ, hint⟩ := inhom_real_schwartz_approx ha hη
    obtain ⟨ha'c, ha'i, ⟨M', hM'⟩, ha'1, ha'2⟩ := inhom_schw_props hφ
    have ha'm : MemLp a' 2 volume := (memLp_two_iff_integrable_sq ha'c.aestronglyMeasurable).2 ha'2
    -- (ii) the difference
    have hcont := inhom_Ccomm_cont hd hs0 hsd hL ham ha'c.aestronglyMeasurable ha2 ha'2 hη hint
    have hint2 : ∫ x, a' x ^ 2 ≤ 2 * B + 2 := by
      have hd2 : Integrable (fun x => (a x - a' x) ^ 2) volume := by
        have : MemLp (fun x => a x - a' x) 2 volume := ha.sub ha'm
        exact (memLp_two_iff_integrable_sq this.aestronglyMeasurable).1 this
      calc ∫ x, a' x ^ 2 ≤ ∫ x, (2 * a x ^ 2 + 2 * (a x - a' x) ^ 2) := by
            refine integral_mono ha'2 ((ha2.const_mul 2).add (hd2.const_mul 2)) fun x => ?_
            simp only
            nlinarith [sq_nonneg (2 * a x - a' x)]
        _ = 2 * B + 2 * ∫ x, (a x - a' x) ^ 2 := by
            rw [integral_add (ha2.const_mul 2) (hd2.const_mul 2), integral_const_mul, integral_const_mul]
        _ ≤ 2 * B + 2 * η ^ 2 := by gcongr
        _ ≤ 2 * B + 2 := by nlinarith
    have hdiff : |CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a'| ≤ (L * W1 * (4 + 3 * B) / 2) * η := by
      refine hcont.trans ?_
      have : L * W1 * η * (2 + B + ∫ x, a' x ^ 2) / 2 ≤ L * W1 * η * (2 + B + (2 * B + 2)) / 2 := by
        gcongr
      refine this.trans (le_of_eq ?_)
      ring
    -- (iii) the Schwartz estimate
    have hsch := hSch v K hv φ a' hφ
    rw [← inhom_sobSqE_eq hφ] at hsch
    set S' := sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 a') with hS'
    have hδmem : MemLp (fun x => a' x - a x) 2 volume := ha'm.sub ha
    have hmink := inhom_sob_minkowski ha hδmem (w := a') (fun x => by ring) (-alphaE d s)
    have hδS : sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 fun x => a' x - a x) ≤
        ENNReal.ofReal (η ^ 2) := by
      refine (inhom_sob_le_L2 hδmem (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
      calc ∫ x, (a' x - a x) ^ 2 = ∫ x, (a x - a' x) ^ 2 := by
            refine integral_congr_ae (Eventually.of_forall fun x => ?_); simp only; ring
        _ ≤ η ^ 2 := hint
    have hS'half : S' ^ ((1 : ℝ) / 2) ≤ ENNReal.ofReal (R + η) := by
      refine hmink.trans ?_
      rw [← hS, hSR, ENNReal.ofReal_add hR0 hη.le]
      gcongr
      calc sobSqE (-alphaE d s) (HRS.PDE.ToolboxRd.fourierL2 fun x => a' x - a x) ^ ((1 : ℝ) / 2)
          ≤ ENNReal.ofReal (η ^ 2) ^ ((1 : ℝ) / 2) := ENNReal.rpow_le_rpow hδS (by norm_num)
        _ = ENNReal.ofReal η := by
            rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
              Real.sqrt_sq hη.le]
    have hS'le : S' ≤ ENNReal.ofReal ((R + η) ^ 2) := by
      calc S' = S' ^ ((1 : ℝ) / 2) * S' ^ ((1 : ℝ) / 2) := (inhom_sqrt_mul_sqrt S').symm
        _ ≤ ENNReal.ofReal (R + η) * ENNReal.ofReal (R + η) := by gcongr
        _ = ENNReal.ofReal ((R + η) ^ 2) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; ring_nf
    have hsch2 : |CcommFun (ghiForce s) v a'| ≤ (CS * K) * (R + η) ^ 2 := by
      have h1 : ENNReal.ofReal |CcommFun (ghiForce s) v a'| ≤
          ENNReal.ofReal ((CS * K) * (R + η) ^ 2) := by
        refine hsch.trans ?_
        calc ENNReal.ofReal (CS * K) * S' ≤ ENNReal.ofReal (CS * K) * ENNReal.ofReal ((R + η) ^ 2) := by
              gcongr
          _ = _ := (ENNReal.ofReal_mul (by positivity)).symm
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
    calc |CcommFun (ghiForce s) v a|
        = |CcommFun (ghiForce s) v a' + (CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a')| := by
          ring_nf
      _ ≤ |CcommFun (ghiForce s) v a'| + |CcommFun (ghiForce s) v a - CcommFun (ghiForce s) v a'| :=
          abs_add_le _ _
      _ ≤ (CS * K) * (R + η) ^ 2 + (L * W1 * (4 + 3 * B) / 2) * η := add_le_add hsch2 hdiff
  -- conclude
  calc ENNReal.ofReal |CcommFun (ghiForce s) v a| ≤ ENNReal.ofReal ((CS * K) * R ^ 2) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (CS * K) * S := by
        rw [hSeq, ENNReal.ofReal_mul (by positivity)]

end HRS.Commutator.Whole
