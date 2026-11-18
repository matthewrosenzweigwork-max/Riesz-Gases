import HRS.MS.R26T8AP11s
import HRS.MS.R26T8AP06a4

/-!
# S8.2 nonlocal layer: local integrability of the actual local Riesz integrand (P11e, part 6)
For `F` conormal of order `sigma < d`, `y` fixed and `z = x - y != 0`, the function
`v |-> ‖z-v‖^(alpha-d) * 1_{|v|<=2} * |F (y+v) y|` is integrable (two separated singularities, at `v = 0` of order `|v|^-s`, `s < d`, and at `v = z`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

/-- Pointwise pole bound of a conormal function on the diagonal-near fibre. -/
theorem r26t8a_loc_Fbound (d : ℕ) (k b : ℕ) (M sigma : ℝ) (hM : 0 ≤ M) (hsd : sigma < d) (hd : 2 ≤ d) :
    ∃ s : ℝ, 0 < s ∧ s < d ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal k b M sigma A F →
      ∀ y : Euc d, ∃ c : ℝ, 0 ≤ c ∧ ∀ v : Euc d, 0 < ‖v‖ → ‖v‖ ≤ 2 → |F (y + v) y| ≤ c * ‖v‖ ^ (-s) := by
  set sp : ℝ := max sigma 0 with hsp
  have hsp0 : 0 ≤ sp := le_max_right _ _
  have hspd : sp < d := max_lt hsd (by exact_mod_cast (by omega : 0 < d))
  set s : ℝ := sp + ((d : ℝ) - sp) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  have hsd' : s < d := by rw [hs]; linarith
  have hε : 0 < s - sp := by rw [hs]; linarith
  set Mm : ℝ := r26t8a_p06_M (s - sp) b with hMm
  have hMm0 : 0 ≤ Mm := by rw [hMm, r26t8a_p06_M]; have := hε; positivity
  refine ⟨s, hs0, hsd', ?_⟩
  intro A hA F hF y
  -- envelope bound
  have hE : ∀ v : Euc d, 0 < ‖v‖ → ‖v‖ ≤ 2 →
      1 + (min 1 ‖v‖) ^ (-(sigma + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖v‖)|) ^ b ≤
        (1 + Mm + 2 * 2 ^ s) * ‖v‖ ^ (-s) := by
    intro v hv hv2
    have hvs : 0 < ‖v‖ ^ (-s) := Real.rpow_pos_of_pos hv _
    have hL : 1 ≤ (1 + |Real.log (min 1 ‖v‖)|) ^ b :=
      one_le_pow₀ (by linarith [abs_nonneg (Real.log (min 1 ‖v‖))])
    rcases le_total ‖v‖ 1 with h1 | h1
    · rw [min_eq_right h1]
      simp only [Nat.cast_zero, add_zero]
      have hneg : (1 : ℝ) ≤ ‖v‖ ^ (-s) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv h1 (by linarith)
      have h2 : ‖v‖ ^ (-sigma) ≤ ‖v‖ ^ (-sp) :=
        Real.rpow_le_rpow_of_exponent_ge hv h1 (by rw [hsp]; linarith [le_max_left sigma 0])
      have h3 : ‖v‖ ^ (-sp) * (1 + |Real.log ‖v‖|) ^ b ≤ Mm * ‖v‖ ^ (-s) := by
        have := r26t8a_p06_slog b hε hv h1
        have e : ‖v‖ ^ (-sp) = ‖v‖ ^ (-s) * ‖v‖ ^ (s - sp) := by
          rw [← Real.rpow_add hv]; congr 1; ring
        calc ‖v‖ ^ (-sp) * (1 + |Real.log ‖v‖|) ^ b
            = ‖v‖ ^ (-s) * (‖v‖ ^ (s - sp) * (1 + |Real.log ‖v‖|) ^ b) := by rw [e]; ring
          _ ≤ ‖v‖ ^ (-s) * Mm := mul_le_mul_of_nonneg_left this hvs.le
          _ = Mm * ‖v‖ ^ (-s) := mul_comm _ _
      have h4 : ‖v‖ ^ (-sigma) * (1 + |Real.log ‖v‖|) ^ b ≤ Mm * ‖v‖ ^ (-s) :=
        (mul_le_mul_of_nonneg_right h2 (by positivity)).trans h3
      nlinarith [hneg, h4, mul_nonneg (by positivity : (0:ℝ) ≤ 2 * 2 ^ s) hvs.le]
    · rw [min_eq_left h1]
      simp only [Nat.cast_zero, add_zero, Real.one_rpow, Real.log_one, abs_zero, add_zero, one_pow, mul_one]
      have h5 : (2 : ℝ) ^ (-s) ≤ ‖v‖ ^ (-s) :=
        Real.rpow_le_rpow_of_nonpos hv hv2 (by linarith)
      have h6 : (2 : ℝ) ^ s * 2 ^ (-s) = 1 := by
        rw [← Real.rpow_add (by norm_num)]; simp
      have h7 : (1 : ℝ) ≤ 2 ^ s * ‖v‖ ^ (-s) := by
        calc (1 : ℝ) = 2 ^ s * 2 ^ (-s) := h6.symm
          _ ≤ 2 ^ s * ‖v‖ ^ (-s) := mul_le_mul_of_nonneg_left h5 (by positivity)
      nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) s]
  have hjy : 0 < jbracket y := s83_jb_pos y
  have hp1 : 0 ≤ (4 * jbracket y) ^ M := Real.rpow_nonneg (by linarith) _
  have hp2 : 0 ≤ jbracket y ^ M := Real.rpow_nonneg hjy.le _
  have hcE : 0 ≤ 1 + Mm + 2 * 2 ^ s := by
    have := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) s; linarith
  set c0 : ℝ := A * (4 * jbracket y) ^ M * jbracket y ^ M * (1 + Mm + 2 * 2 ^ s) with hc0
  refine ⟨c0, mul_nonneg (mul_nonneg (mul_nonneg hA hp1) hp2) hcE, ?_⟩
  intro v hv hv2
  have hX : y + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = y + v := by module
  have hX' : y + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v = y := by module
  have h0 := hF.2 0 0 (by omega) (y + (1 / 2 : ℝ) • v) v (norm_pos_iff.1 hv)
  rw [hX, hX'] at h0
  have hmj : ‖mixedJet 0 0 F (y + (1 / 2 : ℝ) • v) v‖ = |F (y + v) y| := by
    have : midPair F (y + (1 / 2 : ℝ) • v) v = F (y + v) y := by
      unfold midPair; rw [hX, hX']
    simp only [mixedJet, norm_iteratedFDeriv_zero, this, Real.norm_eq_abs]
  rw [hmj] at h0
  refine h0.trans ?_
  have hpw : pairWeight M (y + v) y ≤ (4 * jbracket y) ^ M * jbracket y ^ M := by
    unfold pairWeight
    have h1 : jbracket (y + v) ≤ 4 * jbracket y := by
      refine (r26t8a_jb_shift' y v).trans ?_
      nlinarith [s83_jb_pos y]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (s83_jb_pos _).le h1 hM) hp2
  have hE' := hE v hv hv2
  have hpw0 : 0 ≤ pairWeight M (y + v) y := by
    unfold pairWeight; exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) hp2
  calc A * pairWeight M (y + v) y * (1 + (min 1 ‖v‖) ^ (-(sigma + ((0 : ℕ) : ℝ))) *
        (1 + |Real.log (min 1 ‖v‖)|) ^ b)
      ≤ A * ((4 * jbracket y) ^ M * jbracket y ^ M) * ((1 + Mm + 2 * 2 ^ s) * ‖v‖ ^ (-s)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hpw hA) hE'
          (add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (le_min zero_le_one hv.le) _)
            (pow_nonneg (by linarith [abs_nonneg (Real.log (min 1 ‖v‖))]) _)))
          (mul_nonneg hA (mul_nonneg hp1 hp2))
    _ = c0 * ‖v‖ ^ (-s) := by rw [hc0]; ring

/-- Local integrability of the dominating function of the actual local Riesz integrand. -/
theorem r26t8a_loc_integrable (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d) :
    ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal k b M sigma A F → ∀ y z : Euc d, z ≠ 0 →
      Integrable (fun v : Euc d => ‖z - v‖ ^ (alpha - (d : ℝ)) *
        (closedBall (0 : Euc d) 2).indicator (fun v => ‖F (y + v) y‖) v) := by
  obtain ⟨s, hs0, hsd', hFb⟩ := r26t8a_loc_Fbound d k b M sigma hM hsd hd
  intro A hA F hF y z hz
  obtain ⟨c, hc0, hc⟩ := hFb A hA F hF y
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  set e : ℝ := alpha - (d : ℝ) with he
  have he0 : e < 0 := by rw [he]; linarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set δ : ℝ := ‖z‖ / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  -- the two integrable pieces
  have hI1 : Integrable ((closedBall (0 : Euc d) 2).indicator (fun v : Euc d => ‖v‖ ^ (-s))) := by
    have h := (r26t8a_p11a_mass d hd (d - s) (by linarith) (by linarith) 3 (by norm_num)).1
    have h' : IntegrableOn (fun v : Euc d => ‖v‖ ^ (-s)) (ball (0 : Euc d) 3) := by
      refine h.congr_fun (fun v _ => ?_) measurableSet_ball
      simp only; congr 1; ring
    exact (h'.mono_set (closedBall_subset_ball (by norm_num))).integrable_indicator measurableSet_closedBall
  have hI2 : Integrable (fun v : Euc d => (ball (0 : Euc d) (‖z‖ + 3)).indicator
      (fun u : Euc d => ‖u‖ ^ e) (z - v)) := by
    have h := (r26t8a_p11a_mass d hd alpha halpha had (‖z‖ + 3) (by positivity)).1
    exact (h.integrable_indicator measurableSet_ball).comp_sub_left z
  set D : Euc d → ℝ := fun v => c * (δ ^ e * (closedBall (0 : Euc d) 2).indicator (fun v : Euc d => ‖v‖ ^ (-s)) v +
    δ ^ (-s) * (ball (0 : Euc d) (‖z‖ + 3)).indicator (fun u : Euc d => ‖u‖ ^ e) (z - v)) with hD
  have hDint : Integrable D := ((hI1.const_mul (δ ^ e)).add (hI2.const_mul (δ ^ (-s)))).const_mul c
  -- measurability
  have hcont : ContinuousOn (fun v : Euc d => F (y + v) y) {v : Euc d | v ≠ 0} := by
    have h1 := hF.1.continuousOn
    refine h1.comp (f := fun v : Euc d => (y + v, y)) ((continuous_const.add continuous_id).prodMk
      continuous_const).continuousOn (fun v hv => ?_)
    simp only [Set.mem_setOf_eq] at hv ⊢
    intro h; apply hv; simpa using h
  have hFm : AEStronglyMeasurable (fun v : Euc d => F (y + v) y) volume := by
    have h := hcont.aestronglyMeasurable (μ := (volume : Measure (Euc d))) (isOpen_ne.measurableSet : MeasurableSet {v : Euc d | v ≠ 0})
    have e1 : (volume : Measure (Euc d)).restrict {v : Euc d | v ≠ 0} = volume := by
      have := restrict_compl_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
      simpa [Set.compl_singleton_eq] using this
    rwa [e1] at h
  have hGm : AEStronglyMeasurable (fun v : Euc d => ‖z - v‖ ^ e *
      (closedBall (0 : Euc d) 2).indicator (fun v => ‖F (y + v) y‖) v) volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact ((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const e).aestronglyMeasurable
    · exact (hFm.norm).indicator measurableSet_closedBall
  have hae : ∀ᵐ v : Euc d, v ≠ 0 := by
    have : (volume : Measure (Euc d)) {(0 : Euc d)}ᶜ = 0 ∨ True := Or.inr trivial
    exact (compl_mem_ae_iff.2 (measure_singleton (0 : Euc d)))
  refine hDint.mono' hGm ?_
  filter_upwards [hae] with v hv
  have hDnn : 0 ≤ D v := by
    rw [hD]; simp only
    refine mul_nonneg hc0 (add_nonneg (mul_nonneg (Real.rpow_nonneg hδ0.le _) ?_) (mul_nonneg (Real.rpow_nonneg hδ0.le _) ?_))
    · exact Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) v
    · exact Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) _
  by_cases hv2 : ‖v‖ ≤ 2
  · have hmem : v ∈ closedBall (0 : Euc d) 2 := by simpa using hv2
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    rw [Set.indicator_of_mem hmem, Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (norm_nonneg _))]
    have hF' := hc v hvpos hv2
    rw [Real.norm_eq_abs] at *
    have hKnn : 0 ≤ ‖z - v‖ ^ e := Real.rpow_nonneg (norm_nonneg _) _
    by_cases hvδ : ‖v‖ ≤ δ
    · have h1 : δ ≤ ‖z - v‖ := by
        have := norm_sub_norm_le z v
        have := norm_sub_le z v
        have h3 : ‖z‖ - ‖v‖ ≤ ‖z - v‖ := by
          have := norm_sub_norm_le z v; linarith
        rw [hδ] at hvδ ⊢; linarith
      have h2 : ‖z - v‖ ^ e ≤ δ ^ e := Real.rpow_le_rpow_of_nonpos hδ0 h1 he0.le
      calc ‖z - v‖ ^ e * ‖F (y + v) y‖ ≤ δ ^ e * (c * ‖v‖ ^ (-s)) :=
            mul_le_mul h2 hF' (norm_nonneg _) (Real.rpow_nonneg hδ0.le _)
        _ ≤ D v := by
            rw [hD]; simp only
            rw [Set.indicator_of_mem hmem]
            have : 0 ≤ c * (δ ^ (-s) * (ball (0 : Euc d) (‖z‖ + 3)).indicator (fun u : Euc d => ‖u‖ ^ e) (z - v)) :=
              mul_nonneg hc0 (mul_nonneg (Real.rpow_nonneg hδ0.le _)
                (Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) _))
            nlinarith
    · push Not at hvδ
      have h2 : ‖v‖ ^ (-s) ≤ δ ^ (-s) := Real.rpow_le_rpow_of_nonpos hδ0 hvδ.le (by linarith)
      have hball : z - v ∈ ball (0 : Euc d) (‖z‖ + 3) := by
        rw [mem_ball, dist_zero_right]
        have := norm_sub_le z v
        linarith
      calc ‖z - v‖ ^ e * ‖F (y + v) y‖ ≤ ‖z - v‖ ^ e * (c * δ ^ (-s)) :=
            mul_le_mul_of_nonneg_left (hF'.trans (mul_le_mul_of_nonneg_left h2 hc0)) hKnn
        _ ≤ D v := by
            rw [hD]; simp only
            rw [Set.indicator_of_mem hball]
            have : 0 ≤ c * (δ ^ e * (closedBall (0 : Euc d) 2).indicator (fun v : Euc d => ‖v‖ ^ (-s)) v) :=
              mul_nonneg hc0 (mul_nonneg (Real.rpow_nonneg hδ0.le _)
                (Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) _))
            nlinarith
  · have hnot : v ∉ closedBall (0 : Euc d) 2 := by simpa using hv2
    rw [Set.indicator_of_notMem hnot, mul_zero, norm_zero]
    exact hDnn

end HRS.MS.R26T8A
