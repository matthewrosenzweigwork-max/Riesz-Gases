import HRS.MS.CritForceMom16
import HRS.MS.S82P2Mom

/-!
# S8.2 local Newton layer, packet T8A.R15: two-anchor capped product, port of the merged `s82p_weighted_pin_product`
The merged theorem hides `M' = M` in its existential; this port keeps the same argument (`S82nShortRangePole` and `ShortRangePole` have the same fields)
with `M' = M` exposed as an equality, in the Phase 2 vocabulary (`triplePole`, `pole`, `logN`, `smallRadius`, `pairWeight`, all definitionally equal to the `s82n`/`s82p` ones).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82N HRS.MS.S82P

theorem r26t8a_weighted_pin_product (d : ℕ) (hd : 2 ≤ d)
    (M G c : ℝ) (hM : 0 ≤ M) (hG : 0 < G) (hc : 0 < c)
    (q : Euc d → ℝ) (hq : ShortRangePole d q) :
    ∃ C M' : ℝ, 0 ≤ C ∧ M ≤ M' ∧ M' = M ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsProbDensity rho → HRS.Whole.HasR2GaussianUpper G c rho →
      ∀ N : ℕ, 2 ≤ N → ∀ x y : Euc d, x ≠ y →
        (∫⁻ z, ENNReal.ofReal (jbracket z ^ M * triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ∂HRS.Whole.withDensityReal rho) ≤
          ENNReal.ofReal (C * pairWeight M' x y * pole x y *
            (logN N + 1 + |Real.log (smallRadius x y)|) / N) := by
  have hq : S82nShortRangePole d q := ⟨hq.measurable, hq.smooth, hq.even, hq.nonneg, hq.near, hq.far⟩
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  obtain ⟨K1, hK1, hqK⟩ := s82p_q_le hq
  have hK : 1 ≤ 2 * (1 + K1) := by linarith
  obtain ⟨C3, hC3, hanch⟩ := s82p_anchor hd M G c (2 * (1 + K1)) hM hG.le hc hK
  have hσ : 0 ≤ 1 + (2 : ℝ) ^ s82n_critS d := by positivity
  refine ⟨4 * (1 + (2 : ℝ) ^ s82n_critS d) * C3, M, by positivity, le_rfl, rfl, ?_⟩
  intro ρ hρ hρG N hN x y hxy
  change (∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ∂HRS.Whole.withDensityReal ρ) ≤
          ENNReal.ofReal (4 * (1 + (2 : ℝ) ^ s82n_critS d) * C3 * s82p_pairWeight M x y * s82n_pole x y *
            (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) / N)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hL1 : 1 ≤ s82n_logN N := by
    rw [s82n_logN_eq N (by omega)]; have := Real.log_nonneg hN1r; linarith
  set μ := HRS.Whole.withDensityReal ρ with hμ
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    infer_instance
  haveI : NullSingletonClass μ := by rw [hμ]; unfold HRS.Whole.withDensityReal; infer_instance
  set σ : ℝ := 1 + (2 : ℝ) ^ s82n_critS d with hσdef
  set P : ℝ := s82n_pole x y with hPdef
  have hP := s82p_pole_ge_one x y
  have hc2 : 0 ≤ 2 * σ * P := by positivity
  have hae : ∀ᵐ z ∂μ, z ≠ x ∧ z ≠ y :=
    (Measure.ae_ne μ x).and (Measure.ae_ne μ y)
  set Kc : ℝ := 2 * (1 + K1) with hKc
  have hpt : ∀ᵐ z ∂μ, ENNReal.ofReal (jbracket z ^ M * s82p_triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ≤
        ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole x z)) +
        ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole y z)) := by
    filter_upwards [hae] with z ⟨hzx, hzy⟩
    have hJ : 0 ≤ jbracket z ^ M := Real.rpow_nonneg (s82n_jb_pos z).le _
    have hxz : x - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzx)
    have hyz : y - z ≠ 0 := sub_ne_zero.2 (Ne.symm hzy)
    have hq1 : q (x - z) ≤ K1 * s82n_pole x z := hqK _ hxz
    have hq2 : q (y - z) ≤ K1 * s82n_pole y z := hqK _ hyz
    have hT := s82p_triplePole_le (by omega) x y z hxy
    have hT0 : 0 ≤ s82p_triplePole x y z := by
      have := s82p_pole_ge_one x z; have := s82p_pole_ge_one y z
      unfold s82p_triplePole; positivity
    have halg := s82p_alg K1 σ hK1 hσ N (by omega) (s82n_pole x z) (s82n_pole y z) P
      (s82p_triplePole x y z) (q (x - z)) (q (y - z)) (s82p_pole_ge_one x z) (s82p_pole_ge_one y z)
      hP hq1 hq2 (hq.nonneg _) (hq.nonneg _) hT hT0
    rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add
      (mul_nonneg hc2 (mul_nonneg hJ (s82p_psi_nonneg _ (by positivity) N (by linarith [s82p_pole_ge_one x z]))))
      (mul_nonneg hc2 (mul_nonneg hJ (s82p_psi_nonneg _ (by positivity) N (by linarith [s82p_pole_ge_one y z]))))]
    refine ENNReal.ofReal_le_ofReal ?_
    calc jbracket z ^ M * s82p_triplePole x y z * min 1 ((1 + q (x - z) + q (y - z)) / N)
        = jbracket z ^ M * (s82p_triplePole x y z * min 1 ((1 + q (x - z) + q (y - z)) / N)) := by ring
      _ ≤ jbracket z ^ M * (2 * σ * P * (s82p_psi Kc N (s82n_pole x z) + s82p_psi Kc N (s82n_pole y z))) :=
          mul_le_mul_of_nonneg_left halg hJ
      _ = _ := by ring
  have hIx := (hanch ρ hρ hρG N hN x)
  have hIy := (hanch ρ hρ hρG N hN y)
  calc (∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_triplePole x y z *
          min 1 ((1 + q (x - z) + q (y - z)) / N)) ∂μ)
      ≤ ∫⁻ z, (ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole x z)) +
        ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole y z))) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (2 * σ * P) * ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole x z)) ∂μ +
        ENNReal.ofReal (2 * σ * P) * ∫⁻ z, ENNReal.ofReal (jbracket z ^ M * s82p_psi Kc N (s82n_pole y z)) ∂μ := by
        rw [lintegral_add_left, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (ENNReal.measurable_ofReal.comp (s82p_measurable_jb_psi Kc N M x)).const_mul _
    _ ≤ ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (C3 * jbracket x ^ M * s82n_logN N / N) +
        ENNReal.ofReal (2 * σ * P) * ENNReal.ofReal (C3 * jbracket y ^ M * s82n_logN N / N) := by
        gcongr
    _ = ENNReal.ofReal (2 * σ * P * (C3 * jbracket x ^ M * s82n_logN N / N) +
        2 * σ * P * (C3 * jbracket y ^ M * s82n_logN N / N)) := by
        rw [← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_mul hc2, ← ENNReal.ofReal_add]
        · exact mul_nonneg hc2 (by have := Real.rpow_nonneg (s82n_jb_pos x).le M; positivity)
        · exact mul_nonneg hc2 (by have := Real.rpow_nonneg (s82n_jb_pos y).le M; positivity)
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hjx : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s82n_jb_one_le x) hM
        have hjy : 1 ≤ jbracket y ^ M := Real.one_le_rpow (s82n_jb_one_le y) hM
        have hlog : 0 ≤ |Real.log (s82n_smallRadius x y)| := abs_nonneg _
        unfold s82p_pairWeight
        have e : 2 * σ * P * (C3 * jbracket x ^ M * s82n_logN N / N) +
            2 * σ * P * (C3 * jbracket y ^ M * s82n_logN N / N) =
            (2 * σ * P * C3 * s82n_logN N / N) * (jbracket x ^ M + jbracket y ^ M) := by ring
        rw [e]
        have e2 : 4 * σ * C3 * (jbracket x ^ M * jbracket y ^ M) * P *
            (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) / N =
            (2 * σ * P * C3 * (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) / N) *
              (2 * (jbracket x ^ M * jbracket y ^ M)) := by ring
        have h4 : 4 * (1 + (2 : ℝ) ^ s82n_critS d) * C3 = 4 * σ * C3 := by rw [hσdef]
        rw [h4, e2]
        have hA : 0 ≤ 2 * σ * P * C3 / N := by positivity
        have hB : s82n_logN N ≤ s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)| := by linarith
        have hC : jbracket x ^ M + jbracket y ^ M ≤ 2 * (jbracket x ^ M * jbracket y ^ M) := by
          nlinarith
        have hD : 0 ≤ jbracket x ^ M + jbracket y ^ M := by linarith
        calc 2 * σ * P * C3 * s82n_logN N / N * (jbracket x ^ M + jbracket y ^ M)
            = (2 * σ * P * C3 / N) * s82n_logN N * (jbracket x ^ M + jbracket y ^ M) := by ring
          _ ≤ (2 * σ * P * C3 / N) * (s82n_logN N + 1 + |Real.log (s82n_smallRadius x y)|) *
              (2 * (jbracket x ^ M * jbracket y ^ M)) := by
              gcongr
          _ = _ := by ring

end HRS.MS.R26T8A
