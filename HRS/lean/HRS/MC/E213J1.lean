import HRS.MC.S7PIDIIncr
import HRS.MC.E213I2

/-!
# Packet E213J1: family-quantified `s7_PID_incr` (Theorem 2.13, translation-uniform PI-D)

`e213j_incr` is `s7_PID_incr_proof` with the constant `K₁ = L² G + Am²` chosen before the shift `b ≥ 0`, for the
regimes `E213F.shift R b hb` at the fixed horizon `G`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213J

open HRS HRS.Sec7 HRS.MC.Sec7.PID HRS.MC.Sec7.S7PIDI HRS.MC.Sec7.PIE

variable {d : ℕ}

theorem e213j_incr (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (G : ℝ) (hG : 0 < G) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ b : ℝ, ∀ hb : 0 ≤ b, ∀ (p : ℝ → ℝ) (B : ℝ), Measurable p → (∀ u, |p u| ≤ B) →
      ∀ c c' : ℝ, 0 ≤ c → c ≤ c' → c' ≤ G → ∀ k : NonzeroLattice d, ∀ s t : ℝ, c ≤ s → s ≤ t → t ≤ c' →
        (∫ u in Set.Ioc c c', ‖p u • causalVec (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u (modeVec m k) -
            p u • causalVec (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m s u (modeVec m k)‖ ^ 2) ≤
          K₁ * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (t - s) ∧
        (∫ u in Set.Ioc c c', ‖p u • causalVec (HRS.MC.E213F.shift R b hb).D (HRS.MC.E213F.shift R b hb).ρ m t u (modeVec m k)‖ ^ 2) ≤
          K₁ * B ^ 2 * Lattice.jp k.1 ^ (-(2 * (m - 1))) * (c' - c) := by
  obtain ⟨k0, hk1, hk2, hk3, hkst, -⟩ := HRS.MC.Sec7.S7PIDV.S7PIDV_hyp R m hm 1 one_pos
  obtain ⟨L, Ac, Am, Cb, hL, hAc, hAm1, hCb, hU⟩ :=
    HRS.MC.E213I.e213i_V_unif_shift R k0 hk1 hkst m hk2 hk3 G hG
  have hAm0 : 0 ≤ Am := by linarith
  refine ⟨L ^ 2 * G + Am ^ 2, by positivity, fun b hb p B _hp hpB c c' hc hcc' hc'G k s t hcs hst htc' => ?_⟩
  set Rb := HRS.MC.E213F.shift R b hb with hRb
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hpB 0)
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ, Q = Lattice.jp k.1 ^ (-(2 * (m - 1))) := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by rw [hQdef]; exact Real.rpow_nonneg (Torus.jp_pos k.1).le _
  rw [← hQdef]
  have htT : t ≤ G := htc'.trans hc'G
  have hsT : s ≤ G := hst.trans htT
  -- the mode vector: norms and the E_{m-1}-norm
  have hsob : sobAt (m - 1) (modeVec m k) ^ 2 = Q := by
    rw [S7PIDI_sobAt_mode, hQdef, S7PIDI_rpow_sq _ (Torus.jp_pos k.1).le]
  have hnorm_le : ‖modeVec m k‖ ≤ sobAt (m - 1) (modeVec m k) := by
    rw [S7PIDI_norm_modeVec, S7PIDI_sobAt_mode]
    exact Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one k.1) (by linarith)
  have hne2 : ‖modeVec m k‖ ^ 2 ≤ Q :=
    calc ‖modeVec m k‖ ^ 2 ≤ sobAt (m - 1) (modeVec m k) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm_le 2
      _ = Q := hsob
  -- the uniform bound of `V^{t,u}` on `E_m` and the Hölder bound of the difference
  have hVb : ∀ u t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ G →
      ‖Vprop Rb.D Rb.ρ m t' u (modeVec m k)‖ ≤ Am * ‖modeVec m k‖ := fun u t' hu hut htT' =>
    HRS.MC.Sec7.PIE.pie_Vbound_of_finBd Rb.D Rb.ρ m t' u hAm0 (hU b hb u u t' hu le_rfl hut htT').1 (modeVec m k)
  have hVd : ∀ u s' t' : ℝ, 0 ≤ u → u ≤ s' → s' ≤ t' → t' ≤ G →
      ‖Vprop Rb.D Rb.ρ m t' u (modeVec m k) - Vprop Rb.D Rb.ρ m s' u (modeVec m k)‖ ≤
        L * (t' - s') ^ (1 / 2 : ℝ) * sobAt (m - 1) (modeVec m k) := fun u s' t' hu hus hst' htT' =>
    ((hU b hb u s' t' hu hus hst' htT').2.2 (modeVec m k) (S7PIDI_memℓp_fc m k)).1
  have hsmul : ∀ (x : NegSobolev d m) (q : ℝ), ‖q • x‖ = |q| * ‖x‖ := fun x q => by
    rw [norm_smul, Real.norm_eq_abs]
  -- the constants of the two integrals
  have hD0 : 0 ≤ B ^ 2 * Am ^ 2 * Q := mul_nonneg (mul_nonneg (sq_nonneg B) (sq_nonneg Am)) hQ0
  have hA0 : 0 ≤ B ^ 2 * (L ^ 2 * (t - s)) * Q :=
    mul_nonneg (mul_nonneg (sq_nonneg B) (mul_nonneg (sq_nonneg L) (by linarith))) hQ0
  -- pointwise bound of the kernel `p u • V^{t,u} e` on `u ∈ (c,c']`, `u ≤ t`
  have hDb : ∀ u t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ G →
      ‖p u • Vprop Rb.D Rb.ρ m t' u (modeVec m k)‖ ^ 2 ≤ B ^ 2 * Am ^ 2 * Q := by
    intro u t' hu hut htT'
    rw [hsmul]
    have h1 : |p u| * ‖Vprop Rb.D Rb.ρ m t' u (modeVec m k)‖ ≤ B * (Am * ‖modeVec m k‖) :=
      mul_le_mul (hpB u) (hVb u t' hu hut htT') (norm_nonneg _) hB0
    calc (|p u| * ‖Vprop Rb.D Rb.ρ m t' u (modeVec m k)‖) ^ 2 ≤ (B * (Am * ‖modeVec m k‖)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) h1 2
      _ = B ^ 2 * Am ^ 2 * ‖modeVec m k‖ ^ 2 := by ring
      _ ≤ B ^ 2 * Am ^ 2 * Q := mul_le_mul_of_nonneg_left hne2 (by positivity)
  -- second conclusion: pointwise bound on `Ioc c c'`
  have hD2 : ∀ u ∈ Set.Ioc c c',
      ‖p u • causalVec Rb.D Rb.ρ m t u (modeVec m k)‖ ^ 2 ≤ B ^ 2 * Am ^ 2 * Q := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans hc hu.1.le
    by_cases hut : u ≤ t
    · rw [S7PIDI_cv_of_le Rb.D Rb.ρ m t u (modeVec m k) hut]
      exact hDb u t hu0 hut htT
    · rw [S7PIDI_cv_of_not_le Rb.D Rb.ρ m t u (modeVec m k) hut, smul_zero, norm_zero]
      simpa using hD0
  -- first conclusion: pointwise bound by a constant plus an indicator of `(s,t]`
  have hpt1 : ∀ u ∈ Set.Ioc c c',
      ‖p u • causalVec Rb.D Rb.ρ m t u (modeVec m k) - p u • causalVec Rb.D Rb.ρ m s u (modeVec m k)‖ ^ 2 ≤
        B ^ 2 * (L ^ 2 * (t - s)) * Q + (Set.Ioc s t).indicator (fun _ => B ^ 2 * Am ^ 2 * Q) u := by
    intro u hu
    have hu0 : 0 ≤ u := le_trans hc hu.1.le
    by_cases hus : u ≤ s
    · have hut : u ≤ t := hus.trans hst
      rw [S7PIDI_cv_of_le Rb.D Rb.ρ m t u (modeVec m k) hut,
        S7PIDI_cv_of_le Rb.D Rb.ρ m s u (modeVec m k) hus, ← smul_sub, hsmul]
      have hind : u ∉ Set.Ioc s t := fun h => absurd hus (not_le.2 h.1)
      rw [Set.indicator_of_notMem hind, add_zero]
      have hY := hVd u s t hu0 hus hst htT
      have h1 : |p u| * ‖Vprop Rb.D Rb.ρ m t u (modeVec m k) - Vprop Rb.D Rb.ρ m s u (modeVec m k)‖ ≤
          B * (L * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) (modeVec m k)) :=
        mul_le_mul (hpB u) hY (norm_nonneg _) hB0
      have hr2 : ((t - s) ^ (1 / 2 : ℝ)) ^ 2 = t - s := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
        norm_num
      calc (|p u| * ‖Vprop Rb.D Rb.ρ m t u (modeVec m k) - Vprop Rb.D Rb.ρ m s u (modeVec m k)‖) ^ 2
          ≤ (B * (L * (t - s) ^ (1 / 2 : ℝ) * sobAt (m - 1) (modeVec m k))) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg (abs_nonneg _) (norm_nonneg _)) h1 2
        _ = B ^ 2 * L ^ 2 * ((t - s) ^ (1 / 2 : ℝ)) ^ 2 * sobAt (m - 1) (modeVec m k) ^ 2 := by ring
        _ = B ^ 2 * (L ^ 2 * (t - s)) * Q := by rw [hr2, hsob]; ring
    · have hsu : s < u := lt_of_not_ge hus
      rw [S7PIDI_cv_of_not_le Rb.D Rb.ρ m s u (modeVec m k) hus, smul_zero, sub_zero]
      by_cases hut : u ≤ t
      · rw [S7PIDI_cv_of_le Rb.D Rb.ρ m t u (modeVec m k) hut,
          Set.indicator_of_mem (show u ∈ Set.Ioc s t from ⟨hsu, hut⟩)]
        have := hDb u t hu0 hut htT
        linarith
      · rw [S7PIDI_cv_of_not_le Rb.D Rb.ρ m t u (modeVec m k) hut, smul_zero, norm_zero,
          Set.indicator_of_notMem (show u ∉ Set.Ioc s t from fun h => hut h.2), add_zero]
        calc (0 : ℝ) ^ 2 = 0 := by norm_num
          _ ≤ B ^ 2 * (L ^ 2 * (t - s)) * Q := hA0
  -- the integrals of the majorant on `Ioc c c'`
  have hlen : volume.real (Set.Ioc c c') = c' - c := Real.volume_real_Ioc_of_le hcc'
  have hi1 : Integrable (fun _ : ℝ => B ^ 2 * (L ^ 2 * (t - s)) * Q) (volume.restrict (Set.Ioc c c')) :=
    integrableOn_const measure_Ioc_lt_top.ne
  have hi2 : Integrable ((Set.Ioc s t).indicator (fun _ : ℝ => B ^ 2 * Am ^ 2 * Q))
      (volume.restrict (Set.Ioc c c')) :=
    (integrableOn_const (C := B ^ 2 * Am ^ 2 * Q) measure_Ioc_lt_top.ne).indicator measurableSet_Ioc
  have hind : (volume.restrict (Set.Ioc c c')).real (Set.Ioc s t) = t - s := by
    simp only [measureReal_def]
    rw [Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.2 (Set.Ioc_subset_Ioc hcs htc'),
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
  have hcalc1 : ∫ u in Set.Ioc c c', (B ^ 2 * (L ^ 2 * (t - s)) * Q +
      (Set.Ioc s t).indicator (fun _ => B ^ 2 * Am ^ 2 * Q) u) =
      B ^ 2 * (L ^ 2 * (t - s)) * Q * (c' - c) + B ^ 2 * Am ^ 2 * Q * (t - s) := by
    rw [integral_add hi1 hi2, setIntegral_const, integral_indicator_const _ measurableSet_Ioc, hind,
      hlen, smul_eq_mul, smul_eq_mul]
    ring
  have hconst : ∫ _ in Set.Ioc c c', B ^ 2 * Am ^ 2 * Q = (c' - c) * (B ^ 2 * Am ^ 2 * Q) := by
    rw [setIntegral_const, hlen, smul_eq_mul, mul_comm]
  -- first conclusion
  have hint1 : ∫ u in Set.Ioc c c', ‖p u • causalVec Rb.D Rb.ρ m t u (modeVec m k) -
      p u • causalVec Rb.D Rb.ρ m s u (modeVec m k)‖ ^ 2 ≤
      ∫ u in Set.Ioc c c', (B ^ 2 * (L ^ 2 * (t - s)) * Q +
        (Set.Ioc s t).indicator (fun _ => B ^ 2 * Am ^ 2 * Q) u) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _) (hi1.add hi2)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => hpt1 u hu))
  -- second conclusion
  have hint2 : ∫ u in Set.Ioc c c', ‖p u • causalVec Rb.D Rb.ρ m t u (modeVec m k)‖ ^ 2 ≤
      ∫ _ in Set.Ioc c c', B ^ 2 * Am ^ 2 * Q :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => sq_nonneg _)
      (integrableOn_const (C := B ^ 2 * Am ^ 2 * Q) measure_Ioc_lt_top.ne)
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => hD2 u hu))
  have hK0 : (0 : ℝ) ≤ L ^ 2 * G + Am ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · refine le_trans hint1 (le_trans (le_of_eq hcalc1) ?_)
    have h3 : 0 ≤ B ^ 2 * (L ^ 2 * (t - s)) * Q * (G - (c' - c)) :=
      mul_nonneg hA0 (by linarith)
    nlinarith [h3]
  · refine le_trans hint2 (le_trans (le_of_eq hconst) ?_)
    have h4 : 0 ≤ L ^ 2 * G * B ^ 2 * Q * (c' - c) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg L) hG.le) (sq_nonneg B)) hQ0)
        (by linarith)
    nlinarith [h4]


end HRS.MC.E213J

end
