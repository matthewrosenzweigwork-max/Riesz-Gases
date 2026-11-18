import HRS.MS.MfeConfAux47

/-!
# S.B.1, packet F6 (part 10): limits as the cut-off is removed, III (the `w`-cut-off term)

`sb1_tendsto_wcut`: `∫_0^t ∫ u w_k ∂_kχ_R → 0` as `R → ∞`, for each `k`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {θ T : ℝ} {b w : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Ψ Wψ : ℝ → EucConfig d N → ℝ} {CΨ Bw Kw CS : ℝ → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem sb1_tendsto_wcut (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hv : 0 < v) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (k : Fin N × Fin d) :
    Tendsto (fun n : ℕ => ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x *
        (w s x k.1 k.2 * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k))) atTop (𝓝 0) := by
  have hM0 := sb1_M_nonneg hP
  have hCu := sb1_Cu_nonneg (d := d) (N := N) hv hM0
  have hcu := hP.cont_u hv
  have hwc' : Continuous (fun p : ℝ × EucConfig d N => w p.1 p.2) := hΨ.wc
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  obtain ⟨L, hL0, hL⟩ := p4m_fderiv_chi_bound (d := d) (N := N)
  suffices key : Tendsto (fun n : ℕ => ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x *
      (w s x k.1 k.2 * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k))) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) t, (0 : ℝ))) by simpa using key
  -- pointwise bound by the tail of `u`
  have hpt : ∀ (n : ℕ) (s : ℝ) (x : EucConfig d N),
      ‖p4Mol v (μ s) x * (w s x k.1 k.2 * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k))‖ ≤
        L * (Bw s + 2 * Kw s) *
          {x : EucConfig d N | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x}.indicator (p4Mol v (μ s)) x := by
    intro n s x
    haveI := hP.prob s
    have hu := p4m_mol_pos hv (hP.hm s) x
    have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hR0 : 0 < (n : ℝ) + 1 := by linarith
    have hBw := (hΨ.nn s).2.1
    have hKw := (hΨ.nn s).2.2.1
    by_cases h0 : fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) = 0
    · rw [h0]
      simp only [mul_zero, norm_zero]
      by_cases hx : x ∈ {x : EucConfig d N | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x}
      · rw [Set.indicator_of_mem hx]; positivity
      · rw [Set.indicator_of_notMem hx]; simp
    · obtain ⟨hq1, hq2⟩ := p4m_fderiv_chi_ne_zero hR0 h0
      have hx : x ∈ {x : EucConfig d N | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x} := hq1
      rw [Set.indicator_of_mem hx]
      have hxn : ‖x‖ ≤ 2 * ((n : ℝ) + 1) := by
        have := p4m_norm_sq_le_q x
        have h1 : ‖x‖ ^ 2 ≤ (2 * ((n : ℝ) + 1)) ^ 2 := by nlinarith
        exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
      have hd := hL ((n : ℝ) + 1) hR0 x k
      have hwk : |w s x k.1 k.2| ≤ Bw s + 2 * Kw s * ((n : ℝ) + 1) := by
        have h1 := p4m_coord_abs_le_norm (w s x) k
        have h2 := hΨ.wg s x
        nlinarith
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hu]
      have hprod : |w s x k.1 k.2| * |fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k)| ≤
          L * (Bw s + 2 * Kw s) := by
        calc |w s x k.1 k.2| * |fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k)|
            ≤ (Bw s + 2 * Kw s * ((n : ℝ) + 1)) * (L / ((n : ℝ) + 1)) := by gcongr
          _ = L * (Bw s / ((n : ℝ) + 1) + 2 * Kw s) := by field_simp
          _ ≤ L * (Bw s + 2 * Kw s) := by
              gcongr
              rw [div_le_iff₀ hR0]
              nlinarith
      calc p4Mol v (μ s) x * (|w s x k.1 k.2| * |fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k)|)
          ≤ p4Mol v (μ s) x * (L * (Bw s + 2 * Kw s)) := by gcongr
        _ = _ := by ring
  refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0 : ℝ) t))
    (fun s => L * (Bw s + 2 * Kw s) * sb1Cu d N v M) ?_ ?_ ?_ ?_
  · intro n
    have hc : Continuous (fun p : ℝ × EucConfig d N => p4Mol v (μ p.1) p.2 *
        (w p.1 p.2 k.1 k.2 * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) p.2 (configBasis d N k))) :=
      hcu.mul (((p4m_continuous_coord k).comp hwc').mul
        ((p4m_cont_deriv_coord (p4m_contDiff_chi (R := (n : ℝ) + 1)) k).comp continuous_snd))
    exact (p4m_cont_param_cs (f := fun s x => p4Mol v (μ s) x *
      (w s x k.1 k.2 * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k))) hc
      (p4m_cs_deriv_coord (p4m_hasCompactSupport_chi (R := (n : ℝ) + 1) (by positivity)) k)
      (fun s x hx => by simp [hx])).aestronglyMeasurable
  · have h1 : IntegrableOn (fun s => Bw s + 2 * Kw s) (Set.Icc (0 : ℝ) t) :=
      (hΨ.intB.mono_set hsub).add ((hΨ.intK.mono_set hsub).const_mul 2)
    exact (h1.const_mul L).mul_const _
  · intro n
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    haveI := hP.prob s
    have hm := hP.hm s
    have hui : Integrable (p4Mol v (μ s)) volume := p4m_integrable_mol hv hm
    have hmeas : MeasurableSet {x : EucConfig d N | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x} :=
      (isClosed_le continuous_const p4m_continuous_q).measurableSet
    have hgi : Integrable (fun x => L * (Bw s + 2 * Kw s) *
        {x : EucConfig d N | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x}.indicator (p4Mol v (μ s)) x) :=
      (hui.indicator hmeas).const_mul _
    have hb := norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall (hpt n s))
    refine hb.trans ?_
    rw [integral_const_mul]
    have hBK : 0 ≤ L * (Bw s + 2 * Kw s) := by
      have := (hΨ.nn s).2.1; have := (hΨ.nn s).2.2.1; positivity
    refine mul_le_mul_of_nonneg_left ?_ hBK
    rw [integral_indicator hmeas]
    refine (setIntegral_le_integral hui (Filter.Eventually.of_forall fun x => (p4m_mol_pos hv hm x).le)).trans ?_
    refine (integral_mono hui (p4m_integrable_q_mol hv hm) fun x => ?_).trans (sb1_int_q_mol_le hv hm (hP.hM s))
    have := p4m_mol_pos hv hm x
    have := p4m_q_nonneg x
    nlinarith
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    haveI := hP.prob s
    have hm := hP.hm s
    have hui : Integrable (p4Mol v (μ s)) volume := p4m_integrable_mol hv hm
    have hBK : 0 ≤ L * (Bw s + 2 * Kw s) := by
      have := (hΨ.nn s).2.1; have := (hΨ.nn s).2.2.1; positivity
    have ht' := (sb1_tail_tendsto hui).const_mul (L * (Bw s + 2 * Kw s))
    rw [mul_zero] at ht'
    refine squeeze_zero_norm (fun n => ?_) ht'
    have hmeas : MeasurableSet {x : EucConfig d N | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x} :=
      (isClosed_le continuous_const p4m_continuous_q).measurableSet
    have hgi : Integrable (fun x => L * (Bw s + 2 * Kw s) *
        {x : EucConfig d N | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x}.indicator (p4Mol v (μ s)) x) :=
      (hui.indicator hmeas).const_mul _
    have hb := norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall (hpt n s))
    refine hb.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_indicator hmeas]

end

end HRS.MS.MfeConf
