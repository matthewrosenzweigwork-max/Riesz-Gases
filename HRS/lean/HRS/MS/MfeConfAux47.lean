import HRS.MS.MfeConfAux46

/-!
# S.B.1, packet F6 (part 9): limits as the cut-off is removed, II (source and `w`-cut-off terms)

* `Sb1Tilt`: the hypotheses on the tilt `Ψ`, its gradient `w`, the time derivative `Wψ` and the integrable constants;
* `sb1_tendsto_src`: `∫_0^t ∫ χ_R u S → ∫_0^t ∫ u S`;
* `sb1_tendsto_wcut`: `∑_k ∫_0^t ∫ u w_k ∂_kχ_R → 0`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- The tilt data: `∇Ψ_s = w_s`, `∂_sΨ = Wψ`, growth bounds with time-integrable constants. -/
structure Sb1Tilt (θ T : ℝ) (b w : ℝ → EucConfig d N → EucConfig d N) (Ψ Wψ : ℝ → EucConfig d N → ℝ)
    (CΨ Bw Kw CS : ℝ → ℝ) : Prop where
  Ψc : Continuous (Function.uncurry Ψ)
  Ψgrad : ∀ r x, HasFDerivAt (Ψ r) (p4InnerL (w r x)) x
  wc : Continuous (Function.uncurry w)
  w1 : ∀ r, ContDiff ℝ 1 (w r)
  dwc : Continuous (Function.uncurry fun r x => sb1div (w r) x)
  Wc : Continuous (Function.uncurry Wψ)
  Wd : ∀ r ∈ Set.Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => Ψ s x) (Wψ r x) r
  nn : ∀ r, 0 ≤ CΨ r ∧ 0 ≤ Bw r ∧ 0 ≤ Kw r ∧ 0 ≤ CS r
  Ψg : ∀ r x, |Ψ r x| ≤ CΨ r * (1 + p4m_q x)
  wg : ∀ r x, ‖w r x‖ ≤ Bw r + Kw r * ‖x‖
  Sg : ∀ r x, |sb1S θ b w Wψ r x| ≤ CS r * (1 + p4m_q x)
  intΨ : IntegrableOn CΨ (Set.Icc 0 T)
  intB : IntegrableOn Bw (Set.Icc 0 T)
  intK : IntegrableOn Kw (Set.Icc 0 T)
  intS : IntegrableOn CS (Set.Icc 0 T)

section
variable {θ T : ℝ} {b w : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Ψ Wψ : ℝ → EucConfig d N → ℝ} {CΨ Bw Kw CS : ℝ → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem sb1_S_cont (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (θ' : ℝ) :
    Continuous (fun p : ℝ × EucConfig d N => sb1S θ' b w Wψ p.1 p.2) := by
  have hbc' : Continuous (fun p : ℝ × EucConfig d N => b p.1 p.2) := hP.bc
  have hwc' : Continuous (fun p : ℝ × EucConfig d N => w p.1 p.2) := hΨ.wc
  unfold sb1S
  exact ((hΨ.dwc.neg.sub (((p4m_continuous_innerL.comp hwc').clm_apply hbc').div_const θ')).add
    ((p4m_continuous_q.comp hwc').div_const θ')).add (hΨ.Wc.div_const θ')

theorem sb1_M_nonneg (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV) : 0 ≤ M := by
  haveI := hP.prob 0
  exact (integral_nonneg fun y => p4m_q_nonneg y).trans (hP.hM 0)

theorem sb1_tendsto_src (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hv : 0 < v) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun n : ℕ => ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_chi ((n : ℝ) + 1) x *
        (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x * sb1S θ b w Wψ s x)) := by
  have hM0 := sb1_M_nonneg hP
  have hCu := sb1_Cu_nonneg (d := d) (N := N) hv hM0
  have hSc := sb1_S_cont hP hΨ θ
  have hcu := hP.cont_u hv
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0 : ℝ) t))
    (fun s => CS s * sb1Cu d N v M) ?_ ?_ ?_ ?_
  · intro n
    have hc : Continuous (fun p : ℝ × EucConfig d N => p4m_chi ((n : ℝ) + 1) p.2 *
        (p4Mol v (μ p.1) p.2 * sb1S θ b w Wψ p.1 p.2)) :=
      ((p4m_contDiff_chi (R := (n : ℝ) + 1)).continuous.comp continuous_snd).mul (hcu.mul hSc)
    exact (p4m_cont_param_cs (f := fun s x => p4m_chi ((n : ℝ) + 1) x *
      (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) hc (p4m_hasCompactSupport_chi (R := (n : ℝ) + 1) (by positivity))
      (fun s x hx => by simp [hx])).aestronglyMeasurable
  · exact (hΨ.intS.mono_set hsub).mul_const _
  · intro n
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    haveI := hP.prob s
    have hm := hP.hm s
    have hCS := (hΨ.nn s).2.2.2
    have hgi : Integrable (fun x => CS s * ((1 + p4m_q x) * p4Mol v (μ s) x)) :=
      (p4m_integrable_q_mol hv hm).const_mul _
    have hpt : ∀ x, ‖p4m_chi ((n : ℝ) + 1) x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)‖ ≤
        CS s * ((1 + p4m_q x) * p4Mol v (μ s) x) := by
      intro x
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (p4m_chi_nonneg _ _),
        abs_of_pos (p4m_mol_pos hv hm x)]
      have h1 := hΨ.Sg s x
      have h2 := p4m_chi_le_one ((n : ℝ) + 1) x
      have h3 := p4m_mol_pos hv hm x
      have h4 := p4m_chi_nonneg ((n : ℝ) + 1) x
      calc p4m_chi ((n : ℝ) + 1) x * (p4Mol v (μ s) x * |sb1S θ b w Wψ s x|)
          ≤ 1 * (p4Mol v (μ s) x * (CS s * (1 + p4m_q x))) := by gcongr
        _ = _ := by ring
    have hb := norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall hpt)
    refine hb.trans ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (sb1_int_q_mol_le hv hm (hP.hM s)) hCS
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    haveI := hP.prob s
    have hm := hP.hm s
    have hu_s : Continuous (p4Mol v (μ s)) := hcu.comp (Continuous.prodMk continuous_const continuous_id)
    have hS_s : Continuous (fun x => sb1S θ b w Wψ s x) := hSc.comp (Continuous.prodMk continuous_const continuous_id)
    refine tendsto_integral_of_dominated_convergence
      (fun x => CS s * ((1 + p4m_q x) * p4Mol v (μ s) x)) ?_ ((p4m_integrable_q_mol hv hm).const_mul _) ?_ ?_
    · intro n
      exact ((p4m_contDiff_chi (R := (n : ℝ) + 1)).continuous.mul (hu_s.mul hS_s)).aestronglyMeasurable
    · intro n
      refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (p4m_chi_nonneg _ _),
        abs_of_pos (p4m_mol_pos hv hm x)]
      have h1 := hΨ.Sg s x
      have h2 := p4m_chi_le_one ((n : ℝ) + 1) x
      have h3 := p4m_mol_pos hv hm x
      have h4 := p4m_chi_nonneg ((n : ℝ) + 1) x
      calc p4m_chi ((n : ℝ) + 1) x * (p4Mol v (μ s) x * |sb1S θ b w Wψ s x|)
          ≤ 1 * (p4Mol v (μ s) x * (CS s * (1 + p4m_q x))) := by gcongr
        _ = _ := by ring
    · refine Filter.Eventually.of_forall fun x => ?_
      obtain ⟨n0, hn0⟩ := exists_nat_gt (p4m_q x)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop n0] with n hn
      have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
      have hq := p4m_q_nonneg x
      have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [p4m_chi_eq_one (R := (n : ℝ) + 1) (by positivity) (by nlinarith), one_mul]

end

end HRS.MS.MfeConf
