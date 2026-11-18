import HRS.MS.MfeConfAux48

/-!
# S.B.1, packet F6 (part 11): limits as the cut-off is removed, IV (the flux cut-off term)

`sb1_cont_Lam`, `sb1_tendsto_flux`: `∑_k ∫_0^t ∫ Λ ∂_kχ_R J_k → 0` as `R → ∞` (transplant of `P4MolData.tendsto_E`, with the
time-dependent tilt `Ψ` and the time-integrable growth constant `C_Ψ`).
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

theorem sb1_cont_Lam (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hv : 0 < v) :
    Continuous (fun p : ℝ × EucConfig d N => p4m_Lam v θ (μ p.1) (fun y => H y + Ψ p.1 y) p.2) := by
  unfold p4m_Lam
  refine (((hP.cont_u hv).log fun p => (hP.pos_u hv p.1 p.2).ne').add continuous_const).add ?_
  exact ((hP.Vc.comp (Continuous.prodMk continuous_fst continuous_snd)).add hΨ.Ψc).div_const θ

theorem sb1_tendsto_flux (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hv : 0 < v) (hθ : 0 < θ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun n : ℕ => ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x,
      p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
        (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) atTop (𝓝 0) := by
  have hM0 := sb1_M_nonneg hP
  have hCV : 0 ≤ CV := by
    have := hP.Vg 0 0
    have h0 : p4m_q (0 : EucConfig d N) = 0 := by simp [p4m_q]
    simp only [h0] at this
    nlinarith [abs_nonneg (H 0)]
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  obtain ⟨AE, hAE0, hAE⟩ := sb1_Ek_gen (d := d) (N := N) (v := v) (θ := θ) (B := B) (K := K) hv hP.hB hP.hK
  obtain ⟨L, hL0, hL⟩ := p4m_fderiv_chi_bound (d := d) (N := N)
  set b0 : ℝ := 1 / (4 * v) with hb0
  have hb0pos : 0 < b0 := by positivity
  set Cw : ℝ := (∫ w : EucConfig d N, p4m_E b0 w) + 2 * (∫ w : EucConfig d N, p4m_q w * p4m_E b0 w) +
    2 * (∫ w : EucConfig d N, p4m_E b0 w) * M with hCw
  have hI0 : 0 ≤ ∫ w : EucConfig d N, p4m_E b0 w := integral_nonneg fun w => (p4m_E_pos _ _).le
  set a0 : ℝ := |Real.log (p4m_cst d N v)| + (1 + M) / v + 1 with ha0
  have ha00 : 0 ≤ a0 := by positivity
  set AF : ℝ → ℝ := fun s => a0 + (CV + CΨ s) / θ with hAF
  have hAF0 : ∀ s, 0 ≤ AF s := fun s => by
    have := (hΨ.nn s).1
    simp only [hAF]; positivity
  have hcΛ := sb1_cont_Lam hP hΨ hv (θ := θ)
  have hdχ : ∀ (R : ℝ) (k : Fin N × Fin d), Continuous (fun x => fderiv ℝ (p4m_chi R) x (configBasis d N k)) :=
    fun R k => ((p4m_contDiff_chi (R := R)).continuous_fderiv (by norm_num)).clm_apply continuous_const
  set Ehat : ℕ → ℝ → ℝ := fun n s => ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x *
      fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
      (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) with hEhat
  have hEcont : ∀ (n : ℕ) (k : Fin N × Fin d), Continuous (fun s => ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x *
      fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
      (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) := by
    intro n k
    have hEc : Continuous (fun p : ℝ × EucConfig d N =>
        p4m_Lam v θ (μ p.1) (fun y => H y + Ψ p.1 y) p.2 *
          fderiv ℝ (p4m_chi ((n : ℝ) + 1)) p.2 (configBasis d N k) *
          (θ * p4m_gu v (μ p.1) k p.2 - p4m_B v (μ p.1) (b p.1) k p.2)) :=
      (hcΛ.mul ((hdχ _ k).comp continuous_snd)).mul (hP.cont_J hv k)
    exact p4m_cont_param_cs (f := fun s x => p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x *
      fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
      (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) hEc
      (p4m_cs_deriv_coord (p4m_hasCompactSupport_chi (R := (n : ℝ) + 1) (by positivity)) k)
      (fun s x hx => by simp [hx])
  have hEc : ∀ n : ℕ, Continuous (Ehat n) := fun n => continuous_finset_sum _ fun k _ => hEcont n k
  have hsum : ∀ n : ℕ, ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x,
      p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
        (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) = ∫ s in Set.Icc (0 : ℝ) t, Ehat n s := by
    intro n
    rw [integral_finset_sum]
    intro k _
    exact (hEcont n k).integrableOn_Icc (μ := volume)
  simp_rw [hsum]
  -- pointwise bound
  have hbd : ∀ (n : ℕ) (s : ℝ), |Ehat n s| ≤ AE * AF s * L * ∫ x in {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x},
      (1 + p4m_q x) * ∫ y, p4m_E b0 (x - y) ∂(μ s) := by
    intro n s
    haveI := hP.prob s
    have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hR0 : 0 < (n : ℝ) + 1 := by linarith
    have hΨs := (hΨ.nn s).1
    have hF : ∀ x, |p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x| ≤ AF s * (1 + p4m_q x) := by
      intro x
      have hV : ∀ x, |H x + Ψ s x| ≤ (CV + CΨ s) * (1 + p4m_q x) := by
        intro x
        have h1 := hP.Vg s x
        have h2 := hΨ.Ψg s x
        calc |H x + Ψ s x| ≤ |H x| + |Ψ s x| := abs_add_le _ _
          _ ≤ CV * (1 + p4m_q x) + CΨ s * (1 + p4m_q x) := add_le_add h1 h2
          _ = _ := by ring
      have := sb1_Lam_bound hv hθ (hP.hm s) (hP.hM s) hM0 (by linarith : 0 ≤ CV + CΨ s) hV x
      simp only [hAF, ha0]
      calc _ ≤ _ := this
        _ = _ := by ring
    exact hAE (μ s) (hP.hm s) (b s) (hP.bg s) (hP.bc.comp (Continuous.prodMk continuous_const continuous_id))
      _ (AF s) (hAF0 s) hF ((n : ℝ) + 1) L hR hL0 (p4m_chi ((n : ℝ) + 1))
      (fun x k hk => p4m_fderiv_chi_ne_zero hR0 hk) (fun x k => hL _ hR0 x k)
  have hKle : ∀ (n : ℕ) (s : ℝ), (∫ x in {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x},
      (1 + p4m_q x) * ∫ y, p4m_E b0 (x - y) ∂(μ s)) ≤ Cw := by
    intro n s
    haveI := hP.prob s
    have hi := p4m_integrable_weight (hP.hm s) hb0pos
    have hnn : ∀ x : EucConfig d N, 0 ≤ (1 + p4m_q x) * ∫ y, p4m_E b0 (x - y) ∂(μ s) := fun x =>
      mul_nonneg (by have := p4m_q_nonneg x; linarith) (integral_nonneg fun y => (p4m_E_pos _ _).le)
    refine (setIntegral_le_integral hi (Filter.Eventually.of_forall hnn)).trans ?_
    refine (p4m_weight_integral_le (hP.hm s) hb0pos).trans ?_
    have := hP.hM s
    nlinarith
  suffices key : Tendsto (fun n : ℕ => ∫ s in Set.Icc (0 : ℝ) t, Ehat n s) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) t, (0 : ℝ))) by simpa using key
  refine tendsto_integral_of_dominated_convergence (μ := volume.restrict (Set.Icc (0 : ℝ) t))
    (fun s => AE * AF s * L * Cw) ?_ ?_ ?_ ?_
  · intro n
    exact (hEc n).aestronglyMeasurable
  · have h1 : IntegrableOn AF (Set.Icc (0 : ℝ) t) := by
      have : IntegrableOn (fun s => a0 + CV / θ + (1 / θ) * CΨ s) (Set.Icc (0 : ℝ) t) :=
        (integrableOn_const (by simp [Real.volume_Icc]) ).add ((hΨ.intΨ.mono_set hsub).const_mul _)
      refine this.congr_fun (fun s _ => ?_) measurableSet_Icc
      simp only [hAF]; ring
    exact ((h1.const_mul AE).mul_const L).mul_const Cw
  · intro n
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    rw [Real.norm_eq_abs]
    refine (hbd n s).trans ?_
    have hAFs := hAF0 s
    exact mul_le_mul_of_nonneg_left (hKle n s) (by positivity)
  · refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
    haveI := hP.prob s
    have ht' := (sb1_tail_tendsto (p4m_integrable_weight (hP.hm s) hb0pos)).const_mul (AE * AF s * L)
    rw [mul_zero] at ht'
    refine squeeze_zero_norm (fun n => ?_) ht'
    rw [Real.norm_eq_abs]
    exact hbd n s

end

end HRS.MS.MfeConf
