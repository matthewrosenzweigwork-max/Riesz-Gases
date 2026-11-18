import HRS.MP.SelfSimP4MolI2

/-!
# Packet MPP4MOL: the mollified dissipation inequality `p4_mollified_ineq` (interface lemma (5) of P4)

`HRS.MP.SelfSimP4Mol.p4_mollified_ineq_proof` has the statement of `HRS.MP.SelfSimP4.p4_mollified_ineq`.
Route (the CepH2 route "mollify the law, not the equation", on `ℝ^{dN}` without periodisation):
the law `μ_r` is mollified by the Gaussian `G_v`, `u = G_v * μ_r`; the weak Fokker-Planck equation with the
test `G_v(x - ·)` gives `∂_t u = a` (`P4MolData.hasDerivAt_u`); an integration by parts against `χ_R Λ`
(`p4m_ibp_identity`, `p4m_fixed_time`) with the commutator term bounded by Young (`p4m_young_pt`) gives the
cut-off inequality (`P4MolData.time_ineq`); `R → ∞` is done by dominated convergence for the free energy and
the cut-off errors (`P4MolData.tendsto_free`, `P4MolData.tendsto_E`) and by Fatou for the dissipation
(`p4m_fatou_chain`); `P4MolData.main` is the abstract (time-clamped) statement.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d : ℕ}

/-- The projection of the time axis onto `[0,T]`. -/
def p4m_clamp (T r : ℝ) : ℝ := max 0 (min r T)

theorem p4m_clamp_continuous (T : ℝ) : Continuous (p4m_clamp T) :=
  continuous_const.max (continuous_id.min continuous_const)

theorem p4m_clamp_mem {T : ℝ} (hT : 0 ≤ T) (r : ℝ) : p4m_clamp T r ∈ Set.Icc (0 : ℝ) T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem p4m_clamp_eq {T r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) : p4m_clamp T r = r := by
  unfold p4m_clamp
  rw [min_eq_left hr.2, max_eq_right hr.1]

theorem p4m_clamp_eventuallyEq {T r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) T) : p4m_clamp T =ᶠ[𝓝 r] id := by
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  exact p4m_clamp_eq ⟨hs.1.le, hs.2.le⟩

theorem p4m_data_of_hyp {N : ℕ} {θ : ℝ} {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    {μ : ℝ → Measure (EucConfig d N)} (hμ : P4FlowHyp θ b T μ) :
    ∃ (W : ℝ → EucConfig d N → ℝ) (Kl : ℝ≥0) (B K M CV : ℝ),
      P4MolData θ T (fun r => b (p4m_clamp T r)) (fun r => V (p4m_clamp T r)) W
        (fun r => μ (p4m_clamp T r)) Kl B K M CV := by
  obtain ⟨Vd, hVdc, hVdd, hVdle, -⟩ := hV.dtime
  obtain ⟨Kl, hKl⟩ := hV.lip
  obtain ⟨B, hB, hbg⟩ := p4m_b_growth hV.cont_b hKl
  obtain ⟨CV, hCV, hVg⟩ := p4m_V_bound hV.cont_V hV.cont_b hV.grad hKl
  obtain ⟨C, hC, hmom⟩ := hμ.mom
  have hmem := p4m_clamp_mem hT
  have hcl := p4m_clamp_continuous T
  refine ⟨fun r x => Vd (p4m_clamp T r) x, Kl, B, Kl, N * C.toReal, CV, ?_⟩
  exact
    { prob := fun r => hμ.prob _
      hm := fun r => (p4m_moment hC (hmom _ (hmem r))).1
      hM := fun r => (p4m_moment hC (hmom _ (hmem r))).2
      narrow := fun g hg hgb => (hμ.narrow g hg hgb).comp_continuous hcl hmem
      bc := hV.cont_b.comp (Continuous.prodMk (hcl.comp continuous_fst) continuous_snd)
      bl := fun r => hKl _ (hmem r)
      hB := hB
      hK := Kl.2
      bg := fun r y => hbg _ (hmem r) y
      Vc := hV.cont_V.comp (Continuous.prodMk (hcl.comp continuous_fst) continuous_snd)
      grad := fun r x => hV.grad _ x
      Vg := fun r x => hVg _ (hmem r) x
      Wc := hVdc.comp (Continuous.prodMk (hcl.comp continuous_fst) continuous_snd)
      Wd := fun r hr x => by
        have h1 := hVdd r x
        have h2 := p4m_clamp_eq (T := T) ⟨hr.1.le, hr.2.le⟩
        have h3 : (fun s => V (p4m_clamp T s) x) =ᶠ[𝓝 r] fun s => V s x := by
          filter_upwards [p4m_clamp_eventuallyEq hr] with s hs
          simp only [id] at hs
          rw [hs]
        rw [h2]
        exact h1.congr_of_eventuallyEq h3
      Wle := fun r x => hVdle _ (hmem r) x
      fp := fun g hg t ht => by
        have e0 : p4m_clamp T 0 = 0 := p4m_clamp_eq ⟨le_rfl, hT⟩
        have et : p4m_clamp T t = t := p4m_clamp_eq ht
        simp only [e0, et]
        rw [hμ.fp g hg t ht]
        congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
        have hr' : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
        simp only [p4m_clamp_eq hr']
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [p4Gen, p4m_clamp_eq hr'] }

/-- **(5) L.**  Mollified dissipation inequality on `ℝ^{dN}` with a time-dependent potential (CepH2 route, no
periodisation, extra term `∫u∂_tV/θ ≤ 0` dropped). -/
theorem p4_mollified_ineq_proof {N : ℕ} {θ : ℝ} (hθ : 0 < θ) {V : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N} {T : ℝ} (hT : 0 ≤ T) (hV : P4PotHyp V b T)
    {μ : ℝ → Measure (EucConfig d N)} (hμ : P4FlowHyp θ b T μ) :
    ∃ C : ℝ, ∀ v : ℝ, 0 < v →
      AEMeasurable (fun r => p4Diss θ (V r) (p4Mol v (μ r))) (volume.restrict (Set.Icc (0 : ℝ) T)) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 → ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ r in Set.Icc (0 : ℝ) t, p4Diss θ (V r) (p4Mol v (μ r)) ≠ ⊤ ∧
        p4Free θ (V t) (p4Mol v (μ t)) +
            θ * (1 - δ) * (∫⁻ r in Set.Icc (0 : ℝ) t, p4Diss θ (V r) (p4Mol v (μ r))).toReal ≤
          p4Free θ (V 0) (p4Mol v (μ 0)) + t * (C * v / δ) := by
  obtain ⟨W, Kl, B, K, M, CV, hD⟩ := p4m_data_of_hyp hT hV hμ
  refine ⟨N * (Kl : ℝ) ^ 2 * ((N * d : ℕ) : ℝ) / (4 * θ), fun v hv => ⟨?_, fun δ hδ hδ1 t ht => ?_⟩⟩
  · have hm := (hD.measurable_diss (θ := θ) hv).aemeasurable (μ := volume.restrict (Set.Icc (0 : ℝ) T))
    refine hm.congr ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
    simp only [p4m_clamp_eq hr]
  · have hmain := hD.main hv hθ hδ hδ1 ht
    have e0 : p4m_clamp T 0 = 0 := p4m_clamp_eq ⟨le_rfl, hT⟩
    have et : p4m_clamp T t = t := p4m_clamp_eq ht
    have hcongr : ∫⁻ r in Set.Icc (0 : ℝ) t, p4Diss θ (V (p4m_clamp T r)) (p4Mol v (μ (p4m_clamp T r))) =
        ∫⁻ r in Set.Icc (0 : ℝ) t, p4Diss θ (V r) (p4Mol v (μ r)) := by
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [p4m_clamp_eq (⟨hr.1, hr.2.trans ht.2⟩ : r ∈ Set.Icc (0 : ℝ) T)]
    simp only [e0, et, hcongr] at hmain
    obtain ⟨h1, h2⟩ := hmain
    refine ⟨h1, ?_⟩
    have hc : t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ * δ)) =
        t * (N * (Kl : ℝ) ^ 2 * ((N * d : ℕ) : ℝ) / (4 * θ) * v / δ) := by
      field_simp
    rw [← hc]
    exact h2

example := (@p4_mollified_ineq_proof : type_of% @HRS.MP.SelfSimP4.p4_mollified_ineq)

end HRS.MP.SelfSimP4Mol
