import HRS.MC.S7S7dAux7
import HRS.MC.SEdgeB9
import HRS.MC.SEdgeB13c

/-!
# Packet `s7_S7d_uniform_limits`, helper 8: joint weak convergence of `(B_N, cs_N)`

From `sed_B9a_quadratic_limit_lin_proof` (with the data of `sed_B9_B_window_proof`): for `0 < γ` and smooth
`φ, v` there is a probability measure `ν` on `R × R^p` with
`E F(B_N, cs_N) → ∫ F dν` for all bounded continuous `F`, where `cs_N` is centred under `Q_N` (identified with the
first-marginal centring by exchangeability, exactly as in `B9`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem s7d_B_weak (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 < γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j)) :
    ∃ ν : Measure (ℝ × EuclideanSpace ℝ (Fin p)), IsProbabilityMeasure ν ∧
      ∀ F : ℝ × EuclideanSpace ℝ (Fin p) → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
        Tendsto (fun n : ℕ => ∫ X, F (sed_B d s ρ γ v X, centeredStat (sed_Q d s (n + 1) γ ρ) φ X)
          ∂(sed_Q d s (n + 1) γ ρ)) atTop (𝓝 (∫ x, F x ∂ν)) := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  obtain ⟨B, c, hc, hB⟩ := HRS.MC.SEdge.B2a.sed_B2a_envelope_proof hd hs0 hs hv
  have hvc : ∀ j, Continuous (v j) := fun j => (HRS.MC.SEdge.B9.b9_cont_of_smooth (hv j)).1
  have hmeas := HRS.Q66.q66_hv_measurable hsd hvc
  have hsymm := HRS.Q66.q66_hv_symm hsd v
  obtain ⟨e, he⟩ := HRS.MC.SEdge.B3.sed_B3_onb_proof (by omega) hρ
  have hφ' : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M := fun a =>
    ⟨(HRS.MC.SEdge.B9.b9_cont_of_smooth (hφ a)).2.1, (HRS.MC.SEdge.B9.b9_cont_of_smooth (hφ a)).2.2⟩
  obtain ⟨Ω, mΩ, P, hP, G, Qv, Lin, hdata, hint, hlim⟩ :=
    HRS.MC.SEdge.B9a.sed_B9a_quadratic_limit_lin_proof hd hs0 hs hγ hρ c hc B (HRS.Q66.q66_hv d s v)
      hmeas hsymm hB e he p φ hφ'
  have hQm : Measurable Qv := hdata.2.1
  have hLm : ∀ a, Measurable (Lin a) := hdata.2.2.1
  have hpm : Measurable (fun ω => (Qv ω, (WithLp.toLp 2 fun a => Lin a ω : EuclideanSpace ℝ (Fin p)))) :=
    hQm.prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp (measurable_pi_iff.2 hLm))
  refine ⟨P.map (fun ω => (Qv ω, (WithLp.toLp 2 fun a => Lin a ω : EuclideanSpace ℝ (Fin p)))),
    (Measure.isProbabilityMeasure_map_iff hpm.aemeasurable).2 hP, fun F hFc hFb => ?_⟩
  obtain ⟨M, hM⟩ := hFb
  set F' : ℝ × (Fin p → ℝ) → ℝ := fun bz => F (bz.1, WithLp.toLp 2 bz.2) with hF'
  have hF'c : Continuous F' :=
    hFc.comp (continuous_fst.prodMk ((PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).comp continuous_snd))
  have hF'b : ∃ M', ∀ b z, |F' (b, z)| ≤ M' * (1 + |b|) := by
    refine ⟨|M|, fun b z => ?_⟩
    have h1 : |F' (b, z)| ≤ |M| := (hM _).trans (le_abs_self M)
    have h2 : 0 ≤ |b| := abs_nonneg _
    nlinarith [abs_nonneg M]
  have hlim1 := hlim F' hF'c hF'b
  have hint_eq : ∫ ω, F' (Qv ω, fun a => Lin a ω) ∂P =
      ∫ x, F x ∂(P.map (fun ω => (Qv ω, (WithLp.toLp 2 fun a => Lin a ω : EuclideanSpace ℝ (Fin p))))) := by
    rw [integral_map hpm.aemeasurable hFc.aestronglyMeasurable]
  rw [← hint_eq]
  have h2 := hlim1.comp (tendsto_add_atTop_nat 1)
  have key : ∀ N : ℕ, 1 ≤ N → ∫ X, F' ((N : ℝ) * (modulatedEnergy (HRS.Q66.q66_hv d s v) X (withDensityReal ρ) -
        ∫ Y, modulatedEnergy (HRS.Q66.q66_hv d s v) Y (withDensityReal ρ) ∂(sed_Q d s N γ ρ)),
        fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, φ a (X i) -
          pair (firstMarginal (sed_Q d s N γ ρ)) (φ a))) ∂(sed_Q d s N γ ρ) =
      ∫ X, F (sed_B d s ρ γ v X, centeredStat (sed_Q d s N γ ρ) φ X) ∂(sed_Q d s N γ ρ) := by
    intro N hN
    have h0 : 0 < N := hN
    let D : HRS.Q08.Q08Data d := HRS.MC.SEdge.B9a.b9a_D hd hs0 hs hγ hρ c hc B (HRS.Q66.q66_hv d s v)
      hmeas hsymm hB e he p φ hφ'
    haveI hQprob : IsProbabilityMeasure (sed_Q d s N γ ρ) := HRS.Q08.q08_gibbs_isProb D N hN
    have hcen : ∀ a, ∫ Y, pair (empirical Y) (φ a) ∂(sed_Q d s N γ ρ) =
        pair (firstMarginal (sed_Q d s N γ ρ)) (φ a) := by
      intro a
      obtain ⟨hc1, hm1, M1, hM1⟩ := HRS.MC.SEdge.B9.b9_cont_of_smooth (hφ a)
      have hint : ∀ i : Fin N, Integrable (fun Y : Config d N => φ a (Y i)) (sed_Q d s N γ ρ) := by
        intro i
        refine (integrable_const M1).mono' ((hm1.comp (measurable_pi_apply i)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun Y => ?_)
        simpa [Real.norm_eq_abs] using hM1 (Y i)
      have hex : ∀ i : Fin N, ∫ Y, φ a (Y i) ∂(sed_Q d s N γ ρ) =
          pair (firstMarginal (sed_Q d s N γ ρ)) (φ a) := fun i =>
        HRS.Q08.q08gl_exch_integral D hN (φ a) hm1 i
      simp_rw [pair_empirical h0]
      rw [integral_const_mul, integral_finset_sum _ fun i _ => hint i]
      simp_rw [hex]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp
    have hcs : ∀ X : Config d N, centeredStat (sed_Q d s N γ ρ) φ X =
        WithLp.toLp 2 fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, φ a (X i) -
          pair (firstMarginal (sed_Q d s N γ ρ)) (φ a)) := by
      intro X
      unfold centeredStat
      congr 1
      funext a
      rw [hcen a, pair_empirical h0, one_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [hcs]
    rfl

  refine h2.congr fun n => ?_
  exact key (n + 1) (by omega)

end HRS.MC.Sec7.S7d

end
