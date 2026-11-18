import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB2a
import HRS.MC.SEdgeB3
import HRS.MC.SEdgeB8b
import HRS.MC.SEdgeB9a
import HRS.MC.SEdgeB15a

/-!
# Packet B9: `sed_B9_B_window` (relocation)

Route: `sed_B9a_quadratic_limit_lin_proof` with `F(b,z) = b psi(z)` and `h = h_v` (envelope B2a, ONB B3),
evaluation of the limit by `sed_B8b_chaos_ibp_proof`, `sed_Cmat = susceptibilityCov` (B15a), and the
identification of the first-marginal centring with the `E_Q mu_N` centring by exchangeability.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B9

open HRS.Sec7
open HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

theorem b9_cont_of_smooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Continuous f ∧ Measurable f ∧ ∃ M, ∀ x, |f x| ≤ M := by
  obtain ⟨C, hC⟩ := HRS.MC.SEdge.B15a.b15a_bound hf
  exact ⟨HRS.MC.SEdge.B15a.b15a_continuous hf, (HRS.MC.SEdge.B15a.b15a_continuous hf).measurable,
    C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

theorem sed_B9_B_window_proof (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {p : ℕ} {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 2 ψ) :
    Tendsto (fun N : ℕ => ∫ X, sed_B d s ρ β v X * ψ (centeredStat (sed_Q d s N β ρ) φ X)
        ∂(sed_Q d s N β ρ)) atTop
      (𝓝 ((1 / 2) * ∑ b, ∑ c,
        sed_Qt d s ρ v (responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ b))
            (responseInverse (periodicRiesz d s) (withDensityReal ρ) β (φ c)) *
          ∫ z, iteratedFDeriv ℝ 2 ψ z ![stdVec b, stdVec c]
            ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)))) := by
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    linarith
  obtain ⟨B, c, hc, hB⟩ := HRS.MC.SEdge.B2a.sed_B2a_envelope_proof hd hs0 hs hv
  have hvc : ∀ j, Continuous (v j) := fun j => (b9_cont_of_smooth (hv j)).1
  have hmeas := Q66.q66_hv_measurable hsd hvc
  have hsymm := Q66.q66_hv_symm hsd v
  obtain ⟨e, he⟩ := HRS.MC.SEdge.B3.sed_B3_onb_proof (by omega) hρ
  have hφ' : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M := fun a =>
    ⟨(b9_cont_of_smooth (hφ a)).2.1, (b9_cont_of_smooth (hφ a)).2.2⟩
  obtain ⟨Ω, mΩ, P, hP, G, Qv, Lin, hdata, hint, hlim⟩ :=
    HRS.MC.SEdge.B9a.sed_B9a_quadratic_limit_lin_proof hd hs0 hs hβ hρ c hc B (Q66.q66_hv d s v)
      hmeas hsymm hB e he p φ hφ'
  obtain ⟨hlaw, hibp⟩ := HRS.MC.SEdge.B8b.sed_B8b_chaos_ibp_proof hd hs0 hs hβ hρ hc hmeas hsymm hB he
    hφ' P G Qv Lin hdata
  -- test function
  have hψc : Continuous ψ := hψ.1.continuous
  obtain ⟨Mψ, hMψ⟩ : ∃ M, ∀ x, ‖ψ x‖ ≤ M := by
    obtain ⟨M, hM⟩ := hψ.2 0 (Nat.zero_le _)
    refine ⟨M, fun x => ?_⟩
    have := hM ⟨x, rfl⟩
    simpa [norm_iteratedFDeriv_zero] using this
  have hFc : Continuous (fun bz : ℝ × (Fin p → ℝ) => bz.1 * ψ (WithLp.toLp 2 bz.2)) :=
    continuous_fst.mul (hψc.comp ((PiLp.continuous_toLp 2 _).comp continuous_snd))
  have hFb : ∃ M, ∀ b z, |(fun bz : ℝ × (Fin p → ℝ) => bz.1 * ψ (WithLp.toLp 2 bz.2)) (b, z)| ≤
      M * (1 + |b|) := by
    refine ⟨|Mψ|, fun b z => ?_⟩
    show |b * ψ (WithLp.toLp 2 z)| ≤ |Mψ| * (1 + |b|)
    rw [abs_mul]
    have h1 : |ψ (WithLp.toLp 2 z)| ≤ |Mψ| := by
      have := hMψ (WithLp.toLp 2 z)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_abs_self _)
    have h2 : 0 ≤ |b| := abs_nonneg _
    nlinarith [abs_nonneg Mψ, abs_nonneg (ψ (WithLp.toLp 2 z))]
  have hlim1 := hlim _ hFc hFb
  -- the limit value
  have hCmat : sed_Cmat d s β ρ φ = Matrix.of fun a b =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (φ a) (φ b) := by
    ext a b
    exact (HRS.MC.SEdge.B15a.sed_B15a_bridge_cov_proof hd hs0 hs hβ.le hρ hφ).1 a b
  have hval := (hibp ψ hψ)
  rw [← hCmat] at hval
  have hlimeq : ∫ ω, (fun bz : ℝ × (Fin p → ℝ) => bz.1 * ψ (WithLp.toLp 2 bz.2))
      (Qv ω, fun a => Lin a ω) ∂P = _ := hval
  rw [hlimeq] at hlim1
  refine hlim1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have h0 : 0 < N := hN
  let D : HRS.Q08.Q08Data d := HRS.MC.SEdge.B9a.b9a_D hd hs0 hs hβ hρ c hc B (Q66.q66_hv d s v)
    hmeas hsymm hB e he p φ hφ'
  haveI hQprob : IsProbabilityMeasure (sed_Q d s N β ρ) := HRS.Q08.q08_gibbs_isProb D N hN
  have hcen : ∀ a, ∫ Y, pair (empirical Y) (φ a) ∂(sed_Q d s N β ρ) =
      pair (firstMarginal (sed_Q d s N β ρ)) (φ a) := by
    intro a
    obtain ⟨hc1, hm1, M, hM⟩ := b9_cont_of_smooth (hφ a)
    have hint : ∀ i : Fin N, Integrable (fun Y : Config d N => φ a (Y i)) (sed_Q d s N β ρ) := by
      intro i
      refine (integrable_const M).mono' ((hm1.comp (measurable_pi_apply i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun Y => ?_)
      simpa [Real.norm_eq_abs] using hM (Y i)
    have hex : ∀ i : Fin N, ∫ Y, φ a (Y i) ∂(sed_Q d s N β ρ) =
        pair (firstMarginal (sed_Q d s N β ρ)) (φ a) := fun i =>
      HRS.Q08.q08gl_exch_integral D hN (φ a) hm1 i
    simp_rw [pair_empirical h0]
    rw [integral_const_mul, integral_finset_sum _ fun i _ => hint i]
    simp_rw [hex]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have hcs : ∀ X : Config d N, centeredStat (sed_Q d s N β ρ) φ X =
      WithLp.toLp 2 fun a => Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, φ a (X i) -
        pair (firstMarginal (sed_Q d s N β ρ)) (φ a)) := by
    intro X
    unfold centeredStat
    congr 1
    funext a
    rw [hcen a, pair_empirical h0, one_div]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  simp only [hcs]
  rfl

end HRS.MC.SEdge.B9

end

