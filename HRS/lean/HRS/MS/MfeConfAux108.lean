import HRS.MS.MfeConfAux107
import HRS.MP.SelfSimP4LscM

/-!
# S.B.1, packet F9 (part 11): convergence of the Gibbs references and lower semicontinuity of the entropy along `M → ∞`

* `sb1_Q_integral_eq`: `∫ψ dQ_k = K_k⁻¹ ∫ F_k ψ dμ^N`;
* `sb1_Q_tendsto`: `∫ψ dQ^M → ∫ψ dQ` for bounded measurable `ψ` (dominated convergence, normalisers converge to a positive limit);
* `sb1_lsc_Q`: `H(m|Q) ≤ liminf_M H(m_M|Q^M)` under setwise convergence `m_M → m` (`p4lm_klDiv_liminf`).
-/

noncomputable section

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Gibbs

variable {s : ℝ} {ρ0 : Euc d → ℝ} {Cρ M1 : ℝ} {kn : ℕ → Euc d → ℝ} {k : Euc d → ℝ}

theorem sb1_Q_integral_eq (hk : Measurable k) (R : Sb1Rho ρ0 Cρ M1) {β : ℝ} (ψ : Whole.EucConfig d N → ℝ) :
    ∫ X, ψ X ∂(Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0)) =
      (∫ X : Whole.EucConfig d N, sb1FF k β N ρ0 X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0))⁻¹ *
        ∫ X : Whole.EucConfig d N, sb1FF k β N ρ0 X * ψ X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) := by
  rw [sb1_integral_modGibbs hk R.dens, sb1_integral_pi R.dens, sb1_integral_pi R.dens,
    sb1_gibbsNormalizer_eq R.dens]
  rfl

theorem sb1_Q_tendsto (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hkn : ∀ n, Sb1KerU d s (kn n)) (hk : Sb1KerU d s k)
    (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (k z))) (R : Sb1Rho ρ0 Cρ M1)
    (hKpos : 0 < ∫ X : Whole.EucConfig d N, sb1FF k β N ρ0 X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0))
    {ψ : Whole.EucConfig d N → ℝ} (hψ : Measurable ψ) {Cψ : ℝ} (hC : ∀ x, |ψ x| ≤ Cψ) :
    Tendsto (fun n => ∫ X, ψ X ∂(Whole.modulatedGibbs (kn n) N β (Whole.withDensityReal ρ0))) atTop
      (𝓝 (∫ X, ψ X ∂(Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0)))) := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ0) := HRS.MS.Thm.cb_withDensityReal_isProb R.dens
  have hae := HRS.MS.Wr.ae_injective_pi_Euc (N := N) (HRS.MS.Wr.wr12_atomless hd ρ0)
  simp_rw [sb1_Q_integral_eq (hkn _).meas R ψ]
  rw [sb1_Q_integral_eq hk.meas R ψ]
  refine ((sb1_K_tendsto hd hs0 hsd hN hβ hkn hk hconv R).inv₀ hKpos.ne').mul ?_
  refine tendsto_integral_of_dominated_convergence (fun _ => sb1CwR d s Cρ M1 β N * |Cψ|)
    (fun n => ((sb1_FF_meas (hkn n) R β).mul hψ).aestronglyMeasurable) (integrable_const _)
    (fun n => Eventually.of_forall fun X => ?_) ?_
  · unfold sb1FF
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (sb1_E_le hd hs0 hsd hN hβ (hkn n) R X) ((hC X).trans (le_abs_self _)) (abs_nonneg _)
      (Real.exp_pos _).le
  · filter_upwards [hae] with X hX
    exact (sb1_FF_tendsto hd hs0 hsd hkn hconv R X hX).mul_const _

theorem sb1_K_eq (R : Sb1Rho ρ0 Cρ M1) {β : ℝ} :
    Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ0) =
      ∫ X : Whole.EucConfig d N, sb1FF k β N ρ0 X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) := by
  unfold Whole.gibbsNormalizer sb1FF
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  simp only [sb1_modEnergy_eq R.dens]

theorem sb1_modGibbs_prob (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hk : Sb1KerU d s k) (R : Sb1Rho ρ0 Cρ M1) :
    IsProbabilityMeasure (Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0)) := by
  have hK : 0 < Whole.gibbsNormalizer k N β (Whole.withDensityReal ρ0) := by
    rw [sb1_K_eq R]; exact sb1_Kpi_pos' hd hs0 hsd hN hβ hk R
  rw [sb1_modGibbs_eq_Dm hk.meas R.dens hK]
  exact sb1Dm_prob (sb1_qd_lintegral R.dens hK)

/-- **lower semicontinuity along `M → ∞`** of the relative entropy with moving normalised Gibbs references -/
theorem sb1_lsc_Q (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N) {β : ℝ} (hβ : 0 ≤ β)
    (hkn : ∀ n, Sb1KerU d s (kn n)) (hk : Sb1KerU d s k)
    (hconv : ∀ z, z ≠ 0 → Tendsto (fun n => kn n z) atTop (𝓝 (k z))) (R : Sb1Rho ρ0 Cρ M1)
    {m : Measure (Whole.EucConfig d N)} {mM : ℕ → Measure (Whole.EucConfig d N)}
    [IsProbabilityMeasure m] [∀ n, IsProbabilityMeasure (mM n)]
    (hm : ∀ A : Set (Whole.EucConfig d N), MeasurableSet A → Tendsto (fun n => mM n A) atTop (𝓝 (m A))) :
    relEntropy m (Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0)) ≤
      liminf (fun n => relEntropy (mM n) (Whole.modulatedGibbs (kn n) N β (Whole.withDensityReal ρ0))) atTop := by
  haveI := sb1_modGibbs_prob hd hs0 hsd hN hβ hk R (N := N)
  haveI : ∀ n, IsProbabilityMeasure (Whole.modulatedGibbs (kn n) N β (Whole.withDensityReal ρ0)) :=
    fun n => sb1_modGibbs_prob hd hs0 hsd hN hβ (hkn n) R
  have hKpos : 0 < ∫ X : Whole.EucConfig d N, sb1FF k β N ρ0 X ∂(Measure.pi fun _ : Fin N => Whole.withDensityReal ρ0) :=
    sb1_Kpi_pos' hd hs0 hsd hN hβ hk R
  exact p4lm_klDiv_liminf (μ := m) (ρ := Whole.modulatedGibbs k N β (Whole.withDensityReal ρ0))
    (μn := mM) (ρn := fun n => Whole.modulatedGibbs (kn n) N β (Whole.withDensityReal ρ0))
    (fun ψ hψ ⟨C, hC⟩ => p4m_setwise_integral hm hψ hC)
    (fun ψ hψ ⟨C, hC⟩ => sb1_Q_tendsto hd hs0 hsd hN hβ hkn hk hconv R hKpos hψ hC)

end Gibbs

end HRS.MS.MfeConf
