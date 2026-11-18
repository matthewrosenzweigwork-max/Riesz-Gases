import HRS.PDE.MovFAux1
import HRS.PDE.MovFAux3
import HRS.PDE.MovFAux4
import HRS.PDE.MovFAux5
import HRS.PDE.MovFAux9
import HRS.PDE.MovFAux12
import HRS.PDE.MovFAux14

/-!
# MOVF: relocated proofs of MovSpec3 packets (`_proof`, statements verbatim)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movT_relEntropy_split_proof (hN : 2 ≤ N) {D : DynData d} (hβ : 0 < D.invβ) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hs : Torus.IsCk 2 ρ) (hpos : ∀ x, 0 < ρ x)
    {ν : Measure (Config d N)} [IsProbabilityMeasure ν] :
    (relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ)) ≠ ⊤ ↔
      MFEFinite d D.s ν (withDensityReal ρ)) ∧
    (MFEFinite d D.s ν (withDensityReal ρ) →
      (relEntropy ν (modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ))).toReal =
        (relEntropy ν (Measure.pi fun _ : Fin N => withDensityReal ρ)).toReal +
          D.invβ⁻¹ * N * ∫ X, rieszEnergy d D.s X (withDensityReal ρ) ∂ν +
          Real.log (gibbsNormalizer (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal ρ))) := by
  have hd : 1 ≤ d := b15_one_le_d D
  have hc : Continuous ρ := mova_continuous_of_isCk hs
  have hN0 : 0 < N := by omega
  haveI := isProb_withDensityReal hρ
  have hβ' : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  obtain ⟨hm, C, hC⟩ := movf_energy_facts hd D.hs0 D.hsd hρ hc hN0 (N := N)
  have hQ := movf_modGibbs_eq_tilted hd D.hs0 D.hsd hρ hc hN0 hβ'.le
  set P := Measure.pi fun _ : Fin N => withDensityReal ρ with hP
  set f : Config d N → ℝ := fun X => -D.invβ⁻¹ * N *
    modulatedEnergyKernel (periodicRiesz d D.s) X (withDensityReal ρ) with hf
  have hfm : Measurable f := measurable_const.mul hm
  have hfC : ∀ X, f X ≤ D.invβ⁻¹ * N * C := fun X => by
    have := hC X
    have h0 : 0 ≤ D.invβ⁻¹ * N := by positivity
    simp only [hf]
    nlinarith
  have hNne : -D.invβ⁻¹ * (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast hN0
    have := mul_pos hβ' this
    intro h; linarith
  have hint : ∀ {ν' : Measure (Config d N)}, Integrable f ν' ↔
      Integrable (fun X => rieszEnergy d D.s X (withDensityReal ρ)) ν' := fun {ν'} =>
    integrable_const_mul_iff (isUnit_iff_ne_zero.2 hNne) _
  have key := movf_kl_tilted P ν hfm hfC
  unfold MFEFinite relEntropy
  rw [hQ]
  refine ⟨?_, fun hfin => ?_⟩
  · rw [key.1, hint]
  · have := key.2 ⟨hfin.1, (hint).2 hfin.2⟩
    rw [this]
    have hi : ∫ X, f X ∂ν = -D.invβ⁻¹ * N * ∫ X, rieszEnergy d D.s X (withDensityReal ρ) ∂ν :=
      integral_const_mul _ _
    rw [hi]
    show _ = _ + _ + Real.log (∫ x, Real.exp (f x) ∂P)
    ring

example := (@movT_relEntropy_split_proof : type_of% @HRS.movT_relEntropy_split)

theorem movT_prepared_initial_Lp_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {μ : Torus d → ℝ}
    (hμ : IsProbDensity μ) (hck : Torus.IsCk 2 μ) (hpos : ∀ x, 0 < μ x) {β₀ β p₀ : ℝ} (hβ₀ : 0 < β₀)
    (hβ : 0 < β) (hp₀ : 1 < p₀) (hcoef : 0 < p₀ * β₀ - (p₀ - 1) * β) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal μ) ≪
        modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ) ∧
      eLpNorm ((modulatedGibbs (periodicRiesz d s) N β₀ (withDensityReal μ)).rnDeriv
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ))) (ENNReal.ofReal p₀)
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal μ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d s N)) :=
  movf_prepared_initial_Lp hd hs0 hsd hμ hck hpos hβ₀ hβ hp₀ hcoef

example := (@movT_prepared_initial_Lp_proof : type_of% @HRS.movT_prepared_initial_Lp)

theorem movT_prepared_initial_Lp_iid_proof (hd : 2 ≤ d) {μ : Torus d → ℝ} (hμ : IsProbDensity μ) (hck : Torus.IsCk 2 μ)
    (hpos : ∀ x, 0 < μ x) {β : ℝ} (hβ : 0 < β) :
    ∃ p₀ C : ℝ, 1 < p₀ ∧ ∀ N : ℕ, 2 ≤ N →
      modulatedGibbs (periodicRiesz d 0) N 0 (withDensityReal μ) ≪
        modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ) ∧
      eLpNorm ((modulatedGibbs (periodicRiesz d 0) N 0 (withDensityReal μ)).rnDeriv
          (modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ))) (ENNReal.ofReal p₀)
        (modulatedGibbs (periodicRiesz d 0) N β (withDensityReal μ)) ≤
        ENNReal.ofReal (Real.exp (C * N * deltaN d 0 N)) :=
  movf_prepared_initial_Lp_iid hd hμ hck hpos hβ

example := (@movT_prepared_initial_Lp_iid_proof : type_of% @HRS.movT_prepared_initial_Lp_iid)

theorem movT_traj_uniform_proof (s β : ℝ) (V ρ₀ : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (hs0 : 0 ≤ s)
    (hsd : s < d) (hβ : 0 < β) (hV : Torus.IsSmooth V) (hρ₀ : SmoothPosDensity ρ₀)
    (hglobal : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
      ∃ ρc : ℝ → (Lattice d → ℂ), PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧
        ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t) :
    ∃ c₀ Λ₂ : ℝ, 0 < c₀ ∧ ∀ t : ℝ, 0 ≤ t → (∀ x, c₀ ≤ ρ t x) ∧ Torus.cbNorm 2 (ρ t) ≤ Λ₂ :=
  movf_traj_uniform s β V ρ₀ ρ hs0 hsd hβ hV hρ₀ hglobal

example := (@movT_traj_uniform_proof : type_of% @HRS.movT_traj_uniform)

theorem movT_traj_of_global_proof (s β : ℝ) (V ρ₀ : Torus d → ℝ) (ρ : ℝ → Torus d → ℝ) (hs0 : 0 ≤ s)
    (hsd : s < d) (hβ : 0 < β) (hV : Torus.IsSmooth V) (hρ₀ : SmoothPosDensity ρ₀)
    (hglobal : ∀ K : ℕ, (d : ℝ) / 2 + 6 < K →
      ∃ ρc : ℝ → (Lattice d → ℂ), PDE.IsMFSolutionHK d s V β⁻¹ K ρ₀ ρc ∧
        ∀ t, 0 ≤ t → PDE.mfPath ρc t = ρ t)
    (T : ℝ) : MovTraj (PDE.mfData d s hs0 hsd V β hβ) T ρ :=
  movf_traj_of_global s β V ρ₀ ρ hs0 hsd hβ hV hρ₀ hglobal T

example := (@movT_traj_of_global_proof : type_of% @HRS.movT_traj_of_global)

theorem movT_isC12Test_of_weak_proof {D : DynData d} {T Λ lam₀ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hM : D.M = -1) (hβ : 0 < D.invβ) (hV : Torus.IsCk (PDE.mStar d + 2) D.V)
    (hmf : IsMeanFieldSolution D T ρ) (hreg : IsRegularMF (PDE.mStar d + 2) Λ T ρ)
    (hpos : 0 < lam₀ ∧ ∀ t ∈ Set.Icc 0 T, ∀ x, lam₀ ≤ ρ t x) :
    ∃ ρt : ℝ → Torus d → ℝ, IsC12Test T ρ ρt :=
  movf_isC12Test_of_weak hM hβ hV hmf hreg hpos

example := (@movT_isC12Test_of_weak_proof : type_of% @HRS.movT_isC12Test_of_weak)

theorem movT_hyp_of_mfeHyp_proof {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : DynData d}
    {T Λ lam₀ : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : MFEHyp P D N T Λ lam₀ ρ X₀ W X) : MovHyp P D N T ρ X₀ W X := by
  have hn2 : 2 ≤ PDE.mStar d + 2 := by omega
  refine ⟨⟨h.gradient, h.pos_temp, mova_isCk_of_le (by exact_mod_cast hn2) h.V_reg, h.mf,
    fun r hr => mova_isCk_of_le (by exact_mod_cast hn2) (h.mf_reg r hr).1,
    ⟨Λ, fun r hr => (KernelGrad.cbNorm_mono hn2).trans (h.mf_reg r hr).2⟩,
    fun r hr x => lt_of_lt_of_le h.pos_density.1 (h.pos_density.2 r hr x),
    movT_isC12Test_of_weak_proof h.gradient h.pos_temp h.V_reg h.mf h.mf_reg h.pos_density⟩,
    h.brownian, h.indep, h.sol, h.filtered⟩

example := (@movT_hyp_of_mfeHyp_proof : type_of% @HRS.movT_hyp_of_mfeHyp)

/-- `movT_relaxation_L` with the extra hypothesis `hρβ : Torus.IsCk 2 ρβ`.  As stated (without it) the packet needs the
`C²` regularity of the thermal density for a merely `C²` potential: `hrelax` is junk-vulnerable (`cbNorm` of a non-`C²`
difference is a junk value), and the repo proves thermal regularity only for smooth `V` and `d ≥ 2`
(`PDE.thermal_exists_unique_smooth`, `Regime.thermal`).  In the consumer (`Regime`) `ρβ` is smooth. -/
theorem movT_relaxation_L_proof_reg {D : DynData d} {ρ : ℝ → Torus d → ℝ} {ρβ : Torus d → ℝ}
    (hM : D.M = -1) (hβ : 0 < D.invβ) (hth : IsThermalDensity (periodicRiesz d D.s) D.V D.invβ⁻¹ ρβ)
    (hρβ : Torus.IsCk 2 ρβ)
    (htr : ∀ T : ℝ, MovTraj D T ρ) {C₀ lam : ℝ} (hlam : 0 < lam)
    (hrelax : ∀ t : ℝ, 0 ≤ t → Torus.cbNorm 2 (fun x => ρ t x - ρβ x) ≤ C₀ * Real.exp (-lam * t)) :
    ∃ L : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ L t) ∧ IntegrableOn L (Set.Ici 0) ∧
      ∀ t : ℝ, 0 ≤ t → IsLipschitzVF (L t) (mfeTransport D (ρ t)) :=
  movf_relaxation_L_of_reg hM hβ hth hρβ htr hlam hrelax

end HRS

end
