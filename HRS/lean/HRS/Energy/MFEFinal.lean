import HRS.Energy.MFEAux1
import HRS.Energy.Commutator.Assembly
import HRS.PDE.MovSpec3
import HRS.PDE.MovFFinal
import HRS.PDE.MovSpecAux
import HRS.PDE.EnergyR2Fn

/-!
# MFE: relocated proof of Proposition 3.41 `mfe_uniform` (statement verbatim)

Chain plan: header of `HRS/Energy/MFEAux1.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d : ℕ}

theorem mfe_uniform_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧
      ∀ (D : DynData d), D.s = s → ∀ (N : ℕ), 2 ≤ N → ∀ (T Λ lam₀ : ℝ), 0 ≤ T →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (ρ : ℝ → Torus d → ℝ) (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
        (X : ℝ≥0 → Ω → Config d N),
        MFEHyp P D N T Λ lam₀ ρ X₀ W X →
      ∀ K : ℝ → ℝ, IntegrableOn K (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc 0 T, HasTransportBound d s (mfeTransport D (ρ t)) (K t)) →
      ∀ t ∈ Set.Icc 0 T,
        (P.map (X (Real.toNNReal t))).AbsolutelyContinuous volume ∧
        MFEFinite d s (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) ∧
        modulatedFreeEnergy d s D.invβ (P.map (X (Real.toNNReal t))) (withDensityReal (ρ t)) +
            oNΛ d s C₀ Λ N ≤
          Real.exp (C * ∫ r in Set.Icc 0 T, K r) *
            (modulatedFreeEnergy d s D.invβ (P.map X₀) (withDensityReal (ρ 0)) + oNΛ d s C₀ Λ N) := by
  obtain ⟨A₀, A, hA₀, hA, hcomm⟩ := Commutator.commutator_estimate_of_packets hd hs0 hsd
  obtain ⟨B₀, hB₀, hnn⟩ := Commutator.energy_add_oN_nonneg hd hs0 hsd
  refine ⟨max A₀ B₀, A / 2, le_max_of_le_left hA₀, by positivity, ?_⟩
  intro D hDs N hN T Λ lam₀ hT Ω _ P _ ρ X₀ W X h K hKi hK
  subst hDs
  have hMov := movT_hyp_of_mfeHyp_proof h
  have key := mov_mfe_ineq hN P hMov h.mfe_init
  have hΛ1 : 1 ≤ Λ := h.Λ_ge
  have hΛ0 : 0 ≤ Λ := by linarith
  have hβ : 0 < D.invβ := h.pos_temp
  set o : ℝ := oNΛ d D.s (max A₀ B₀) Λ N with ho
  have hoA : oNΛ d D.s A₀ Λ N ≤ o := oNΛ_mono_C₀ (le_max_left _ _) hΛ0 N
  have hoB : oNΛ d D.s B₀ Λ N ≤ o := oNΛ_mono_C₀ (le_max_right _ _) hΛ0 N
  have hK0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ K r := fun r hr => (hK r hr).nonneg
  have hρΛ : ∀ r ∈ Set.Icc 0 T, ∀ x, ρ r x ≤ Λ := fun r hr x =>
    (le_abs_self _).trans ((PDE.R2Aux.abs_le_cbNorm (h.mf_reg r hr).1 x).trans (h.mf_reg r hr).2)
  -- general bounds for a probability measure ν of finite modulated free energy at time r
  have hbd : ∀ r ∈ Set.Icc 0 T, ∀ (ν : Measure (Config d N)) [IsProbabilityMeasure ν],
      MFEFinite d D.s ν (withDensityReal (ρ r)) →
      0 ≤ ∫ Z, rieszEnergy d D.s Z (withDensityReal (ρ r)) ∂ν + o ∧
      |∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r)) ∂ν| ≤
        A * K r * (∫ Z, rieszEnergy d D.s Z (withDensityReal (ρ r)) ∂ν + o) ∧
      ∫ Z, rieszEnergy d D.s Z (withDensityReal (ρ r)) ∂ν + o ≤
        modulatedFreeEnergy d D.s D.invβ ν (withDensityReal (ρ r)) + o := by
    intro r hr ν _ hfin
    have hρ := h.mf.density r hr
    obtain ⟨-, hae⟩ := mfe41_ac hd hρ hfin.1
    have hnn' : ∀ᵐ Z ∂ν, 0 ≤ rieszEnergy d D.s Z (withDensityReal (ρ r)) + o := by
      filter_upwards [hae] with Z hZ
      have := hnn Λ hΛ1 N hN (ρ r) hρ (hρΛ r hr) Z hZ
      linarith
    have hc' : ∀ᵐ Z ∂ν, |commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r))| ≤
        A * K r * (rieszEnergy d D.s Z (withDensityReal (ρ r)) + o) := by
      filter_upwards [hae] with Z hZ
      have h1 := (hcomm Λ hΛ1 N hN (ρ r) hρ (hρΛ r hr) Z hZ _ (K r) (hK r hr)).2
      refine h1.trans ?_
      have hAK : 0 ≤ A * K r := mul_nonneg hA.le (hK0 r hr)
      exact mul_le_mul_of_nonneg_left (by linarith) hAK
    obtain ⟨h1, h2⟩ := mfe41_int hfin.2 hnn' hc'
    refine ⟨h1, h2, ?_⟩
    unfold modulatedFreeEnergy
    have : 0 ≤ D.invβ * (normRelEntropy N ν (Measure.pi fun _ : Fin N => withDensityReal (ρ r))).toReal :=
      mul_nonneg hβ.le ENNReal.toReal_nonneg
    linarith
  -- Gronwall
  have hT' : T ∈ Set.Icc 0 T := ⟨hT, le_rfl⟩
  have hint := (key T hT').2.2.1
  have hgr := movspec_gronwall_var (T := T)
    (u0 := modulatedFreeEnergy d D.s D.invβ (P.map X₀) (withDensityReal (ρ 0)) + o)
    (a := fun r => A / 2 * K r)
    (G := fun r => -(1 / 2) * ∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r))
        ∂(P.map (X r.toNNReal)))
    (u := fun r => modulatedFreeEnergy d D.s D.invβ (P.map (X r.toNNReal)) (withDensityReal (ρ r)) + o)
    (fun r hr => mul_nonneg (by positivity) (hK0 r hr)) (hKi.const_mul _) (hint.const_mul _)
    (fun t ht => by
      have := (key t ht).2.2.2
      rw [integral_const_mul]
      linarith)
    (fun r hr => by
      haveI : IsProbabilityMeasure (P.map (X r.toNNReal)) := inferInstance
      obtain ⟨-, h2, h3⟩ := hbd r hr (P.map (X r.toNNReal)) (key r hr).1
      have h4 := neg_abs_le (∫ Z, commQuantity d D.s (mfeTransport D (ρ r)) Z (withDensityReal (ρ r))
        ∂(P.map (X r.toNNReal)))
      have h5 : 0 ≤ A * K r := mul_nonneg hA.le (hK0 r hr)
      have h6 := mul_le_mul_of_nonneg_left h3 h5
      nlinarith)
  haveI : IsProbabilityMeasure (P.map X₀) := inferInstance
  obtain ⟨hu0, -, hu0'⟩ := hbd 0 ⟨le_rfl, hT⟩ (P.map X₀) h.mfe_init
  intro t ht
  refine ⟨?_, (key t ht).1, ?_⟩
  · have hρ := h.mf.density t ht
    exact (mfe41_ac hd hρ (key t ht).1.1).1
  · have h1 := hgr t ht
    refine h1.trans ?_
    have hu0n : 0 ≤ modulatedFreeEnergy d D.s D.invβ (P.map X₀) (withDensityReal (ρ 0)) + o := by
      linarith
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hu0n
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set hKi (ae_restrict_of_forall_mem measurableSet_Icc (fun r hr => hK0 r hr))
      (Eventually.of_forall (Set.Icc_subset_Icc le_rfl ht.2))

example := (@mfe_uniform_proof : type_of% @HRS.mfe_uniform)

end HRS

end
