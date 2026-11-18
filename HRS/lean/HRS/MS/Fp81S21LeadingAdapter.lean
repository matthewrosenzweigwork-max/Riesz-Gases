import HRS.MS.Fp81S21Radius
import HRS.MS.S21A_Metric
import HRS.MS.S21A_Mono
import HRS.MS.S21B2_Wrap
import HRS.MS.WsPrepAux10
import HRS.MS.S104bOrb1
import HRS.MS.S81G_Main

/-!
# HRS S2.1(iii), SOL26 packet 7: common-radius leading W₁ comparison

The history length enters the frozen orbit theorem through its window-test clause.  The
common-radius result supplies that clause at every horizon, so the S2.1(ii) metric argument can
be run at one radius.  The S6.6 preparation radius comes from the horizon-free entropy input;
only its window-moment constant depends on the chosen horizon.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinOrbNL
open HRS.MS.R2WinErr
open HRS.MS.S21A

private theorem fp81s21_thermalDensity_thermal (p : Parameters) :
    IsThermalEquilibrium p.d p.s p.a p.β (thermalDensity p.d p.s p.a p.β) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  by_cases hs0 : p.s = 0
  · obtain ⟨⟨ρ, hρ, -⟩, -, -⟩ :=
      HRS.MS.Thm.logThermalDensity_spec_proof p.hd p.a p.β p.ha p.hβ
    have hρ' : IsThermalEquilibrium p.d p.s p.a p.β ρ := by simpa [hs0] using hρ
    have hρeq := HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρ'
    rw [hρeq] at hρ'
    simpa [hs0] using hρ'
  · have hspos : 0 < p.s := lt_of_le_of_ne p.hs0 (Ne.symm hs0)
    obtain ⟨⟨ρ, hρ, -⟩, -, -⟩ :=
      HRS.MS.Thm.thermalDensity_spec_proof p.hd hspos hsd p.a p.β p.ha p.hβ
    have hρeq := HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρ
    rw [hρeq] at hρ
    exact hρ

private def fp81s21_ParticlePackage (p : Parameters) (εstar C₀ CB CT H : ℝ) : Prop :=
  ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
    ∀ ε : ℝ, ∀ ψ : Euc p.d → ℝ,
      IsAdmissiblePerturbation ρβ εstar ε ψ → ∀ ρ : ℝ → Euc p.d → ℝ,
      IsResultingSolution p.d p.s p.a p.β ρβ εstar ε ψ p.c₁ p.C₁ ρ →
      ∀ N : ℕ, 2 ≤ N → GibbsEntropyContraction p.d p.s p.a p.β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig p.d N) (W : ℝ≥0 → Ω → (Fin N → Euc p.d))
        (X : ℝ≥0 → Ω → EucConfig p.d N),
        IsVectorBrownian P W → IndepFun X₀ (fun ζ t => W t ζ) P →
        law P X₀ = HRS.Whole.modulatedGibbs (rieszKernel p.d p.s) N p.γ
          (HRS.Whole.withDensityReal (ρ 0)) →
        (∀ T' : ℝ, IsWholeStrongSolution P (quadraticGradientDyn p.d p.s p.a p.β) T' X₀ W X) →
        ∃ X' : ℝ≥0 → Ω → EucConfig p.d N,
          (∀ t : ℝ≥0, X' t =ᵐ[P] X t) ∧
          IsR2Realization p.d p.s p.a p.β P X₀ W X' ∧
          MovParticleBounds p.d p.s p.a p.β C₀ CB ρ N P X' ∧
          ∀ b : ℝ, 0 ≤ b →
            ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + H),
              ENNReal.ofReal (movSecondMoment (X' t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal CT

theorem fp81s21_particlePackage_commonRadius (p : Parameters)
    (hDiss : HRS.MS.MfeConf.SuperDiss p.d p.s) :
    ∃ εpkg : ℝ, 0 < εpkg ∧ ∃ C₀ CB : ℝ,
      ∀ H : ℝ, 0 < H → ∃ CT : ℝ,
        fp81s21_ParticlePackage p εpkg C₀ CB CT H := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρ0 : IsThermalEquilibrium p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) := fp81s21_thermalDensity_thermal p
  have hMov : HRS.Whole.MovEntAt p.d p.s 1 (p.d / 2 + 8) :=
    HRS.MS.MovEnt.movEntAt_low_of_diss hDiss
  have hjm : (p.d : ℝ) / 2 + (1 : ℕ) + 6 < ((p.d / 2 + 8 : ℕ) : ℝ) := by
    have hnat : p.d ≤ 2 * (p.d / 2) + 1 := by omega
    have hreal : (p.d : ℝ) ≤ 2 * ((p.d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast hnat
    push_cast
    linarith
  have hjb : 1 + 1 ≤ 100 * p.d + 1001 := by omega
  have hmb : ((p.d / 2 + 8 : ℕ) : ℝ) ≤ 102 * (p.d : ℝ) + 1020 := by
    have hd0 : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
    have hdiv : ((p.d / 2 : ℕ) : ℝ) ≤ (p.d : ℝ) / 2 := Nat.cast_div_le
    push_cast
    nlinarith
  obtain ⟨ε63, r, c₀, c, C63, hε63, hr, hc₀, hc, hC63, hconc, C₀, hC₀, hC₀b, hγ⟩ :=
    hMov p.hd p.hs0 hsd p.β p.a p.hβ p.ha (thermalDensity p.d p.s p.a p.β) hρ0
      (by norm_num) hjm
  obtain ⟨⟨CB, hCB⟩, hwin⟩ := hγ p.γ p.hγ
  set K : ℝ := max p.C₁ 1 with hK
  have hK1 : 0 < K := lt_of_lt_of_le one_pos (le_max_right _ _)
  set εpkg : ℝ := min ε63 (r / K) with hεpkg
  have hεpkg0 : 0 < εpkg := lt_min hε63 (div_pos hr hK1)
  have hCr : p.C₁ * εpkg ≤ r := by
    calc
      p.C₁ * εpkg ≤ K * εpkg := mul_le_mul_of_nonneg_right (le_max_left _ _) hεpkg0.le
      _ ≤ K * (r / K) := mul_le_mul_of_nonneg_left (min_le_right _ _) hK1.le
      _ = r := by field_simp
  refine ⟨εpkg, hεpkg0, C₀, CB, fun H hH => ?_⟩
  obtain ⟨CT, hCT⟩ := hwin H hH
  refine ⟨CT, ?_⟩
  intro ρβ hρβ ε ψ hadm ρ hres N hN hGEC Ω _ P _ X₀ W X hBr hInd hlaw0 hstrong
  have hρeq : ρβ = thermalDensity p.d p.s p.a p.β := by
    rw [HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρβ,
      HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρ0]
  subst hρeq
  obtain ⟨hf0, hcls⟩ := HRS.Whole.s21p_resulting_in_class_low hjb hmb hconc
    (min_le_left _ _) hCr hadm hres
  have hX0m : Measurable (X 0) := (hstrong 0).adapted 0
  have hinit : X 0 =ᵐ[P] X₀ := (hstrong 0).init
  have hindep0 : IndepFun (X 0) (fun ζ t => W t ζ) P :=
    IndepFun.congr hInd hinit.symm Filter.EventuallyEq.rfl
  have hdistinct : ∀ᵐ ζ ∂P, X 0 ζ ∉ eucCollisionSet p.d N := by
    filter_upwards [(hstrong 0).no_collision] with ζ h
    exact h 0 (by simp)
  have hS0 : ∀ T' : ℝ, 0 < T' →
      IsWholeStrongSolution P (quadraticGradientDyn p.d p.s p.a p.β) T' (X 0) W X :=
    fun T' _ => { hstrong T' with init := Filter.Eventually.of_forall fun _ => rfl }
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide : 1 ≤ 2) p.hd
  obtain ⟨X', ℱ, W', hmod, hsol', hfil⟩ :=
    HRS.MS.S21.s21p_filtered_global hd1 p.s p.a p.β hN P W X hBr hindep0
      hdistinct hS0 hX0m
  have hsolX : ∀ T' : ℝ,
      IsWholeStrongSolution P (quadraticGradientDyn p.d p.s p.a p.β) T' X₀ W X' := by
    intro T'
    have hi : ∀ᵐ ζ ∂P, X' 0 ζ = X₀ ζ := by
      filter_upwards [(hsol' T').init, hinit] with ζ h1 h2
      exact h1.trans h2
    exact { hsol' T' with init := hi }
  have hreal : IsR2Realization p.d p.s p.a p.β P X₀ W X' :=
    { brownian := hBr
      indep := hInd
      solution := hsolX
      filtered := ⟨ℱ, W', hfil⟩ }
  have hsetup : MovParticleSetup P p.d p.s p.a p.β N X₀ W X' :=
    ⟨hBr, hInd, hreal.solution, hreal.filtered⟩
  have hprob0 : IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ 0)) :=
    HRS.MS.Thm.cb_withDensityReal_isProb
      ((hres.global 0).density 0 ⟨le_rfl, le_rfl⟩)
  have hprep : MovPrepared p.d p.s N p.γ (HRS.Whole.withDensityReal (ρ 0)) (P.map X₀) := by
    rcases p.hγ.eq_or_lt with h0 | hpos
    · refine Or.inl ⟨h0.symm, ?_⟩
      have := hlaw0
      rw [← h0, HRS.Whole.modulatedGibbs_zero] at this
      exact this
    · exact Or.inr ⟨hpos, hlaw0⟩
  refine ⟨X', hmod, hreal, hCB _ hf0 ρ hcls N hN hGEC P X₀ W X' hsetup hprep, ?_⟩
  intro b hb
  exact hCT _ hf0 ρ hcls N hN hGEC P X₀ W X' hsetup hprep b hb

theorem fp81s21_recentWindowGeometry {a₀ L T : ℝ}
    (ha₀ : 0 ≤ a₀) (hL : 0 < L) (hT : 0 < T) :
    let b := max (a₀ - L) 0
    0 ≤ b ∧ 0 ≤ a₀ - b ∧ a₀ - b ≤ L ∧ a₀ + T ≤ b + (L + T) := by
  dsimp
  by_cases haL : a₀ ≤ L
  · rw [max_eq_right (sub_nonpos.mpr haL)]
    constructor
    · exact le_refl (0 : ℝ)
    constructor
    · simpa using ha₀
    constructor
    · linarith
    · linarith
  · have hLa : L < a₀ := lt_of_not_ge haL
    rw [max_eq_left (sub_nonneg.mpr hLa.le)]
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    · linarith

theorem fp81s21_gibbsEntropyContraction (p : Parameters) (N : ℕ) :
    HRS.Whole.GibbsEntropyContraction p.d p.s p.a p.β N :=
  HRS.MS.S81G.s81g_gibbsEntropyContraction
    (Nat.le_trans (by decide : 1 ≤ 2) p.hd) p.hs0 p.ha p.hβ

#print axioms fp81s21_particlePackage_commonRadius
#print axioms fp81s21_recentWindowGeometry
#print axioms fp81s21_gibbsEntropyContraction

