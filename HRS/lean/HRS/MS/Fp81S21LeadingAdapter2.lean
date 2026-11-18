import HRS.MS.Fp81S21LeadingAdapter
import HRS.MS.Fp81S21Radius
import HRS.MS.S21A_Real
import HRS.MS.S21A_Err
import HRS.MS.S104bOrb1
import HRS.MS.S105rReg2
import HRS.MS.WsPrepAux14

/-!
# HRS S2.1(iii), SOL26 packet 7: fixed-radius leading W₁ adapter

The fixed-radius reconstruction uses the horizon-free orbit and terminal-regularity
clauses, while selecting the S10.3 window constant and S10.4/S6.6 completion constants
after the requested history length.
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

/-- The selected thermal density is a thermal equilibrium also in the zero-confinement case. -/
private theorem fp81s21_canonicalThermal (p : Parameters) :
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

/-- A fixed-radius terminal-orbit and window package yields the INIT orbit input at each horizon. -/
theorem fp81s21_orbClass_from_commonRadius (p : Parameters) {δ H : ℝ}
    (hδ : 0 < δ) (hH : 0 < H)
    (hNL : S104nAllOrb p.d p.s p.a p.β δ p.c₁ p.C₁)
    (hWindow : ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      S103nWindowClause p.d p.s p.a p.β H ρβ δ p.c₁ p.C₁) :
    ∃ Corb : ℝ, 0 ≤ Corb ∧ HRS.MS.S21.S21iOrbClass p.d p.s p.a p.β H δ p.c₁ p.C₁ Corb := by
  have hthermal := fp81s21_canonicalThermal p
  obtain ⟨Cw, hW⟩ := hWindow (thermalDensity p.d p.s p.a p.β) hthermal
  set Corb : ℝ := max Cw 0 with hCorb
  have hCorb0 : 0 ≤ Corb := le_max_right _ _
  refine ⟨Corb, hCorb0, ?_⟩
  intro ρβ hρβ ε ψ hadm ρ hres
  have hρeq : ρβ = thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 (by linarith [p.hs]) p.ha p.hβ hρβ
  subst ρβ
  refine ⟨hCorb0, fun bw hbw n α => ?_, fun bw hbw α x => ?_⟩
  · have hex : ∀ t : ℝ, 0 ≤ t → ∃ f : ℝ → Euc p.d → ℝ,
        IsClassicalAdjointW ((quadraticGradientDyn p.d p.s p.a p.β).coeff ρ) t
          (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α) f :=
      fun t ht => (hNL _ hthermal ε ψ ρ hadm hres α t ht).ex0 t ⟨ht, le_rfl⟩
    obtain ⟨hmem, hbound⟩ := hW ε ψ ρ hadm hres α hex bw hbw n
    refine ⟨hmem, ?_⟩
    have hn : 0 ≤ (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) := by positivity
    have hb : 0 ≤ HRS.MS.R2WinOrb.s103_b p.d α :=
      HRS.MS.R2WinOrb.s103_b_nonneg (d := p.d) α
    calc
      cbNorm (4 * p.d + 42) (r2WindowTest ((quadraticGradientDyn p.d p.s p.a p.β).coeff ρ)
          ((wholeSpaceIndex p.d : ℕ) : ℝ) H bw n α) ≤
        Cw * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * HRS.MS.R2WinOrb.s103_b p.d α := hbound
      _ ≤ Corb * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * HRS.MS.S21.s21iB p.d α := by
        calc
          Cw * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * HRS.MS.R2WinOrb.s103_b p.d α ≤
              Corb * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * HRS.MS.R2WinOrb.s103_b p.d α :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left Cw 0) hn) hb
          _ = Corb * (1 + (n : ℝ)) ^ (-(5 : ℝ) / 4) * HRS.MS.S21.s21iB p.d α := by
            rfl
  · have hc := s21a_cont_of_diff (T0 := bw + H) (by linarith)
      (hNL _ hthermal ε ψ ρ hadm hres α (bw + H) (by linarith)) x
    exact hc.comp (continuousOn_const.add continuousOn_id) fun u hu =>
      ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- Combine the horizon-free nonlinear orbit bounds with the stationary S10.3 bounds. -/
theorem fp81s21_orbitGrad_commonRadius (p : Parameters) {δ H Co co : ℝ}
    (hH : 0 < H) (hco : 0 < co)
    (hOrbit : ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      S103nOrbitClaims p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ Co co) :
    ∃ Cs0 cdec : ℝ, 0 ≤ Cs0 ∧ 0 < cdec ∧ Summable (s104_b p.d) ∧
      ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
        ∀ ρ : ℝ → Euc p.d → ℝ,
          IsR2WindowTrajectory p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ ρ →
          ∀ α : MultiIndex p.d,
            (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn p.d p.s p.a p.β).coeff ρ)
              (4 * p.d + 42) t (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)
              (Cs0 * s104_b p.d α) cdec) ∧
            (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn p.d p.s p.a p.β).coeff ρ)
              (4 * p.d + 42) t
              (generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff ρ) t
                (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α))
              (Cs0 * s104_b p.d α) cdec) := by
  obtain ⟨Cstat, cstat, hcstat, hsum, hstat⟩ := HRS.MS.R2WinOrb.s103_stationary
    p.hd p.s p.hs0 (by linarith [p.hs]) p.a p.β p.ha p.hβ H hH
  let Cs0 : ℝ := max (max Cstat Co) 0
  let cdec : ℝ := min cstat co
  have hCs00 : 0 ≤ Cs0 := le_max_right _ _
  have hCstat : Cstat ≤ Cs0 := (le_max_left _ _).trans (le_max_left _ _)
  have hCo : Co ≤ Cs0 := (le_max_right _ _).trans (le_max_left _ _)
  have hcdec : 0 < cdec := lt_min hcstat hco
  have hcstat' : cdec ≤ cstat := min_le_left _ _
  have hco' : cdec ≤ co := min_le_right _ _
  have hsum' : Summable (s104_b p.d) := by
    change Summable (HRS.MS.R2WinOrb.s103_b p.d)
    exact hsum
  have hb0 : ∀ α : MultiIndex p.d, 0 ≤ s104_b p.d α :=
    HRS.MS.R2WinErr.s104_b_nonneg
  have hgrad : ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      ∀ ρ : ℝ → Euc p.d → ℝ,
        IsR2WindowTrajectory p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ ρ →
        ∀ α : MultiIndex p.d,
          (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn p.d p.s p.a p.β).coeff ρ)
            (4 * p.d + 42) t (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α)
            (Cs0 * s104_b p.d α) cdec) ∧
          (∀ t : ℝ, 0 ≤ t → R2OrbitGrad ((quadraticGradientDyn p.d p.s p.a p.β).coeff ρ)
            (4 * p.d + 42) t
            (generatorW ((quadraticGradientDyn p.d p.s p.a p.β).coeff ρ) t
              (oscTestFun ((wholeSpaceIndex p.d : ℕ) : ℝ) α))
            (Cs0 * s104_b p.d α) cdec) := by
    intro ρβ hρβ ρ htraj α
    refine ⟨?_, ?_⟩
    · intro t ht
      rcases htraj with hstatρ | ⟨ε, ψ, hadm, hres⟩
      · rw [hstatρ]
        have hsα := hstat ρβ hρβ α
        dsimp only at hsα
        obtain ⟨hclaims, -⟩ := hsα
        obtain ⟨-, hphi, -, hgen, -⟩ := hclaims t ht
        have hA : 0 ≤ Cs0 * s104_b p.d α := mul_nonneg hCs00 (hb0 α)
        have hm : Cstat * s104_b p.d α ≤ Cs0 * s104_b p.d α :=
          mul_le_mul_of_nonneg_right hCstat (hb0 α)
        exact HRS.MS.R2WinOrbNL.s103n_orbitGrad_mono_c
          (HRS.MS.R2WinOrb.s103_orbitGrad_mono hphi hm) hcstat' hA
      · obtain ⟨-, hphi, -, hgen, -⟩ := hOrbit ρβ hρβ ε ψ ρ hadm hres α t ht
        have hA : 0 ≤ Cs0 * s104_b p.d α := mul_nonneg hCs00 (hb0 α)
        have hm : Co * s104_b p.d α ≤ Cs0 * s104_b p.d α :=
          mul_le_mul_of_nonneg_right hCo (hb0 α)
        exact HRS.MS.R2WinOrbNL.s103n_orbitGrad_mono_c
          (HRS.MS.R2WinOrb.s103_orbitGrad_mono hphi hm) hco' hA
    · intro t ht
      rcases htraj with hstatρ | ⟨ε, ψ, hadm, hres⟩
      · rw [hstatρ]
        have hsα := hstat ρβ hρβ α
        dsimp only at hsα
        obtain ⟨hclaims, -⟩ := hsα
        obtain ⟨-, hphi, -, hgen, -⟩ := hclaims t ht
        have hA : 0 ≤ Cs0 * s104_b p.d α := mul_nonneg hCs00 (hb0 α)
        have hm : Cstat * s104_b p.d α ≤ Cs0 * s104_b p.d α :=
          mul_le_mul_of_nonneg_right hCstat (hb0 α)
        exact HRS.MS.R2WinOrbNL.s103n_orbitGrad_mono_c
          (HRS.MS.R2WinOrb.s103_orbitGrad_mono hgen hm) hcstat' hA
      · obtain ⟨-, hphi, -, hgen, -⟩ := hOrbit ρβ hρβ ε ψ ρ hadm hres α t ht
        have hA : 0 ≤ Cs0 * s104_b p.d α := mul_nonneg hCs00 (hb0 α)
        have hm : Co * s104_b p.d α ≤ Cs0 * s104_b p.d α :=
          mul_le_mul_of_nonneg_right hCo (hb0 α)
        exact HRS.MS.R2WinOrbNL.s103n_orbitGrad_mono_c
          (HRS.MS.R2WinOrb.s103_orbitGrad_mono hgen hm) hco' hA
  exact ⟨Cs0, cdec, hCs00, hcdec, hsum', hgrad⟩

/-- S6.6 particle preparation, with its class radius and completion constants exposed. -/
abbrev fp81s21_ParticlePackage (p : Parameters) (εpkg C₀ CB CT H : ℝ) : Prop :=
  ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
    ∀ ε : ℝ, ∀ ψ : Euc p.d → ℝ,
      IsAdmissiblePerturbation ρβ εpkg ε ψ → ∀ ρ : ℝ → Euc p.d → ℝ,
      IsResultingSolution p.d p.s p.a p.β ρβ εpkg ε ψ p.c₁ p.C₁ ρ →
      ∀ N : ℕ, 2 ≤ N → HRS.Whole.GibbsEntropyContraction p.d p.s p.a p.β N →
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

/-- Reassemble the S21A metric estimate with a radius fixed before the horizon. -/
theorem fp81s21_fixedRadiusMetric (p : Parameters) {δ εpkg C₀pkg CBpkg : ℝ}
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hδpkg : δ ≤ εpkg)
    (hNL : S104nAllOrb p.d p.s p.a p.β δ p.c₁ p.C₁)
    {Co co : ℝ} (hco : 0 < co)
    (hOrbit : ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      S103nOrbitClaims p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ Co co)
    (hWindow : ∀ H : ℝ, 0 < H → ∀ ρβ : Euc p.d → ℝ,
      IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      S103nWindowClause p.d p.s p.a p.β H ρβ δ p.c₁ p.C₁)
    (hPackage : ∀ H : ℝ, 0 < H → ∃ CT : ℝ,
      fp81s21_ParticlePackage p εpkg C₀pkg CBpkg CT H) :
    ∀ H : ℝ, 0 < H → ∃ C₀ C : ℝ, 0 ≤ C ∧
      HRS.Whole.S21PrepMetric p.d p.s p.a p.β p.γ H p.c₁ p.C₁ δ C₀ C := by
  intro H hH
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨CTpkg, hpkg⟩ := hPackage H hH
  obtain ⟨Cs0, cdec, hCs0, hcdec, hsum, hgrad⟩ :=
    fp81s21_orbitGrad_commonRadius p hH hco hOrbit
  obtain ⟨C₀s, herr⟩ := HRS.MS.S21A.s21a_errors_up p.hd p.s p.hs0 hsd p.a p.β p.ha p.hβ
    H hH δ p.c₁ p.C₁ hNL Cs0 cdec hcdec hsum hgrad
  set C₀ : ℝ := max (max C₀s C₀pkg) 1
  have hC₀s : C₀s ≤ C₀ := (le_max_left _ _).trans (le_max_left _ _)
  have hC₀pkg : C₀pkg ≤ C₀ := (le_max_right _ _).trans (le_max_left _ _)
  have hC₀1 : 1 ≤ C₀ := le_max_right _ _
  set CB : ℝ := max (max ((|CBpkg| + 1) * (|C₀pkg| + 1)) CTpkg) 0
  have hCBa : (|CBpkg| + 1) * (|C₀pkg| + 1) ≤ CB := (le_max_left _ _).trans (le_max_left _ _)
  have hCBb : CTpkg ≤ CB := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨CT4, hCT4⟩ := (herr C₀ hC₀s).2 CB
  set K : ℝ := max CT4 0
  have hK0 : 0 ≤ K := le_max_right _ _
  have hKle : CT4 ≤ K := le_max_left _ _
  obtain ⟨Corb, hCorb, horb⟩ := fp81s21_orbClass_from_commonRadius p hδ hH hNL (hWindow H hH)
  obtain ⟨Cinit, hCi, hW⟩ := HRS.MS.S21.s21i_init p.hd p.hs0 hsd p.ha p.hβ p.hγ hH horb
    (fun hpos => HRS.MS.S21.s21u_tiltClass p.hd p.hs0 hsd p.ha p.hβ hpos
      (J := 4 * p.d + 42) (by
        have hd0 : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
        push_cast
        nlinarith [hd0])
      (εstar := δ) hδhalf)
  obtain ⟨Cs, Cw, hCs, hCw, hCmp⟩ :=
    HRS.MS.R2GenInit.s105_win_compare (d := p.d) ((wholeSpaceIndex p.d : ℕ) : ℝ) H hH
  set C : ℝ := max (Cs * K + K + Cinit) (Cw * Real.sqrt K + K + Cinit)
  have hC1 : Cs * K + K + Cinit ≤ C := le_max_left _ _
  have hC2 : Cw * Real.sqrt K + K + Cinit ≤ C := le_max_right _ _
  have hC0 : 0 ≤ C := le_trans (by positivity) hC1
  refine ⟨C₀, C, hC0, ?_⟩
  intro ρβ hρβ ε ψ hadm ρ hres N hN hGEC Ω _ P _ X₀ W X hBr hInd hlaw hstrong Ω' _ P' _ Z hZ a₀ ha₀
  obtain ⟨hadmpkg, hrespkg⟩ := HRS.MS.S21A.s21a_cls_mono p.hd p.hs0 hsd p.ha p.hβ hρβ hδpkg hadm hres
  obtain ⟨X', hmod, hreal, hMov, hwinmom⟩ := hpkg ρβ hρβ ε ψ hadmpkg ρ hrespkg N hN hGEC
    P X₀ W X hBr hInd hlaw hstrong
  have htraj : IsR2WindowTrajectory p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ ρ :=
    Or.inr ⟨ε, ψ, hadm, hres⟩
  have hMov' := HRS.MS.S21A.s21a_mpb_up hN p.hs0 hC₀pkg hC₀1 hCBa hMov
  have hwinmom' : ∀ b : ℝ, 0 ≤ b → ∫⁻ ζ, ⨆ t ∈ Set.Icc b (b + H),
      ENNReal.ofReal (movSecondMoment (X' t.toNNReal ζ)) ∂P ≤ ENNReal.ofReal CB :=
    fun b hb => (hwinmom b hb).trans (ENNReal.ofReal_le_ofReal hCBb)
  obtain ⟨hBt, hFb⟩ := hCT4 ρβ hρβ ρ htraj N hN P X₀ W X' hreal hMov' hwinmom' a₀ ha₀
  obtain ⟨M, L0, Mom, C₀c, hC₀c, hcl⟩ := HRS.MS.R2WinErr.s104n_hcls
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁
  obtain ⟨hρc, -, hjm⟩ := hcl ρβ hρβ ρ htraj
  have hreg : HRS.MS.S104b.S105nReg p.d p.s p.a p.β δ p.c₁ p.C₁ :=
    HRS.MS.S105r.s105r_reg p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁
  have hS := HRS.MS.S104b.s104b_data p.hd p.hs0 hsd p.ha p.hβ hρβ hres
    (fun α T0 h0 => hNL ρβ hρβ ε ψ ρ hadm hres α T0 h0) Cs0 cdec hcdec hsum
    (hgrad ρβ hρβ ρ htraj) (hreg ρβ hρβ ε ψ ρ hadm hres) hjm (hρc 0 le_rfl).2.2.1 hH ha₀
  have hδN : 0 ≤ HRS.deltaN p.d p.s N := HRS.MS.S53.s53_deltaN_nonneg p.s (by omega)
  have hw : 0 ≤ localizationRate p.d p.s C₀ N :=
    HRS.MS.S21T2.s21t2_localizationRate_nonneg
  have hF : ENNReal.ofReal (CT4 * Real.sqrt N * HRS.deltaN p.d p.s N) ≤
      ENNReal.ofReal (K * (Real.sqrt N * HRS.deltaN p.d p.s N)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hKle (mul_nonneg (Real.sqrt_nonneg _) hδN)
  have hWt : ENNReal.ofReal (CT4 * localizationRate p.d p.s C₀ N) ≤
      ENNReal.ofReal (K * localizationRate p.d p.s C₀ N) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKle hw)
  exact HRS.MS.S21A.s21a_window (K1 := K) (K2 := K) (Corb := Corb) (Cinit := Cinit)
    (C₀ := C₀) (Cs := Cs) (Cw := Cw) (C := C)
    (F := ENNReal.ofReal (CT4 * Real.sqrt N * HRS.deltaN p.d p.s N))
    (Wt := ENNReal.ofReal (CT4 * localizationRate p.d p.s C₀ N))
    p.hd p.hs0 hsd p.ha p.hβ hH horb hW hCs hCw hK0 hK0 hCi hC0 hC1 hC2 hCmp
    hρβ hadm hres hN ha₀ P X₀ W X hlaw (hstrong 0).cont X' hmod hreal hS hFb hBt hF hWt P' Z hZ

/-- The S2.1 leading comparison radius precedes every recent-history length. -/
theorem fp81s21_leadingAdapter2 (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ L : ℝ, 0 < L → ∃ C₀ C : ℝ, 0 ≤ C ∧
        ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ G : GaussianRealization R,
          ∀ a₀ : ℝ, 0 ≤ a₀ →
            wassersteinE 1
              (law A.P (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) a₀
                (Real.sqrt N) A.X R.ρ))
              (law G.P (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) (L + p.T) a₀ G.Z)) ≤
              ENNReal.ofReal (C * (Real.sqrt N * deltaN p.d p.s N +
                Real.sqrt (localizationRate p.d p.s C₀ N) + jN p.d p.s p.γ N)) := by
  obtain ⟨δcommon, Co, co, hδcommon, hhalf, hco, hcommon⟩ := fp81s21_common_radius p
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide : 1 ≤ 2) p.hd
  have hDiss : HRS.MS.MfeConf.SuperDiss p.d p.s :=
    HRS.MS.MfeConf.sb1_superDiss_of_movEnt hd1 p.hd p.hs0 hsd
      (HRS.MS.MfeConf.sb1_superMovEnt hd1 p.hs0 hsd)
  obtain ⟨εpkg, hεpkg, C₀pkg, CBpkg, hPackageRaw⟩ :=
    fp81s21_particlePackage_commonRadius p hDiss
  let δ0 : ℝ := min δcommon εpkg
  have hδ0 : 0 < δ0 := lt_min hδcommon hεpkg
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hhalf
  refine ⟨δ0, hδ0, ?_⟩
  intro δ hδ hδle R L hL
  have hδcommon' : δ ≤ δcommon := hδle.trans (min_le_left _ _)
  have hδpkg : δ ≤ εpkg := hδle.trans (min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  have hData := hcommon δ hδ hδcommon' R.ρβ R.thermal
  have hOrbit : S103nOrbitClaims p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co := hData.1
  have hTerm : ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      S104bTermRegGen p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ := fun ρβ hρβ =>
        (hcommon δ hδ hδcommon' ρβ hρβ).2.2.1
  have hNL : S104nAllOrb p.d p.s p.a p.β δ p.c₁ p.C₁ :=
    HRS.MS.R2WinErr.s104b_allOrb_of_termRegGen hTerm
  have hOrbitAll : ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      S103nOrbitClaims p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ Co co :=
    fun ρβ hρβ => (hcommon δ hδ hδcommon' ρβ hρβ).1
  have hWindow : ∀ H : ℝ, 0 < H → ∀ ρβ : Euc p.d → ℝ,
      IsThermalEquilibrium p.d p.s p.a p.β ρβ → S103nWindowClause p.d p.s p.a p.β H ρβ δ p.c₁ p.C₁ :=
    fun H hH ρβ hρβ => (hcommon δ hδ hδcommon' ρβ hρβ).2.2.2 H hH
  have hPackage : ∀ H : ℝ, 0 < H → ∃ CT : ℝ,
      fp81s21_ParticlePackage p εpkg C₀pkg CBpkg CT H := by
    intro H hH
    obtain ⟨CT, hpkg⟩ := hPackageRaw H hH
    exact ⟨CT, hpkg⟩
  obtain ⟨C₀, C, hC, hMetric⟩ :=
    fp81s21_fixedRadiusMetric p hδ hδhalf hδpkg hNL hco hOrbitAll hWindow hPackage
      (L + p.T) (by linarith [hL, p.hT])
  refine ⟨C₀, C, hC, ?_⟩
  intro N hN A G a₀ ha₀
  have hGEC : HRS.Whole.GibbsEntropyContraction p.d p.s p.a p.β N :=
    fp81s21_gibbsEntropyContraction p N
  have hbounds := hMetric R.ρβ R.thermal R.ε R.ψ R.admissible R.ρ R.resulting N hN hGEC
    A.P A.X₀ A.W A.X A.brownian A.independent A.initial A.strong
    G.P G.Z G.evolution a₀ ha₀
  exact hbounds.2

/-- The recent observation interval pulls back into the length-`L+T` history window. -/
theorem fp81s21_recentWindowRestriction {a₀ L T : ℝ}
    (ha₀ : 0 ≤ a₀) (hL : 0 < L) (hT : 0 < T) :
    let b := max (a₀ - L) 0
    0 ≤ a₀ - b ∧ ∀ u ∈ Set.Icc (0 : ℝ) T,
      (a₀ - b) + u ∈ Set.Icc (0 : ℝ) (L + T) ∧ b + ((a₀ - b) + u) = a₀ + u := by
  obtain ⟨hb, hshift, hshiftL, hend⟩ := fp81s21_recentWindowGeometry ha₀ hL hT
  refine ⟨hshift, fun u hu => ?_⟩
  constructor
  · constructor <;> linarith [hshift, hu.1, hshiftL, hu.2, hend]
  · ring

/-- S.B.1 gives the dissipation input of S6.6 throughout the parameter range. -/
theorem fp81s21_superDiss_unconditional (p : Parameters) :
    HRS.MS.MfeConf.SuperDiss p.d p.s := by
  have hd1 : 1 ≤ p.d := Nat.le_trans (by decide : 1 ≤ 2) p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have hdpos : (0 : ℝ) < (p.d : ℝ) := by
      exact_mod_cast (Nat.lt_of_lt_of_le (by decide : 0 < 2) p.hd)
    linarith [p.hs, hdpos]
  exact HRS.MS.MfeConf.sb1_superDiss_of_movEnt hd1 p.hd p.hs0 hsd
    (HRS.MS.MfeConf.sb1_superMovEnt hd1 p.hs0 hsd)

#print axioms fp81s21_superDiss_unconditional
#print axioms fp81s21_orbClass_from_commonRadius
#print axioms fp81s21_orbitGrad_commonRadius
#print axioms fp81s21_fixedRadiusMetric
#print axioms fp81s21_leadingAdapter2
#print axioms fp81s21_recentWindowRestriction

end HRS.Fp81.S21

end
