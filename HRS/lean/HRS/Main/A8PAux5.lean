import HRS.Energy.Commutator.CommonProof
import HRS.Main.A8PAux4

/-!
# Packet A8P, part 5: the adjoint package and the pointwise remainder bound
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

/-- The uniform adjoint bounds of Proposition 3.9 at the level `m_*`, in the form used below. -/
def A8AdjSpec (d : ℕ) (s : ℝ) (Rg : PDE.Regime) (MB Λ VB ν₀ Ca Λ₁ : ℝ) : Prop :=
  ∀ (D : DynData d) (T : ℝ) (μ : ℝ → Torus d → ℝ),
    PDE.AdjointData s (PDE.mStar d) Rg MB Λ VB D ν₀ T μ →
    ∀ t ∈ Set.Ioc 0 T, ∀ φ : Torus d → ℝ, Continuous φ → MemSobolev (PDE.mStar d : ℝ) φ →
      IsClassicalAdjointSolution D μ t φ (fun r => propagator D μ r t φ) ∧
      ∀ r ∈ Set.Icc 0 t, MemSobolev (PDE.mStar d : ℝ) (propagator D μ r t φ) ∧
        sobolevNorm (PDE.mStar d : ℝ) (propagator D μ r t φ) ≤
          Real.exp (Λ₁ * (t - r)) * sobolevNorm (PDE.mStar d : ℝ) φ ∧
        Torus.cbNorm 2 (propagator D μ r t φ) ≤
          Ca * Real.exp (Λ₁ * (t - r)) * sobolevNorm (PDE.mStar d : ℝ) φ

theorem a8p_adjSpec (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : PDE.Regime)
    (MB Λ VB ν₀ : ℝ) : ∃ Ca Λ₁ : ℝ, 0 < Ca ∧ A8AdjSpec d s Rg MB Λ VB ν₀ Ca Λ₁ := by
  obtain ⟨Ca, Cs, hCa, hCs, h⟩ := PDE.adjoint_torus_classical hd s hs0 hsd (PDE.mStar d) le_rfl Rg MB Λ VB
  refine ⟨Ca, Rg.lambdaM (Cs (PDE.mStar d)) ν₀ (PDE.thetaOrder d s), hCa, ?_⟩
  intro D T μ hA t ht φ hc hm
  obtain ⟨hsol, hprop, hnorm, hcb⟩ := h D ν₀ T μ hA t ht φ hc hm
  refine ⟨gfb2_propagator_isClassical ⟨_, hsol⟩, fun r hr => ?_⟩
  have h3 : 1 ≤ PDE.mStar d := by have := PDE.ClassicalPart.three_le_mStar d; omega
  obtain ⟨h1, h2⟩ := hnorm (PDE.mStar d) h3 le_rfl r hr
  exact ⟨h1, h2, hcb r hr⟩

section Pkg

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- `K(t, φ) = e^{|Λ₁| t} ‖φ‖_{H^{m_*}}`. -/
def a8pK (Λ₁ t : ℝ) (φ : Torus d → ℝ) : ℝ := Real.exp (|Λ₁| * t) * sobolevNorm (PDE.mStar d : ℝ) φ

theorem a8pK_nonneg (Λ₁ t : ℝ) (φ : Torus d → ℝ) : 0 ≤ a8pK Λ₁ t φ :=
  mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

/-- The classical adjoint solution, the `H^{m_*}`/`C²` bounds, for every `t ∈ [0,T]` (including `t = 0`). -/
theorem a8p_adj_pkg (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (PDE.mStar d : ℝ) φ) :
    Torus.IsCk 2 φ ∧
    IsClassicalAdjointSolution (S.dyn N) (S.ρ N) t φ (fun r => propagator (S.dyn N) (S.ρ N) r t φ) ∧
    ∀ r ∈ Set.Icc 0 t, MemSobolev (PDE.mStar d : ℝ) (propagator (S.dyn N) (S.ρ N) r t φ) ∧
      sobolevNorm (PDE.mStar d : ℝ) (propagator (S.dyn N) (S.ρ N) r t φ) ≤ a8pK Λ₁ t φ ∧
      Torus.cbNorm 2 (propagator (S.dyn N) (S.ρ N) r t φ) ≤ Ca * a8pK Λ₁ t φ := by
  have hAdj := a8p_adjointData hS hN
  have hT0 : (0 : ℝ) < S.T := S.hT
  obtain ⟨hclT, hbT⟩ := hspec (S.dyn N) S.T (S.ρ N) hAdj S.T ⟨hT0, le_rfl⟩ φ hφc hφ
  have hterm : propagator (S.dyn N) (S.ρ N) S.T S.T φ = φ := hclT.terminal
  have hCk : Torus.IsCk 2 φ := by
    have := hclT.c2 S.T ⟨hT0.le, le_rfl⟩
    rwa [hterm] at this
  have hcbφ : Torus.cbNorm 2 φ ≤ Ca * sobolevNorm (PDE.mStar d : ℝ) φ := by
    have := (hbT S.T ⟨hT0.le, le_rfl⟩).2.2
    rwa [hterm, sub_self, mul_zero, Real.exp_zero, mul_one] at this
  refine ⟨hCk, ?_⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · -- `t = 0`
    subst h0
    have hd1 : 1 ≤ d := S.hd
    have hK : PDE.ClassicalAux.ConvKernelFacts d (S.dyn N).s := PDE.ClassicalAux.convKernelFacts hd1 (S.dyn N)
    have hV1 : Torus.IsCk 1 (S.dyn N).V := by
      have := hAdj.hV.1
      exact (this.of_le (by exact_mod_cast (by omega : 1 ≤ PDE.mStar d + 3)))
    have hμ1 : Torus.IsCk 1 (S.ρ N 0) := by
      have := (a8p_coeffHyp hS hN).smooth 0 ⟨le_rfl, S.hT.le⟩
      exact (this.of_le (by exact_mod_cast (by omega : 1 ≤ PDE.mStar d + 3)))
    have hcl0 := PDE.MFSemigroup.isClassical_zero (S.dyn N) hK hV1 (S.ρ N) hμ1 hCk
    have hcl := gfb2_propagator_isClassical ⟨_, hcl0⟩
    have hp0 : propagator (S.dyn N) (S.ρ N) 0 0 φ = φ :=
      PDE.MFSemigroup.propagator_zero (S.dyn N) hK hV1 (S.ρ N) hμ1 hCk
    refine ⟨hcl, fun r hr => ?_⟩
    have hr0 : r = 0 := le_antisymm hr.2 hr.1
    subst hr0
    rw [hp0]
    refine ⟨hφ, ?_, ?_⟩
    · simp [a8pK]
    · simpa [a8pK] using hcbφ
  · obtain ⟨hcl, hb⟩ := hspec (S.dyn N) S.T (S.ρ N) hAdj t ⟨hpos, ht.2⟩ φ hφc hφ
    refine ⟨hcl, fun r hr => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hb r hr
    have hexp : Real.exp (Λ₁ * (t - r)) ≤ Real.exp (|Λ₁| * t) := by
      refine Real.exp_le_exp.2 ?_
      calc Λ₁ * (t - r) ≤ |Λ₁| * (t - r) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith [hr.2])
        _ ≤ |Λ₁| * t := mul_le_mul_of_nonneg_left (by linarith [hr.1]) (abs_nonneg _)
    have hsob0 : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) φ := Real.sqrt_nonneg _
    refine ⟨h1, h2.trans (mul_le_mul_of_nonneg_right hexp hsob0), ?_⟩
    refine h3.trans ?_
    unfold a8pK
    nlinarith [mul_le_mul_of_nonneg_right hexp hsob0, mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp hsob0) hCa]

end Pkg


/-- The conclusion of `commutator_coercivity_common` for a fixed pair `(C₀*, Cq)`. -/
def A8CommSpec (d : ℕ) (s C₀ Cq : ℝ) : Prop :=
  ∀ (Λ : ℝ), 1 ≤ Λ → ∀ (N : ℕ), 2 ≤ N →
    ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
    ∀ X : Config d N, X ∉ collisionSet d N →
      0 ≤ rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N ∧
      (∀ (v : Torus d → Euc d) (K : ℝ), HasTransportBound d s v K →
        |commQuantity d s v X (withDensityReal ρ)| ≤
          Cq * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N)) ∧
      (∀ (ψ : Torus d → ℝ) (L : ℝ), 0 ≤ L → KernelGrad.IsLipschitz L ψ →
        HasFiniteHomSobolev (((d : ℝ) - s) / 2) ψ →
        |∫ x, ψ x ∂(empirical X) - ∫ x, ψ x ∂(withDensityReal ρ)| ≤
          Cq * L * smearScale d N Λ +
            Cq * homSobolev (((d : ℝ) - s) / 2) ψ *
              Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N))

theorem a8p_commSpec (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ Cq : ℝ, 0 ≤ C₀ ∧ 0 < Cq ∧ A8CommSpec d s C₀ Cq := by
  obtain ⟨C₀, C, h0, hC, h⟩ := commutator_coercivity_common_proof hd hs0 hsd
  exact ⟨C₀, C, h0, hC, h⟩

/-- Spec monotone in the completion constant. -/
theorem A8CommSpec.mono {s C₀ C₀' Cq : ℝ} (h : A8CommSpec d s C₀ Cq) (hC : C₀ ≤ C₀') (hCq : 0 ≤ Cq) :
    A8CommSpec d s C₀' Cq := by
  intro Λ hΛ N hN ρ hρ hup X hX
  obtain ⟨hlow, hcb, htest⟩ := h Λ hΛ N hN ρ hρ hup X hX
  have hmono := oNΛ_mono_C₀ (d := d) (s := s) (Λ := Λ) hC (by linarith) N
  refine ⟨by linarith, fun v K hK => ?_, fun ψ L hL hψ hfin => ?_⟩
  · have hK0 := hK.nonneg
    refine (hcb v K hK).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hCq hK0)
  · refine (htest ψ L hL hψ hfin).trans ?_
    have hs : Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) ≤
        Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀' Λ N) :=
      Real.sqrt_le_sqrt (by linarith)
    have hh : 0 ≤ homSobolev (((d : ℝ) - s) / 2) ψ := Real.sqrt_nonneg _
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg hCq hh)
    linarith

/-- The pointwise commutator estimate for the remainder integrand `flucInteraction`. -/
theorem a8p_rem_pointwise (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {C₀ Cq : ℝ}
    (hcom : A8CommSpec d s C₀ Cq) (hCq : 0 ≤ Cq) {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 2 ≤ N)
    {D : DynData d} (hDs : D.s = s) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hup : ∀ x, ρ x ≤ Λ)
    {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) {K : ℝ}
    (hTB : HasTransportBound d s (gfb2_v D.M ψ) K) (X : Config d N) (hX : X ∉ collisionSet d N) :
    |flucInteraction D ψ X ρ| ≤
      (1 / 2) * (Cq * K) * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  obtain ⟨hlow, hcb, -⟩ := hcom Λ hΛ N hN ρ hρ hup X hX
  obtain ⟨L, F, hL, hF, hlip, hfrac, hLK⟩ := hTB
  have hOff := HRS.Commutator.offDiagIntegrable_of_lipschitz hd hs0 hsd hρ hup X hL hlip
  have hflu := gfb2_flucInteraction_eq D hψ X ρ (by
    intro i
    have := hOff.1 i
    simpa [hDs] using this)
  have hcb' := hcb (gfb2_v D.M ψ) K ⟨L, F, hL, hF, hlip, hfrac, hLK⟩
  rw [hflu, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hDs]
  have : |commQuantity d s (gfb2_v D.M ψ) X (withDensityReal ρ)| ≤
      Cq * K * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := hcb'
  nlinarith

end HRS.Main.A8P
