import HRS.Main.A8PAux39

/-!
# Packet A8P, part 40: the `ι`-indexed smooth bound
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

section Iota

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- Measurability of the statistics vector and positivity of the surrogate covariance. -/
theorem a8p_iota_basics (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    Measurable (fluctStat (S.sigma N) (R N).X (S.ρ N) ts φ) ∧
    (surrogateCov (S.dyn N) (S.ρ N) (S.qN N) ts φ).PosSemidef := by
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN
  have hXm : ∀ t : ℝ≥0, Measurable ((R N).X t) := fun t => (hF.adapted t).mono (ℱ.le _) le_rfl
  refine ⟨?_, ?_⟩
  · refine a8p_vec_meas _ fun a => Measurable.const_mul ?_ _
    exact a8p_flucPair_meas (hXm _) (hφc a) _
  · have hsb := a8p_sb_isDet hspec hCa hS hN ts hts φ hφc hφ
    have hsc := a8p_surrogateCov_eq (S.dyn N) (S.ρ N) (S.qN N) S.T ts φ (fun a => (hts a).2)
      (fun r => S.ρ N (Q54c.clampT S.T r)) (fun r hr => by rw [Q54c.clampT_of_mem hr])
    rw [hsc, a8p_q_eq S N]
    exact integratedCov_psd hsb

theorem a8p_smooth_iota (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {C₀' Cq Cp cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀)
    (hCp0 : 0 ≤ Cp)
    (hCp : ∀ f g : Torus d → ℝ, Torus.IsCk 2 f → Torus.IsCk 2 g →
      MemSobolev (PDE.mStar d : ℝ) f → MemSobolev (PDE.mStar d : ℝ) g →
      HasFiniteHomSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
      homSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
        Cp * sobolevNorm (PDE.mStar d : ℝ) f * sobolevNorm (PDE.mStar d : ℝ) g)
    (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : ι → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    (hnull : NullContactOccupation (R N).P S.T (R N).X)
    (hη : ∀ ψ : Torus d → ℝ, Measurable fun ω => (R N).η ω ψ) {eI : ℝ} (heI : 0 ≤ eI)
    (hIdiff : ∀ a, ∫⁻ ω, ENNReal.ofReal
        |S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)) -
          S.AN N * (R N).η ω (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a))| ∂(R N).P ≤
        ENNReal.ofReal (eI * a8pK Λ₁ (ts a) (φ a))) :
    smoothDist 2
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
    ((1 / 2) * Cq * cT * S.T + 1 + 4 * S.T * d * Ca ^ 2 + 2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp)) *
      ((∑ a, a8pK Λ₁ (ts a) (φ a)) + (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2) *
      masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N := by
  have hN1 : 1 ≤ N := by omega
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ts₂ : Fin (Fintype.card ι) → ℝ := fun j => ts (e.symm j) with hts₂
  set φ₂ : Fin (Fintype.card ι) → Torus d → ℝ := fun j => φ (e.symm j) with hφ₂
  obtain ⟨hmeas, hpsd⟩ := a8p_iota_basics hspec hCa hS hN1 ts₂ (fun j => hts _) φ₂ (fun j => hφc _)
    (fun j => hφ _)
  have hcore := a8p_smooth_final hspec hCa hS hN hcom hCq hC hCp0 hCp hcT0 hcT ts₂ (fun j => hts _) φ₂
    (fun j => hφc _) (fun j => hφ _) hnull hη heI (fun j => hIdiff _)
  rw [a8p_stat_law_reindex e _ _ _ _ ts φ hmeas,
    a8p_surr_law_reindex e _ _ _ _ _ ts φ _ hη hpsd]
  have hsum : ∑ j, a8pK Λ₁ (ts₂ j) (φ₂ j) = ∑ a, a8pK Λ₁ (ts a) (φ a) :=
    Equiv.sum_comp e.symm (fun a => a8pK Λ₁ (ts a) (φ a))
  rw [hsum] at hcore
  haveI : IsProbabilityMeasure (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts₂ φ₂) :=
    inferInstanceAs (IsProbabilityMeasure ((R N).P.map _))
  haveI : IsProbabilityMeasure (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts₂ φ₂
      (R N).P (R N).η) := by
    unfold surrogateStatLaw
    infer_instance
  exact (a8p_smoothDist_relabel e _ _).trans hcore

end Iota

end HRS.Main.A8P
