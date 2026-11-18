import HRS.Main.A8PAux42

/-!
# Packet A8P, part 43: the per-`N` bounds from the assumptions (cases (b), (a), (d))
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

/-- The package of uniform constants. -/
def A8Pack (d : ℕ) (s : ℝ) (Rg : PDE.Regime) (MB Λ VB ν₀ C₀ : ℝ) (Ca Λ₁ C₀' Cq Cp cT : ℝ) : Prop :=
  0 ≤ Ca ∧ A8AdjSpec d s Rg MB Λ VB ν₀ Ca Λ₁ ∧ A8CommSpec d s C₀' Cq ∧ 0 ≤ Cq ∧ C₀' ≤ C₀ ∧ 0 ≤ Cp ∧
  (∀ f g : Torus d → ℝ, Torus.IsCk 2 f → Torus.IsCk 2 g →
      MemSobolev (PDE.mStar d : ℝ) f → MemSobolev (PDE.mStar d : ℝ) g →
      HasFiniteHomSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
      homSobolev (((d : ℝ) - s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
        Cp * sobolevNorm (PDE.mStar d : ℝ) f * sobolevNorm (PDE.mStar d : ℝ) g) ∧
  0 ≤ cT ∧
  (∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))

section Cases

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

/-- The test data of the transported family: Sobolev membership and norm bound of `U^{0,t_a}φ_a`. -/
theorem a8p_transported_data (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (PDE.mStar d : ℝ) φ) {m₀ : ℕ} (hm₀ : m₀ ≤ PDE.mStar d) :
    MemSobolev (m₀ : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t φ) ∧
    sobolevNorm (m₀ : ℝ) (propagator (S.dyn N) (S.ρ N) 0 t φ) ≤ a8pK Λ₁ t φ := by
  obtain ⟨-, -, hb⟩ := a8p_adj_pkg hspec hCa hS hN ht hφc hφ
  obtain ⟨hmem, hnorm, -⟩ := hb 0 ⟨le_rfl, ht.1⟩
  have hle : (m₀ : ℝ) ≤ (PDE.mStar d : ℝ) := by exact_mod_cast hm₀
  exact ⟨HRS.PDE.MFAdjoint.memSobolev_mono_idx hmem hle,
    (a8p_sobolevNorm_mono hmem hle).trans hnorm⟩

theorem a8p_case_smooth (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : ι → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ}
    (hIF : InitialFluctuation S R m₀ Cin ε (transportedTests S ts φ)) :
    smoothDist 2
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
    ((1 / 2) * Cq * cT * S.T + 1 + 4 * S.T * d * Ca ^ 2 + 2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp)) *
      ((∑ a, a8pK Λ₁ (ts a) (φ a)) + (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2) *
      masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N := by
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hN1 : 1 ≤ N := by omega
  have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
  refine a8p_smooth_iota hspec hCa hS hN hcom hCq hC hCp0 hCp hcT0 hcT ts hts φ hφc hφ
    (a8p_nullContact hS hN1) (hIF.η_meas N) hε (fun a => ?_)
  obtain ⟨hmem, hnorm⟩ := a8p_transported_data hspec hCa hS hN1 (hts a) (hφc a) (hφ a) hIF.m₀_le
  exact a8p_I1_conv hIF hS hN1 (Submodule.subset_span ⟨a, rfl⟩) hmem hnorm

theorem a8p_case_wass1 (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : ι → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ}
    (hIF : InitialFluctuation S R m₀ Cin ε (transportedTests S ts φ)) :
    wassersteinE 1
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
    ENNReal.ofReal (((1 / 2) * Cq * cT * S.T + 1 +
        Real.sqrt (2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp))) *
      ((∑ a, a8pK Λ₁ (ts a) (φ a)) + (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2) *
      masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) := by
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hN1 : 1 ≤ N := by omega
  have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
  refine a8p_wass1_iota hspec hCa hS hN hcom hCq hC hCp0 hCp hcT0 hcT ts hts φ hφc hφ
    (a8p_nullContact hS hN1) (hIF.η_meas N) hε (fun a => ?_)
  obtain ⟨hmem, hnorm⟩ := a8p_transported_data hspec hCa hS hN1 (hts a) (hφc a) (hφ a) hIF.m₀_le
  exact a8p_I1_conv hIF hS hN1 (Submodule.subset_span ⟨a, rfl⟩) hmem hnorm

theorem a8p_case_wass2 (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : ι → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {𝔈' ε2 : ℕ → ℝ}
    (hIF : InitialFluctuation S R m₀ Cin ε (transportedTests S ts φ))
    (hE2 : EnergySmallness2 S R C₀ Λ m₀ (transportedTests S ts φ) 𝔈' ε2) :
    wassersteinE 2
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
    ENNReal.ofReal (((1 / 2) * Cq * cT * S.T + 1 +
        Real.sqrt (2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp))) *
      ((∑ a, a8pK Λ₁ (ts a) (φ a)) + (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2) *
      masterRate d (ε2 N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈' N) N) := by
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP
  have hN1 : 1 ≤ N := by omega
  have hε : 0 ≤ ε2 N := hE2.ε2_nonneg N hN1
  refine a8p_wass2_iota hspec hCa hS hN hcom hCq hC hCp0 hCp hcT0 hcT ts hts φ hφc hφ
    (a8p_nullContact hS hN1) (hIF.η_meas N) hε (fun a => ?_) (hE2.𝔈'_nonneg N hN1) (hE2.bound N hN1)
  obtain ⟨hmem, hnorm⟩ := a8p_transported_data hspec hCa hS hN1 (hts a) (hφc a) (hφ a) hIF.m₀_le
  exact a8p_I1L2_conv hE2 hS hN1 (Submodule.subset_span ⟨a, rfl⟩) hmem hnorm

end Cases

end HRS.Main.A8P
