import HRS.Main.A8PAux15
import HRS.Main.A8PAux9

/-!
# Packet A8P, part 16: pathwise covariance bound for a.e. time
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section CovPt

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- The transported test family `r ↦ U^{r,t_a} φ_a`. -/
def a8pF (S : MainData d) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (a : Fin q) :
    ℝ → Torus d → ℝ :=
  fun r => propagator (S.dyn N) (S.ρ N) r (ts a) (φ a)

theorem a8p_cov_rpt (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {C₀' Cq Cp : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hCp0 : 0 ≤ Cp)
    (hCp : ∀ f g : Torus d → ℝ, Torus.IsCk 2 f → Torus.IsCk 2 g →
      MemSobolev (PDE.mStar d : ℝ) f → MemSobolev (PDE.mStar d : ℝ) g →
      HasFiniteHomSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
      homSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
        Cp * sobolevNorm (PDE.mStar d : ℝ) f * sobolevNorm (PDE.mStar d : ℝ) g)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    (ω : (R N).Ω)
    (hω : volume {s : ℝ | s ∈ Set.Icc 0 S.T ∧ (R N).X (Real.toNNReal s) ω ∈ collisionSet d N} = 0) :
    ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)), ∀ a b,
      |killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts r ω a b -
          a8pSigBar ts (a8pG ts (a8pF S N ts φ)) (fun r => S.ρ N (Q54c.clampT S.T r))
            (2 * (S.sigma N ^ 2 * S.invβ N / N)) r a b| ≤
        2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (Cq * (2 * d * (Ca * a8pK Λ₁ (ts a) (φ a)) * (Ca * a8pK Λ₁ (ts b) (φ b))) * smearScale d N Λ +
            Cq * (Cp * a8pK Λ₁ (ts a) (φ a) * a8pK Λ₁ (ts b) (φ b)) *
              Real.sqrt (a8pEn S R N C₀ Λ r ω)) := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have hΛ := a8p_Lam_ge_one hS
  have hcom' := hcom.mono hC hCq
  have hpk := fun a => a8p_adj_pkg hspec hCa hS hN1 (hts a) (hφc a) (hφ a)
  have hnull : ∀ᵐ r ∂(volume : Measure ℝ),
      ¬ (r ∈ Set.Icc 0 S.T ∧ (R N).X (Real.toNNReal r) ω ∈ collisionSet d N) :=
    measure_eq_zero_iff_ae_notMem.1 hω
  have hq0 : 0 ≤ S.sigma N ^ 2 * S.invβ N / N := by
    have := S.hinvβ N
    positivity
  have hsm : 0 ≤ smearScale d N Λ := by
    unfold smearScale
    exact Real.rpow_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity) _
  refine (ae_restrict_iff' measurableSet_Icc).2 ?_
  filter_upwards [hnull] with r hr hrT a b
  have hcoll : (R N).X (Real.toNNReal r) ω ∉ collisionSet d N := fun h => hr ⟨hrT, h⟩
  have hKa := a8pK_nonneg Λ₁ (ts a) (φ a)
  have hKb := a8pK_nonneg Λ₁ (ts b) (φ b)
  have hrhs0 : 0 ≤ 2 * (S.sigma N ^ 2 * S.invβ N / N) *
      (Cq * (2 * d * (Ca * a8pK Λ₁ (ts a) (φ a)) * (Ca * a8pK Λ₁ (ts b) (φ b))) * smearScale d N Λ +
        Cq * (Cp * a8pK Λ₁ (ts a) (φ a) * a8pK Λ₁ (ts b) (φ b)) *
          Real.sqrt (a8pEn S R N C₀ Λ r ω)) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  have he : killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts r ω a b -
          a8pSigBar ts (a8pG ts (a8pF S N ts φ)) (fun r => S.ρ N (Q54c.clampT S.T r))
            (2 * (S.sigma N ^ 2 * S.invβ N / N)) r a b =
      if 0 ≤ r ∧ r < min (ts a) (ts b) then
        2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (∫ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ b r) x)
              ∂(empirical ((R N).X (Real.toNNReal r) ω)) -
            ∫ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ b r) x) *
              S.ρ N (Q54c.clampT S.T r) x)
      else 0 :=
    a8p_cov_entry_eq hN1 (S.dyn N) (S.sigma N) ts (a8pF S N ts φ) (R N).X
      (fun r => S.ρ N (Q54c.clampT S.T r)) r ω a b
  rw [he]
  by_cases h : 0 ≤ r ∧ r < min (ts a) (ts b)
  · rw [if_pos h]
    have hra : r ∈ Set.Icc (0 : ℝ) (ts a) := ⟨h.1, (lt_min_iff.1 h.2).1.le⟩
    have hrb : r ∈ Set.Icc (0 : ℝ) (ts b) := ⟨h.1, (lt_min_iff.1 h.2).2.le⟩
    obtain ⟨hCka, hcla, hba⟩ := hpk a
    obtain ⟨hCkb, hclb, hbb⟩ := hpk b
    obtain ⟨hmema, hnorma, hcba⟩ := hba r hra
    obtain ⟨hmemb, hnormb, hcbb⟩ := hbb r hrb
    have hdens := (hS.mean_field.solution N hN1).density r hrT
    have hpt := a8p_cov_pt hcom' hCq hCp0 hCp hΛ hN hdens (fun x => a8p_rho_le hS hN1 hrT x) hcoll
      (hcla.c2 r hra) (hclb.c2 r hrb) hmema hmemb hnorma hnormb hcba hcbb
    rw [Q54c.clampT_of_mem hrT, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (S.sigma N ^ 2 * S.invβ N / N))]
    have hge := a8pEn_ge S R N C₀ Λ r ω
    unfold correctedEnergy at hge
    have hsq : Real.sqrt (rieszEnergy d S.s ((R N).X (Real.toNNReal r) ω) (withDensityReal (S.ρ N r)) +
        oNΛ d S.s C₀ Λ N) ≤ Real.sqrt (a8pEn S R N C₀ Λ r ω) := Real.sqrt_le_sqrt hge
    have hCK : 0 ≤ Cq * (Cp * a8pK Λ₁ (ts a) (φ a) * a8pK Λ₁ (ts b) (φ b)) := by positivity
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine hpt.trans ?_
    have := mul_le_mul_of_nonneg_left hsq hCK
    linarith
  · rw [if_neg h, abs_zero]
    exact hrhs0

end CovPt

end HRS.Main.A8P
