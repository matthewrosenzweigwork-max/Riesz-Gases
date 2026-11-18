import HRS.Main.A8PAux34

/-!
# Packet A8P, part 35: the smooth-metric bound with the master rate (index set `Fin q`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_smear_le (hd : 1 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 1 ≤ N) :
    smearScale d N Λ ≤ ((N : ℝ) ^ (-(1 : ℝ) / (2 * d))) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold smearScale
  have h1 : ((N : ℝ) ^ (-(1 : ℝ) / (2 * d))) ^ 2 = (N : ℝ) ^ (-(1 : ℝ) / d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 1
    field_simp
    norm_num
  rw [h1, Real.mul_rpow hNr.le (by linarith)]
  have h2 : Λ ^ (-(1 : ℝ) / d) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hΛ (by
      have : (0 : ℝ) ≤ 1 / d := by positivity
      have e : -(1 : ℝ) / d = -(1 / d) := by ring
      rw [e]; linarith)
  have h3 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg hNr.le _
  nlinarith

section Final

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_smooth_final (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
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
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
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
  have hT0 : 0 ≤ S.T := S.hT.le
  have hΛ := a8p_Lam_ge_one hS
  obtain ⟨hq0, hq1⟩ := a8p_q_bounds S hN1
  have hσ := a8p_sigma_nonneg S N
  have hE := hS.energy.pos N hN1
  have hK : 0 ≤ ∑ a, a8pK Λ₁ (ts a) (φ a) := Finset.sum_nonneg fun a _ => a8pK_nonneg Λ₁ (ts a) (φ a)
  have hsm := a8p_smear_le S.hd hΛ hN1
  have hsm0 : 0 ≤ smearScale d N Λ := by
    unfold smearScale
    exact Real.rpow_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity) _
  have hu : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / (2 * d)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hqeq := a8p_q_eq S N
  have hrem := a8p_remConst_eq S N Cq cT Λ₁ ts φ
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN1
  have hb4 : 0 ≤ (𝔈 N) ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hE.le _
  set Ks : ℝ := ∑ a, a8pK Λ₁ (ts a) (φ a) with hKs
  have hsumeI : ∑ a, eI * a8pK Λ₁ (ts a) (φ a) = eI * Ks := (Finset.mul_sum _ _ _).symm
  have hmain : ∀ Ccov : ℝ,
      covDiscrepancyMatrix (R N).P S.T (a8pSg S R N ts φ) (a8pSb S N ts φ) ≤ Ccov →
      smoothDist 2
        (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      S.sigma N * ((1 / 2) * (Cq * cT)) * Ks * (S.T * 𝔈 N) + eI * Ks + (1 / 2) * Ccov := by
    intro Ccov hcov
    have h := a8p_smooth_core hspec hCa hS hN hcom hCq hC hcT0 hcT ts hts φ hφc hφ hcov hη heI hIdiff
    rw [hrem, hsumeI] at h
    exact h
  have hrate : 0 ≤ masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N := by
    unfold masterRate
    have := Real.sqrt_nonneg (S.qN N)
    have : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / (2 * d)) := hu
    positivity
  have hKK : 0 ≤ Ks + Ks ^ 2 := by positivity
  by_cases hr : masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N < 1
  · have hcov : covDiscrepancyMatrix (R N).P S.T (a8pSg S R N ts φ) (a8pSb S N ts φ) ≤
        a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ :=
      a8p_cov_cost hspec hCa hS hN hcom hCq hC hCp0 hCp ts hts φ hφc hφ hF.progressive hnull
    refine (hmain _ hcov).trans ?_
    rw [a8p_covCost_eq, ← hqeq]
    have harith := a8p_arith_smooth_cost (K := Ks) (ε := eI) (σ := S.sigma N) (E := 𝔈 N)
      (q := S.qN N) (sm := smearScale d N Λ) (u := (N : ℝ) ^ (-(1 : ℝ) / (2 * d))) (T := S.T)
      (Cq := Cq) (cT := cT) (Ca := Ca) (Cp := Cp) (dd := d) hK heI hσ hE hq0 hsm0 hsm hu hT0 hCq hcT0
      hCp0 (Nat.cast_nonneg d) hr
    have hmono : ((1 / 2) * Cq * cT * S.T + 1 + 2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp)) * (Ks + Ks ^ 2) *
        masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N ≤
        ((1 / 2) * Cq * cT * S.T + 1 + 4 * S.T * d * Ca ^ 2 + 2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp)) *
          (Ks + Ks ^ 2) * masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hKK) hrate
      have : 0 ≤ 4 * S.T * d * Ca ^ 2 := by positivity
      linarith
    unfold masterRate at hmono harith ⊢
    refine le_trans (le_of_eq ?_) (harith.trans hmono)
    ring
  · push_neg at hr
    have hcov : covDiscrepancyMatrix (R N).P S.T (a8pSg S R N ts φ) (a8pSb S N ts φ) ≤
        a8pCovCostTriv S N Ca Λ₁ ts φ :=
      a8p_cov_cost_triv hspec hCa hS hN1 ts hts φ hφc hφ
    refine (hmain _ hcov).trans ?_
    rw [a8p_covCostTriv_eq, ← hqeq]
    have hr' : eI + S.sigma N * 𝔈 N ≤ masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N := by
      unfold masterRate
      have := mul_nonneg (Real.sqrt_nonneg (S.qN N)) (add_nonneg hb4 hu)
      linarith
    have harith := a8p_arith_smooth_triv (K := Ks) (ε := eI) (σ := S.sigma N) (E := 𝔈 N)
      (q := S.qN N) (T := S.T) (Cq := Cq) (cT := cT) (Ca := Ca) (dd := d)
      (r := masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) hK heI hσ hE hq0 hq1 hT0 hCq hcT0
      (Nat.cast_nonneg d) hr' hr
    have hmono : ((1 / 2) * Cq * cT * S.T + 1 + 4 * S.T * d * Ca ^ 2) * (Ks + Ks ^ 2) *
        masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N ≤
        ((1 / 2) * Cq * cT * S.T + 1 + 4 * S.T * d * Ca ^ 2 + 2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp)) *
          (Ks + Ks ^ 2) * masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hKK) hrate
      have : 0 ≤ 2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp) := by positivity
      linarith
    refine le_trans (le_of_eq ?_) (harith.trans hmono)
    ring

end Final

end HRS.Main.A8P
