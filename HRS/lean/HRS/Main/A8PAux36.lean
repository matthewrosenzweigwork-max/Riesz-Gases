import HRS.Main.A8PAux35

/-!
# Packet A8P, part 36: the Wasserstein bounds with the master rate (index set `Fin q`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_sum_ofReal {x y z B : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z ≤ B) :
    ENNReal.ofReal x + ENNReal.ofReal y + ENNReal.ofReal z ≤ ENNReal.ofReal B := by
  rw [← ENNReal.ofReal_add hx hy, ← ENNReal.ofReal_add (add_nonneg hx hy) hz]
  exact ENNReal.ofReal_le_ofReal h

section Final2

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_wass_final (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
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
    wassersteinE 1
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
    ENNReal.ofReal (((1 / 2) * Cq * cT * S.T + 1 +
        Real.sqrt (2 * S.T * Cq * (2 * d * Ca ^ 2 + Cp))) *
      ((∑ a, a8pK Λ₁ (ts a) (φ a)) + (∑ a, a8pK Λ₁ (ts a) (φ a)) ^ 2) *
      masterRate d eI (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have hΛ := a8p_Lam_ge_one hS
  obtain ⟨hq0, hq1⟩ := a8p_q_bounds S hN1
  have hσ := a8p_sigma_nonneg S N
  have hE := hS.energy.pos N hN1
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N hN1
  have hKa : ∀ a, 0 ≤ a8pK Λ₁ (ts a) (φ a) := fun a => a8pK_nonneg Λ₁ (ts a) (φ a)
  have hK : 0 ≤ ∑ a, a8pK Λ₁ (ts a) (φ a) := Finset.sum_nonneg fun a _ => hKa a
  have hsm := a8p_smear_le S.hd hΛ hN1
  have hsm0 : 0 ≤ smearScale d N Λ := by
    unfold smearScale
    exact Real.rpow_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity) _
  have hu : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / (2 * d)) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hqeq := a8p_q_eq S N
  have hcore := a8p_wass_core hspec hCa hS hN hcom hCq hC hCp0 hCp ts hts φ hφc hφ hnull hη
    (p := 1) le_rfl (by norm_num)
  have hT1 : ∫⁻ ω, ENNReal.ofReal (‖a8pIemp S R N ts φ ω - a8pItil S R N ts φ ω‖ ^ (1 : ℝ)) ∂(R N).P ≤
      ENNReal.ofReal (∑ a, eI * a8pK Λ₁ (ts a) (φ a)) := by
    refine a8p_vec_L1 _ (fun a => ?_) (fun a => mul_nonneg heI (hKa a)) hIdiff
    have hIm : Measurable fun ω => (a8pIemp S R N ts φ ω) a := by
      have : Measurable fun ω => flucPair ((R N).X 0 ω) (S.ρ N 0)
          (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)) := by
        obtain ⟨-, hcl, -⟩ := a8p_adj_pkg hspec hCa hS hN1 (hts a) (hφc a) (hφ a)
        exact a8p_flucPair_meas ((hF.adapted 0).mono (ℱ.le _) le_rfl)
          (Q54c.isCk_continuous (hcl.c2 0 ⟨le_rfl, (hts a).1⟩)) _
      exact this.const_mul _
    exact hIm.sub (measurable_const.mul (hη _))
  have hT3 := a8p_rem_L1 hspec hCa hS hN hF hcom hCq hC hcT0 hcT ts hts φ hφc hφ
  set Ks : ℝ := ∑ a, a8pK Λ₁ (ts a) (φ a) with hKs
  have hsumeI : ∑ a, eI * a8pK Λ₁ (ts a) (φ a) = eI * Ks := (Finset.mul_sum _ _ _).symm
  rw [hsumeI] at hT1
  rw [a8p_remConst_eq] at hT3
  have e1 : ∀ X : ℝ≥0∞, X ^ (1 / (1 : ℝ)) = X := fun X => by simp
  simp only [e1] at hcore
  have hcostE : Real.sqrt (a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ) =
      Real.sqrt (2 * S.qN N * S.T * Cq * (2 * d * Ca ^ 2 * smearScale d N Λ + Cp * Real.sqrt (𝔈 N))) * Ks := by
    rw [a8p_covCost_eq, ← hqeq]
    have hA : 0 ≤ 2 * S.qN N * S.T * Cq * (2 * d * Ca ^ 2 * smearScale d N Λ + Cp * Real.sqrt (𝔈 N)) := by
      have := Real.sqrt_nonneg (𝔈 N)
      positivity
    rw [Real.sqrt_mul hA, Real.sqrt_sq hK]
  have harith := a8p_arith_wass (K := Ks) (ε := eI) (σ := S.sigma N) (E := 𝔈 N) (E' := 𝔈 N)
    (q := S.qN N) (sm := smearScale d N Λ) (u := (N : ℝ) ^ (-(1 : ℝ) / (2 * d))) (T := S.T)
    (Cq := Cq) (cT := cT) (Ca := Ca) (Cp := Cp) (dd := d) hK heI hσ hE hE.le hq0 hsm0 hsm hu hT0 hCq
    hcT0 hCp0 (Nat.cast_nonneg d)
  have hcR0 : 0 ≤ S.sigma N * ((1 / 2) * (Cq * cT)) * Ks * (S.T * 𝔈 N) := by positivity
  calc _ ≤ _ := hcore
    _ ≤ ENNReal.ofReal (eI * Ks) + ENNReal.ofReal (Real.sqrt (a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ)) +
        ENNReal.ofReal (S.sigma N * ((1 / 2) * (Cq * cT)) * Ks * (S.T * 𝔈 N)) := by
          gcongr
    _ ≤ _ := by
          refine a8p_sum_ofReal (by positivity) (Real.sqrt_nonneg _) hcR0 ?_
          rw [hcostE]
          unfold masterRate
          linarith [harith]

end Final2

end HRS.Main.A8P
