import HRS.Main.A9Aux7

/-!
# Packet A9, part 8: first moment of `Z_k - 𝕀_k` for one mode (a.e. `Z_k - 𝕀_k = M_k + R_k`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

section Mode1

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- A.s. `Z_k - 𝕀_k = M_k + R_k` for the family `{(t, φ_k)}` (a8p_decomp at `q = 1`, coordinate `0`). -/
theorem a9_ZI_decomp (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d) :
    ∀ᵐ ω ∂(R N).P,
      NegSobolev.coord (a9Z S R N t ω) k - NegSobolev.coord (a9I S R N t ω) k =
        vectorItoIntegral (R N).P ℱ W'
          (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) ((fun _ : Fin 1 => t) a)
            (a8pF S N (fun _ : Fin 1 => t) (fun _ => a9phi d k) a) (R N).X) ((fun _ : Fin 1 => t) a))
          S.T ω 0 +
        a8pRem S R N (fun _ : Fin 1 => t) (fun _ => a9phi d k) ω 0 := by
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hdec := a8p_decomp hspec hCa hS' hN hF (fun _ : Fin 1 => t) (fun _ => ht) (fun _ => a9phi d k)
    (fun _ => a9phi_cont k) (fun _ => a9phi_mem _ k)
  filter_upwards [hdec] with ω h
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 1) => v 0) h
  simp only [fluctStat, a8pIemp, PiLp.add_apply] at h0
  rw [a9_Z_coord hS' hN1 ht, a9_I_coord hS hN1 ht]
  have e : S.sigma N * flucPair ((R N).X (Real.toNNReal t) ω) (S.ρ N t) (a9phi d k) =
      S.sigma N * (pair (empirical ((R N).X (Real.toNNReal t) ω)) (a9phi d k) -
        pair (withDensityReal (S.ρ N t)) (a9phi d k)) := rfl
  rw [e, h0]
  ring

theorem a9_ZI_moment (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d) :
    ∫⁻ ω, ENNReal.ofReal |NegSobolev.coord (a9Z S R N t ω) k - NegSobolev.coord (a9I S R N t ω) k|
        ∂(R N).P ≤
      ENNReal.ofReal (Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (d * (Ca * a8pK Λ₁ t (a9phi d k))) ^ 2)) +
        S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ t (a9phi d k)))) * (S.T * 𝔈 N)) := by
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hdec := a9_ZI_decomp hspec hCa hS hN hF ht k
  have hmart := a9_mart_moment hspec hCa hS' hN hF (fun _ : Fin 1 => t) (fun _ => ht)
    (fun _ => a9phi d k) (fun _ => a9phi_cont k) (fun _ => a9phi_mem _ k) 0
  have hrem := a9_rem_moment hspec hCa hS' hN hF hcom hCq hC hcT0 hcT (fun _ : Fin 1 => t)
    (fun _ => ht) (fun _ => a9phi d k) (fun _ => a9phi_cont k) (fun _ => a9phi_mem _ k) 0
  set Mc : (R N).Ω → ℝ := fun ω => vectorItoIntegral (R N).P ℱ W'
    (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) ((fun _ : Fin 1 => t) a)
      (a8pF S N (fun _ : Fin 1 => t) (fun _ => a9phi d k) a) (R N).X) ((fun _ : Fin 1 => t) a))
    S.T ω 0 with hMc
  set Rc : (R N).Ω → ℝ := fun ω => a8pRem S R N (fun _ : Fin 1 => t) (fun _ => a9phi d k) ω 0
    with hRc
  obtain ⟨hL2, hsq⟩ := hmart
  have hMint : ∫⁻ ω, ENNReal.ofReal |Mc ω| ∂(R N).P ≤ ENNReal.ofReal (Real.sqrt (S.T *
      (2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ t (a9phi d k))) ^ 2))) := by
    have hint : Integrable (fun ω => |Mc ω|) (R N).P := hL2.integrable one_le_two |>.abs
    have e : ENNReal.ofReal (∫ ω, |Mc ω| ∂(R N).P) = ∫⁻ ω, ENNReal.ofReal |Mc ω| ∂(R N).P :=
      ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => abs_nonneg _)
    rw [← e]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (a33_integral_abs_le (P := (R N).P) Mc hL2).trans (Real.sqrt_le_sqrt hsq)
  calc ∫⁻ ω, ENNReal.ofReal |NegSobolev.coord (a9Z S R N t ω) k - NegSobolev.coord (a9I S R N t ω) k|
        ∂(R N).P
      ≤ ∫⁻ ω, (ENNReal.ofReal |Mc ω| + ENNReal.ofReal |Rc ω|) ∂(R N).P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hdec] with ω h
        rw [h, ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = ∫⁻ ω, ENNReal.ofReal |Mc ω| ∂(R N).P + ∫⁻ ω, ENNReal.ofReal |Rc ω| ∂(R N).P := by
        refine lintegral_add_left' ?_ _
        exact (hL2.aestronglyMeasurable.aemeasurable.abs).ennreal_ofReal
    _ ≤ _ := by
        have hσ := a8p_sigma_nonneg S N
        have hK0 := a8pK_nonneg Λ₁ t (a9phi d k)
        have hT0 := S.hT.le
        have hE0 := (hS.energy.pos N hN1).le
        rw [ENNReal.ofReal_add (Real.sqrt_nonneg _) (by
          have : 0 ≤ Cq * (cT * a8pK Λ₁ t (a9phi d k)) := mul_nonneg hCq (mul_nonneg hcT0 hK0)
          positivity)]
        exact add_le_add hMint hrem

end Mode1

end HRS.Main.A9
