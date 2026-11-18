import HRS.Main.A9Aux17

/-!
# Packet A9, part 18: the per-`N` field bound in terms of `fieldRate` plus the mode tail
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a9_smear_le (hd : 1 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 1 ≤ N) :
    smearScale d N Λ ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ((N : ℝ) ^ (-(1 : ℝ) / (2 * d))) ^ 2 = (N : ℝ) ^ (-(1 : ℝ) / d) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 1
    field_simp
    norm_num
  have := a8p_smear_le hd hΛ hN
  rwa [h1] at this

section Main

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

theorem a9_cost_nonneg (hCa : 0 ≤ Ca) (hCq : 0 ≤ Cq) (hCp : 0 ≤ Cp) (hΛ : 1 ≤ Λ) {N : ℕ}
    {E t : ℝ} (hE : 0 ≤ E) {q : ℕ} (k : Fin q → NonzeroLattice d) :
    0 ≤ a8pCovCost S N Cq Cp Ca Λ₁ Λ E (fun _ : Fin q => t) (fun a => a9phi d (k a)) := by
  have hT := S.hT.le
  have hq0 : 0 ≤ S.sigma N ^ 2 * S.invβ N / N := by
    have := S.hinvβ N
    positivity
  have hsm : 0 ≤ smearScale d N Λ := by
    unfold smearScale
    exact Real.rpow_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity) _
  unfold a8pCovCost
  refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
  have h1 := a8pK_nonneg Λ₁ ((fun _ : Fin q => t) a) ((fun a => a9phi d (k a)) a)
  have h2 := a8pK_nonneg Λ₁ ((fun _ : Fin q => t) b) ((fun a => a9phi d (k a)) b)
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have := Real.sqrt_nonneg E
  positivity

theorem a9_field_bound (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    {Ktr : ℝ} (hKtr0 : 0 ≤ Ktr)
    (hKtr : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData S.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * Ktr)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {Cin : ℝ} {εf : ℕ → ℝ} {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)}
    {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG)
    {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k) {Kb : ℝ}
    (hKb : ∑' j, a9K d Λ₁ t j ≤ Kb) :
    smoothDist 2 (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
      (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
    Ktr * εf N + ((1 / 2) * Cq * cT * S.T * Kb) * (S.sigma N * 𝔈 N) +
      (S.T * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp)) *
        (S.qN N * ((𝔈 N) ^ ((1 : ℝ) / 2) + (N : ℝ) ^ (-(1 : ℝ) / d))) +
      (2 * Real.sqrt (2 * S.T) * (d * Ca)) * a9tail d Λ₁ t k := by
  have hP' := hP
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP'
  have hS' := a9_standing_mStar hS
  have hN1 : 1 ≤ N := by omega
  have hT := S.hT.le
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hσ := a8p_sigma_nonneg S N
  have hΛ1 := a8p_Lam_ge_one hS'
  have hqe := a8p_q_eq S N
  obtain ⟨hq0, hq1⟩ := a8p_q_bounds S hN1
  have hεf := hfield.εf_nonneg N hN1
  have hsm := a9_smear_le S.hd hΛ1 hN1
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hKtot0 : 0 ≤ ∑' j, a9K d Λ₁ t j := tsum_nonneg fun j => a9K_nonneg _ _ _
  have hKb0 : 0 ≤ Kb := hKtot0.trans hKb
  have hcost0 := a9_cost_nonneg (S := S) (N := N) hCa hCq hCp0 hΛ1 h𝔈 (Λ₁ := Λ₁) (t := t) k
  have hbQ0 : ∀ j, 0 ≤ a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j :=
    fun j => a9bQ_nonneg hCa hCq hcT0 hN1 h𝔈 k j
  have hbG0 : ∀ j, 0 ≤ a9bG S N Ca Λ₁ t k j := fun j => by
    unfold a9bG; split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  have hRHS0 : 0 ≤ Ktr * εf N + ∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j +
      (1 / 2) * a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) (fun _ : Fin q => t) (fun a => a9phi d (k a)) +
      ∑' j, a9bG S N Ca Λ₁ t k j := by
    have h1 : 0 ≤ ∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j := tsum_nonneg hbQ0
    have h2 : 0 ≤ ∑' j, a9bG S N Ca Λ₁ t k j := tsum_nonneg hbG0
    have h3 := mul_nonneg hKtr0 hεf
    linarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 1/2) hcost0]
  have hle : smoothDist 2 (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
      (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
      Ktr * εf N + ∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j +
        (1 / 2) * a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) (fun _ : Fin q => t) (fun a => a9phi d (k a)) +
        ∑' j, a9bG S N Ca Λ₁ t k j := by
    refine Real.iSup_le (fun Φ => ?_) hRHS0
    exact a9_core_Phi hP hKtr0 hKtr hS hN hfield ht hνG hk Φ.1 Φ.2
  refine hle.trans ?_
  rw [a9bQ_tsum hCq hcT0 hCa hN1 h𝔈 k, a9bG_tsum hCa k]
  have hcost := a9_cost_le (S := S) (Cq := Cq) (Cp := Cp) hCa hCq hCp0 hΛ1 hN1 h𝔈 hk hKb
  -- the pieces
  set tl := a9tail d Λ₁ t k with htl
  have htl0 : 0 ≤ tl := a9tail_nonneg Λ₁ t k
  have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa
  have hs2 : Real.sqrt (2 * S.T) ≥ 0 := Real.sqrt_nonneg _
  have hcM : Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) ≤ Real.sqrt (2 * S.T) := by
    refine Real.sqrt_le_sqrt ?_
    rw [← hqe]
    nlinarith
  have hcG : Real.sqrt (2 * S.qN N * t) ≤ Real.sqrt (2 * S.T) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [ht.1, ht.2]
  have e1 : S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) * ∑' j, a9K d Λ₁ t j ≤
      ((1 / 2) * Cq * cT * S.T * Kb) * (S.sigma N * 𝔈 N) := by
    have h0 : 0 ≤ S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) := by positivity
    calc _ ≤ S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) * Kb :=
          mul_le_mul_of_nonneg_left hKb h0
      _ = _ := by ring
  have e2 : Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * ((d : ℝ) * Ca) * tl +
      Real.sqrt (2 * S.qN N * t) * ((d : ℝ) * Ca) * tl ≤
      (2 * Real.sqrt (2 * S.T) * (d * Ca)) * tl := by
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcM hCd) htl0
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcG hCd) htl0
    linarith
  have e3 : (1 / 2) * a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) (fun _ : Fin q => t)
      (fun a => a9phi d (k a)) ≤ (S.T * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp)) *
        (S.qN N * ((𝔈 N) ^ ((1 : ℝ) / 2) + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
    have hsq : (𝔈 N) ^ ((1 : ℝ) / 2) = Real.sqrt (𝔈 N) := (Real.sqrt_eq_rpow _).symm
    rw [hsq]
    have hsr := Real.sqrt_nonneg (𝔈 N)
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h1 : 2 * (S.sigma N ^ 2 * S.invβ N / N) * (S.T * Cq * (2 * d * Ca ^ 2 * smearScale d N Λ +
        Cp * Real.sqrt (𝔈 N))) * Kb ^ 2 ≤
        2 * S.qN N * (S.T * Cq * ((2 * d * Ca ^ 2 + Cp) * ((N : ℝ) ^ (-(1 : ℝ) / d) +
          Real.sqrt (𝔈 N)))) * Kb ^ 2 := by
      rw [← hqe]
      have hA : 0 ≤ 2 * (d : ℝ) * Ca ^ 2 := by positivity
      have hdiff : 0 ≤ S.T * Cq * Kb ^ 2 * S.qN N *
          (2 * d * Ca ^ 2 * (Real.sqrt (𝔈 N) + ((N : ℝ) ^ (-(1 : ℝ) / d) - smearScale d N Λ)) +
            Cp * (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have h5 : 0 ≤ Real.sqrt (𝔈 N) + ((N : ℝ) ^ (-(1 : ℝ) / d) - smearScale d N Λ) := by
          linarith
        have h6 := mul_nonneg hA h5
        have h7 := mul_nonneg hCp0 hn0
        have h8 : 0 ≤ S.T * Cq * Kb ^ 2 * S.qN N :=
          mul_nonneg (mul_nonneg (mul_nonneg hT hCq) (sq_nonneg _)) hq0
        exact mul_nonneg h8 (by nlinarith [h6, h7])
      linarith [hdiff]
    have h2 : (1 / 2) * a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) (fun _ : Fin q => t)
        (fun a => a9phi d (k a)) ≤
        (1 / 2) * (2 * (S.sigma N ^ 2 * S.invβ N / N) * (S.T * Cq * (2 * d * Ca ^ 2 *
          smearScale d N Λ + Cp * Real.sqrt (𝔈 N))) * Kb ^ 2) := by
      have := hcost
      linarith
    refine h2.trans ?_
    refine (mul_le_mul_of_nonneg_left h1 (by norm_num)).trans (le_of_eq ?_)
    ring
  linarith [e1, e2, e3]

end Main

end HRS.Main.A9
