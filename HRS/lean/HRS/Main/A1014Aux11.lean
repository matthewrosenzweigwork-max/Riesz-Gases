import HRS.Main.A1014Aux10

/-!
# Packet A1014, part 11: the real-number bound of the mode sums, and the per-`k` bounds of `W₁`, `W₂`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A1014

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main HRS.Main.A8P HRS.Main.A9 HRS.GF HRS.Uniform

variable {d : ℕ}

section Sum

variable {S : MainData d} {Ca Cq Cp cT Λ₁ Λ : ℝ}

theorem a1014_cost_le2 (hCa : 0 ≤ Ca) (hCq : 0 ≤ Cq) (hCp : 0 ≤ Cp) (hΛ : 1 ≤ Λ) {N : ℕ}
    (hN : 1 ≤ N) {E t Kb : ℝ} (hE : 0 ≤ E) {q : ℕ} {k : Fin q → NonzeroLattice d}
    (hk : Function.Injective k) (hKb : ∑' j, a9K d Λ₁ t j ≤ Kb) :
    a8pCovCost S N Cq Cp Ca Λ₁ Λ E (fun _ : Fin q => t) (fun a => a9phi d (k a)) ≤
      2 * (S.T * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp)) *
        (S.qN N * (Real.sqrt E + (N : ℝ) ^ (-(1 : ℝ) / d))) := by
  have hT := S.hT.le
  have hqe := a8p_q_eq S N
  obtain ⟨hq0, hq1⟩ := a8p_q_bounds S hN
  have hsm := a9_smear_le S.hd hΛ hN
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hcost := a9_cost_le (S := S) (Cq := Cq) (Cp := Cp) hCa hCq hCp hΛ hN hE hk hKb
  refine hcost.trans ?_
  rw [← hqe]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hsr := Real.sqrt_nonneg E
  have hA : 0 ≤ 2 * (d : ℝ) * Ca ^ 2 := by positivity
  have h1 : 2 * d * Ca ^ 2 * smearScale d N Λ + Cp * Real.sqrt E ≤
      (2 * d * Ca ^ 2 + Cp) * (Real.sqrt E + (N : ℝ) ^ (-(1 : ℝ) / d)) := by
    nlinarith [mul_nonneg hA hsr, mul_nonneg hCp hn0, mul_le_mul_of_nonneg_left hsm hA]
  have h2 : 0 ≤ S.qN N * (S.T * Cq) * Kb ^ 2 := by positivity
  calc 2 * S.qN N * (S.T * Cq * (2 * d * Ca ^ 2 * smearScale d N Λ + Cp * Real.sqrt E)) * Kb ^ 2
      = (2 * (S.qN N * (S.T * Cq) * Kb ^ 2)) *
        (2 * d * Ca ^ 2 * smearScale d N Λ + Cp * Real.sqrt E) := by ring
    _ ≤ (2 * (S.qN N * (S.T * Cq) * Kb ^ 2)) *
        ((2 * d * Ca ^ 2 + Cp) * (Real.sqrt E + (N : ℝ) ^ (-(1 : ℝ) / d))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = _ := by ring

theorem a1014_sum_bound (hCa : 0 ≤ Ca) (hCq : 0 ≤ Cq) (hCp : 0 ≤ Cp) (hcT : 0 ≤ cT) (hΛ : 1 ≤ Λ)
    {N : ℕ} (hN : 1 ≤ N) {𝔈N : ℝ} (h𝔈N : 0 ≤ 𝔈N) {E' : ℝ} (hE' : 0 ≤ E') {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) {q : ℕ} {k : Fin q → NonzeroLattice d}
    (hk : Function.Injective k) {Kb : ℝ} (hKb : ∑' j, a9K d Λ₁ t j ≤ Kb) :
    (∑' j, a9bQ S N Ca Cq cT Λ₁ t E' k j) +
      Real.sqrt (a8pCovCost S N Cq Cp Ca Λ₁ Λ 𝔈N (fun _ : Fin q => t) (fun a => a9phi d (k a))) +
      (∑' j, a9bG S N Ca Λ₁ t k j) ≤
    ((1 / 2) * Cq * cT * S.T * Kb) * (S.sigma N * E') +
      Real.sqrt (2 * (S.T * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp)) *
        (S.qN N * (Real.sqrt 𝔈N + (N : ℝ) ^ (-(1 : ℝ) / d)))) +
      (2 * Real.sqrt (2 * S.T) * (d * Ca)) * a9tail d Λ₁ t k := by
  have hT := S.hT.le
  have hσ := a8p_sigma_nonneg S N
  have hqe := a8p_q_eq S N
  rw [a9bQ_tsum hCq hcT hCa hN hE' k, a9bG_tsum hCa k]
  have hcost := a1014_cost_le2 (S := S) (Λ₁ := Λ₁) (t := t) hCa hCq hCp hΛ hN h𝔈N hk hKb
  set tl := a9tail d Λ₁ t k with htl
  have htl0 : 0 ≤ tl := a9tail_nonneg Λ₁ t k
  have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa
  have hs2 : Real.sqrt (2 * S.T) ≥ 0 := Real.sqrt_nonneg _
  obtain ⟨hq0, hq1⟩ := a8p_q_bounds S hN
  have hcM : Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) ≤ Real.sqrt (2 * S.T) := by
    refine Real.sqrt_le_sqrt ?_
    rw [← hqe]
    nlinarith
  have hcG : Real.sqrt (2 * S.qN N * t) ≤ Real.sqrt (2 * S.T) := by
    refine Real.sqrt_le_sqrt ?_
    nlinarith [ht.1, ht.2]
  have hKtot0 : 0 ≤ ∑' j, a9K d Λ₁ t j := tsum_nonneg fun j => a9K_nonneg _ _ _
  have e1 : S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * E') * ∑' j, a9K d Λ₁ t j ≤
      ((1 / 2) * Cq * cT * S.T * Kb) * (S.sigma N * E') := by
    have h0 : 0 ≤ S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * E') := by positivity
    calc _ ≤ S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * E') * Kb :=
          mul_le_mul_of_nonneg_left hKb h0
      _ = _ := by ring
  have e2 : Real.sqrt (S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N))) * ((d : ℝ) * Ca) * tl +
      Real.sqrt (2 * S.qN N * t) * ((d : ℝ) * Ca) * tl ≤
      (2 * Real.sqrt (2 * S.T) * (d * Ca)) * tl := by
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcM hCd) htl0
    have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcG hCd) htl0
    linarith
  have e3 := Real.sqrt_le_sqrt hcost
  linarith [e1, e2, e3]

end Sum

section Perk

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ C₀' Cq Cp cT : ℝ}

/-- `W₁` for one finite set of modes: `≤ Ktr εf + c₁ σ 𝔈 + √(c₂ q (𝔈^{1/2} + N^{-1/d})) + c₃ tail`. -/
theorem a1014_perk1 (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
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
    wassersteinE 1
      (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
      (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
    ENNReal.ofReal (Ktr * εf N + (((1 / 2) * Cq * cT * S.T * Kb) * (S.sigma N * 𝔈 N) +
      Real.sqrt (2 * (S.T * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp)) *
        (S.qN N * (Real.sqrt (𝔈 N) + (N : ℝ) ^ (-(1 : ℝ) / d)))) +
      (2 * Real.sqrt (2 * S.T) * (d * Ca)) * a9tail d Λ₁ t k)) := by
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N (by omega)
  have hN1 : 1 ≤ N := by omega
  have hS' := a9_standing_mStar hS
  have hP' := hP
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP'
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hΛ1 := a8p_Lam_ge_one hS'
  have hεf := hfield.εf_nonneg N hN1
  have core := a1014_core_abs hP hS hN hF hfield ht hνG hk (p := 1) le_rfl one_le_two
  have hQ := a1014_Q1 hP hS hN hF ht hk
  have hI := a1014_I_diff1 hKtr0 hKtr hS hN1 ht hfield
  have hG := a9_gauss_tail hspec hCa hS' hN1 ht hk hνG
  have hG' : (∫⁻ y, ENNReal.ofReal (‖y - embedCLM (fun a => a9unit (gammaIdx d : ℝ) (k a))
      (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y)‖ ^ (1 : ℝ)) ∂νG) ^ (1 / (1 : ℝ)) ≤
      ENNReal.ofReal (∑' j, a9bG S N Ca Λ₁ t k j) := by
    have hGg : ∫⁻ y, ENNReal.ofReal ‖y - embedCLM (fun a => a9unit (gammaIdx d : ℝ) (k a))
        (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y)‖ ∂νG ≤
        ENNReal.ofReal (∑' j, a9bG S N Ca Λ₁ t k j) := hG
    simpa [Real.rpow_one] using hGg
  have hsum := a1014_sum_bound (S := S) (Λ := Λ) hCa hCq hCp0 hcT0 hΛ1 hN1 h𝔈 h𝔈 ht hk hKb
  have hQ0 : 0 ≤ ∑' j, a9bQ S N Ca Cq cT Λ₁ t (𝔈 N) k j :=
    tsum_nonneg fun j => a9bQ_nonneg hCa hCq hcT0 hN1 h𝔈 k j
  have hG0 : 0 ≤ ∑' j, a9bG S N Ca Λ₁ t k j := tsum_nonneg fun j => by
    unfold a9bG; split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  have hKe : 0 ≤ Ktr * εf N := mul_nonneg hKtr0 hεf
  refine core.trans (le_trans (add_le_add (add_le_add (add_le_add hQ le_rfl) hI) hG') ?_)
  rw [← ENNReal.ofReal_add hQ0 (Real.sqrt_nonneg _), ← ENNReal.ofReal_add
    (add_nonneg hQ0 (Real.sqrt_nonneg _)) hKe, ← ENNReal.ofReal_add
    (add_nonneg (add_nonneg hQ0 (Real.sqrt_nonneg _)) hKe) hG0]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [hsum]

/-- `W₂` for one finite set of modes (with `𝔈'`, `ε^{f,(2)}`). -/
theorem a1014_perk2 (hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT)
    {Ktr : ℝ} (hKtr0 : 0 ≤ Ktr)
    (hKtr : ∀ (D : DynData d) (ρ : ℝ → Torus d → ℝ),
      AdjointData S.s (gammaIdx d) Rg MB Λ VB D ν₀ S.T ρ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∀ F : NegSobolev d (gammaIdx d : ℝ), ‖transportField D ρ t (gammaIdx d : ℝ) F‖ ≤ ‖F‖ * Ktr)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {Cin : ℝ} {εf : ℕ → ℝ} {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)}
    {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin)
    {𝔈' : ℝ} (h𝔈' : 0 ≤ 𝔈')
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ω, ENNReal.ofReal
        ((correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (𝔈' ^ 2))
    {εf2 : ℝ} (hε2 : 0 ≤ εf2)
    (hL2 : ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
        (empirical ((R N).X₀ ω)) S.μ0 - ηF N ω‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (εf2 ^ 2))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG)
    {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k) {Kb : ℝ}
    (hKb : ∑' j, a9K d Λ₁ t j ≤ Kb) :
    wassersteinE 2
      (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
      (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
    ENNReal.ofReal (Ktr * εf2 + (((1 / 2) * Cq * cT * S.T * Kb) * (S.sigma N * 𝔈') +
      Real.sqrt (2 * (S.T * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp)) *
        (S.qN N * (Real.sqrt (𝔈 N) + (N : ℝ) ^ (-(1 : ℝ) / d)))) +
      (2 * Real.sqrt (2 * S.T) * (d * Ca)) * a9tail d Λ₁ t k)) := by
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N (by omega)
  have hN1 : 1 ≤ N := by omega
  have hS' := a9_standing_mStar hS
  have hP' := hP
  obtain ⟨hCa, hspec, hcom, hCq, hC, hCp0, hCp, hcT0, hcT⟩ := hP'
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hΛ1 := a8p_Lam_ge_one hS'
  have core := a1014_core_abs hP hS hN hF hfield ht hνG hk (p := 2) one_le_two le_rfl
  have hQ := a1014_Q2 hP hS hN hF h𝔈' hb ht hk
  have hI := a1014_I_diff2 hKtr0 hKtr hS hN1 ht hε2 hL2
  have hG := a1014_gauss_tail2 hspec hCa hS' hN1 ht hk hνG
  have hG' : (∫⁻ y, ENNReal.ofReal (‖y - embedCLM (fun a => a9unit (gammaIdx d : ℝ) (k a))
      (hmCoordCLM (fun a => a9unit (gammaIdx d : ℝ) (k a)) y)‖ ^ (2 : ℝ)) ∂νG) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (∑' j, a9bG S N Ca Λ₁ t k j) := hG
  have hsum := a1014_sum_bound (S := S) (Λ := Λ) hCa hCq hCp0 hcT0 hΛ1 hN1 h𝔈 h𝔈' ht hk hKb
  have hQ0 : 0 ≤ ∑' j, a9bQ S N Ca Cq cT Λ₁ t 𝔈' k j :=
    tsum_nonneg fun j => a9bQ_nonneg hCa hCq hcT0 hN1 h𝔈' k j
  have hG0 : 0 ≤ ∑' j, a9bG S N Ca Λ₁ t k j := tsum_nonneg fun j => by
    unfold a9bG; split_ifs
    · exact le_rfl
    · exact Real.sqrt_nonneg _
  have hKe : 0 ≤ Ktr * εf2 := mul_nonneg hKtr0 hε2
  refine core.trans (le_trans (add_le_add (add_le_add (add_le_add hQ le_rfl) hI) hG') ?_)
  rw [← ENNReal.ofReal_add hQ0 (Real.sqrt_nonneg _), ← ENNReal.ofReal_add
    (add_nonneg hQ0 (Real.sqrt_nonneg _)) hKe, ← ENNReal.ofReal_add
    (add_nonneg (add_nonneg hQ0 (Real.sqrt_nonneg _)) hKe) hG0]
  refine ENNReal.ofReal_le_ofReal ?_
  linarith [hsum]

end Perk

end HRS.Main.A1014
