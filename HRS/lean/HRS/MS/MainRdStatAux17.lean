import HRS.MS.MainRdStatAux16

/-!
# SA2, packet 8d: the per-`N` `W₁` and `W₂` bounds with the rate `rdRate`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

section WassRate2

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa2_wass1_rate (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cq Ct Cy : ℝ}
    (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ} (hTest : Sa2Test d S.s χ C₀c Ct)
    (hY : Sa2Y0 d χ Cy) {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) (hφc : ∀ a, Continuous (φ a))
    {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hU : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a),
      ulocNormE (mStar d) χ (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ ENNReal.ofReal (B a))
    (hcl : ∀ a, IsClassicalAdjointW (S.coeff N) (ts a) (φ a)
      (fun r => propagatorW (S.coeff N) r (ts a) (φ a)))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    wassersteinE 1 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      ENNReal.ofReal ((Cy + Real.sqrt (2 * Ct * S.T) + 1 / 2 * (Cq * ((d : ℝ) * d * MB)) * S.T) *
        (∑ a, B a) * rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) 0) := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have hr3 : 3 ≤ mStar d + 3 := Nat.le_add_left _ _
  have h𝔈 : 0 < 𝔈 N := hS.energy.pos N hN1
  have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hinj := HRS.MS.PathFidi.sa26_flow_inj_all hT0 (hS.flow N hN1) hF
  have hU2 : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a),
      ulocNormE 2 χ (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ ENNReal.ofReal (B a) := fun a rr h =>
    (sa2_ulocNormE_mono sa2_two_le_mStar χ _).trans (hU a rr h)
  have hcovH := sa2_covH hS hd hN hF.progressive hTest hCt hC₀c hC₀ ts hts φ hB0 hB hU2 hinj hm₂ hmom
  have hη : ∀ ψ : Euc d → ℝ, Measurable fun ζ => (R N).η ζ ψ := hIF.η_meas N
  set c0 : ℝ := 1 / 2 * (Cq * ((d : ℝ) * d * MB)) with hc0def
  have hMB := sa2_cMB_nonneg (d := d) (MB := MB) (M := S.M) hS.matrix_bound
  have hc0 : 0 ≤ c0 := by rw [hc0def]; positivity
  have hdiff : ∀ a, ∫⁻ ζ, ENNReal.ofReal |(sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a| ∂(R N).P ≤
      ENNReal.ofReal (ε N * (Cy * B a)) := by
    intro a
    obtain ⟨hY0c, hYn⟩ := hY m₀ hIF.m₀_le _ (B a) (hB0 a) (hB a 0 ⟨le_rfl, (hts a).1⟩).1
      (hB a 0 ⟨le_rfl, (hts a).1⟩).2 (hU a 0 ⟨le_rfl, (hts a).1⟩)
    exact sa2_I1_diff hS hN1 hIF ts φ a (hΨ a) hYn hY0c
  have hcore := sa2_wass_core hS hN1 ts hts φ hφc hB0 hB hcl hη hcovH (p := 1) le_rfl (by norm_num)
  have e1 : ∀ X : ℝ≥0∞, X ^ (1 / (1 : ℝ)) = X := fun X => by simp
  simp only [e1, Real.rpow_one] at hcore
  have hT1 : ∫⁻ ζ, ENNReal.ofReal ‖sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ‖ ∂(R N).P ≤
      ENNReal.ofReal (∑ a, ε N * (Cy * B a)) := by
    have := HRS.Main.A8P.a8p_vec_L1 (P := (R N).P)
      (fun ζ => sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ)
      (fun a => sa2_diffcoord_meas hS hN1 ts hts φ hB hη a)
      (c := fun a => ε N * (Cy * B a)) (fun a => by have := hB0 a; positivity) hdiff
    simpa only [Real.rpow_one] using this
  have hT3 := sa2_rem_L1 hS hr3 hd hN hF.progressive hLm hcomm hCq hC₀c hC₀ ts hts φ hB hinj
  set cR : ℝ := ∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) with hcR
  have hcR0 : 0 ≤ cR := by
    refine Finset.sum_nonneg fun a _ => ?_
    have := sa2_sigma_nonneg S N
    have := hB0 a
    positivity
  have hcRe : cR = S.sigma N * c0 * ∑ a, B a := by
    rw [hcR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hc0def]; ring
  have hsumε : ∑ a, ε N * (Cy * B a) = ε N * (Cy * ∑ a, B a) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  have hz : ∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ∂(R N).P ≤ ENNReal.ofReal (cR * (𝔈 N * S.T)) := by
    rw [ENNReal.ofReal_mul hcR0, ENNReal.ofReal_mul h𝔈.le]
    exact hT3
  have hBs : 0 ≤ ∑ a, B a := Finset.sum_nonneg fun a _ => hB0 a
  have hq := sa2_q_nonneg S N
  have hw := sa2_wN_nonneg (d := d) (N := N) h𝔈.le hm₂
  have hσ := sa2_sigma_nonneg S N
  refine hcore.trans ((add_le_add (add_le_add hT1 le_rfl) hz).trans ?_)
  refine HRS.Main.A8P.a8p_sum_ofReal (Finset.sum_nonneg fun a _ => by have := hB0 a; positivity)
    (Real.sqrt_nonneg _) (mul_nonneg hcR0 (mul_nonneg h𝔈.le hT0)) ?_
  rw [hsumε, hcRe]
  have key := sa2_arith_wass (Bs := ∑ a, B a) (c0 := c0) (Cy := Cy) (Ct := Ct) (T := S.T) (ε := ε N)
    (q := S.qN N) (σ := S.sigma N) (E := 𝔈 N) (w := wN d N (𝔈 N) m₂) hBs hc0 hCy hCt hT0 hε hq hσ
    h𝔈.le hw
  unfold rdRate
  exact key

theorem sa2_wass2_rate (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cq Ct Cy : ℝ}
    (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ} (hTest : Sa2Test d S.s χ C₀c Ct)
    (hY : Sa2Y0 d χ Cy) {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ}
    {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) (hφc : ∀ a, Continuous (φ a))
    {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hU : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a),
      ulocNormE (mStar d) χ (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ ENNReal.ofReal (B a))
    (hcl : ∀ a, IsClassicalAdjointW (S.coeff N) (ts a) (φ a)
      (fun r => propagatorW (S.coeff N) r (ts a) (φ a)))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ) (hE2 : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    wassersteinE 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      ENNReal.ofReal ((Cy + Real.sqrt (2 * Ct * S.T) + 1 / 2 * (Cq * ((d : ℝ) * d * MB)) * S.T) *
        (∑ a, B a) * rdRate (ε2 N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈' N) 0) := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have hr3 : 3 ≤ mStar d + 3 := Nat.le_add_left _ _
  have h𝔈 : 0 < 𝔈 N := hS.energy.pos N hN1
  have hε : 0 ≤ ε2 N := hE2.ε2_nonneg N hN1
  have h𝔈' : 0 ≤ 𝔈' N := hE2.𝔈'_nonneg N hN1
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hinj := HRS.MS.PathFidi.sa26_flow_inj_all hT0 (hS.flow N hN1) hF
  have hU2 : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a),
      ulocNormE 2 χ (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ ENNReal.ofReal (B a) := fun a rr h =>
    (sa2_ulocNormE_mono sa2_two_le_mStar χ _).trans (hU a rr h)
  have hcovH := sa2_covH hS hd hN hF.progressive hTest hCt hC₀c hC₀ ts hts φ hB0 hB hU2 hinj hm₂ hmom
  have hη : ∀ ψ : Euc d → ℝ, Measurable fun ζ => (R N).η ζ ψ := hIF.η_meas N
  set c0 : ℝ := 1 / 2 * (Cq * ((d : ℝ) * d * MB)) with hc0def
  have hMB := sa2_cMB_nonneg (d := d) (MB := MB) (M := S.M) hS.matrix_bound
  have hc0 : 0 ≤ c0 := by rw [hc0def]; positivity
  have hdiff : ∀ a, ∫⁻ ζ, ENNReal.ofReal (((sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ) a) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal ((ε2 N * (Cy * B a)) ^ 2) := by
    intro a
    obtain ⟨hY0c, hYn⟩ := hY m₀ hIF.m₀_le _ (B a) (hB0 a) (hB a 0 ⟨le_rfl, (hts a).1⟩).1
      (hB a 0 ⟨le_rfl, (hts a).1⟩).2 (hU a 0 ⟨le_rfl, (hts a).1⟩)
    exact sa2_I1L2_diff hS hN1 hE2 ts φ a (hΨ a) hYn hY0c
  have hcore := sa2_wass_core hS hN1 ts hts φ hφc hB0 hB hcl hη hcovH (p := 2) (by norm_num) le_rfl
  have hconv : ∫⁻ ζ, ENNReal.ofReal (‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ)) ∂(R N).P =
      ∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ) ∂(R N).P :=
    lintegral_congr fun ζ => (ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hconv] at hcore
  have hT1 : (∫⁻ ζ, ENNReal.ofReal (‖sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ‖ ^ (2 : ℝ)) ∂(R N).P) ^
      (1 / 2 : ℝ) ≤ ENNReal.ofReal (∑ a, ε2 N * (Cy * B a)) :=
    HRS.Main.A8P.a8p_vec_L2 (P := (R N).P) (fun ζ => sa2Iemp S R N ts φ ζ - sa2Itil S R N ts φ ζ)
      (fun a => sa2_diffcoord_meas hS hN1 ts hts φ hB hη a)
      (c := fun a => ε2 N * (Cy * B a)) (fun a => by have := hB0 a; positivity) hdiff
  have hT3 := sa2_rem_L2 hS hr3 hd hN hF.progressive hLm hcomm hCq hC₀c hC₀ ts hts φ hB hinj hE2
  set cR : ℝ := ∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) with hcR
  have hcR0 : 0 ≤ cR := by
    refine Finset.sum_nonneg fun a _ => ?_
    have := sa2_sigma_nonneg S N
    have := hB0 a
    positivity
  have hcRe : cR = S.sigma N * c0 * ∑ a, B a := by
    rw [hcR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hc0def]; ring
  have hsumε : ∑ a, ε2 N * (Cy * B a) = ε2 N * (Cy * ∑ a, B a) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  have hz : (∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (cR * (𝔈' N * S.T)) := by
    rw [ENNReal.ofReal_mul hcR0, ENNReal.ofReal_mul h𝔈']
    exact hT3
  have hBs : 0 ≤ ∑ a, B a := Finset.sum_nonneg fun a _ => hB0 a
  have hq := sa2_q_nonneg S N
  have hw := sa2_wN_nonneg (d := d) (N := N) h𝔈.le hm₂
  have hσ := sa2_sigma_nonneg S N
  refine hcore.trans ((add_le_add (add_le_add hT1 le_rfl) hz).trans ?_)
  refine HRS.Main.A8P.a8p_sum_ofReal (Finset.sum_nonneg fun a _ => by have := hB0 a; positivity)
    (Real.sqrt_nonneg _) (mul_nonneg hcR0 (mul_nonneg h𝔈' hT0)) ?_
  rw [hsumε, hcRe]
  have key := sa2_arith_wass (Bs := ∑ a, B a) (c0 := c0) (Cy := Cy) (Ct := Ct) (T := S.T) (ε := ε2 N)
    (q := S.qN N) (σ := S.sigma N) (E := 𝔈' N) (w := wN d N (𝔈 N) m₂) hBs hc0 hCy hCt hT0 hε hq hσ
    h𝔈' hw
  unfold rdRate
  exact key

end WassRate2

end HRS.MS.MainRdStat
