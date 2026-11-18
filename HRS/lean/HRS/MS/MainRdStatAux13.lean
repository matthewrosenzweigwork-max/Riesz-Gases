import HRS.MS.MainRdStatAux12

/-!
# SA2, packet 7c: the per-`N` smooth-metric bound with the rate `rdRate`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

section SmoothRate

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

/-- The shape of the `Y₀`-norm control of the transported tests. -/
def Sa2Y0 (d : ℕ) (χ : Euc d → ℝ) (Cy : ℝ) : Prop :=
  ∀ m₀ : ℕ, m₀ ≤ mStar d → ∀ (ψ : Euc d → ℝ) (X : ℝ), 0 ≤ X →
    MemCb 2 ψ → cbNorm 2 ψ ≤ X → ulocNormE (mStar d) χ ψ ≤ ENNReal.ofReal X →
    Y0Class m₀ χ ψ ∧ y0Norm m₀ χ ψ ≤ Cy * X

theorem sa2_smooth_rate (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
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
    smoothDist 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      (1 / 2 * (Cq * ((d : ℝ) * d * MB)) * S.T + Cy + Ct * S.T + 2 * d * S.T) *
        ((∑ a, B a) + (∑ a, B a) ^ 2) *
        rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) 0 := by
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  have h𝔈 : 0 < 𝔈 N := hS.energy.pos N hN1
  have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hinj := HRS.MS.PathFidi.sa26_flow_inj_all hT0 (hS.flow N hN1) hF
  have hU2 : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a),
      ulocNormE 2 χ (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ ENNReal.ofReal (B a) := fun a rr h =>
    (sa2_ulocNormE_mono sa2_two_le_mStar χ _).trans (hU a rr h)
  have hcost := sa2_cov_cost hS hd hN hF.progressive hTest hCt hC₀c hC₀ ts hts φ hB0 hB hU2 hinj hm₂ hmom
  have htriv := sa2_cov_triv hS hN1 ts φ hB0 hB
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
  have hcore := sa2_smooth_core hS hd hN hLm hcomm hCq hC₀c hC₀ ts hts φ hφc hB0 hB hcl
    (Ccov := covDiscrepancyMatrix (R N).P S.T (sa2Sg S R N ts φ)
      (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N))) le_rfl hη
    (eI := fun a => ε N * (Cy * B a)) (fun a => by have := hB0 a; positivity) hdiff
  have hcR : ∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) =
      S.sigma N * c0 * ∑ a, B a := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hc0def]; ring
  have hsumε : ∑ a, ε N * (Cy * B a) = ε N * (Cy * ∑ a, B a) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  rw [hcR, hsumε] at hcore
  refine hcore.trans ?_
  have hq1 : S.qN N ≤ 1 := (Q54c.qScale_bounds hN0 (S.hκ N) (S.hinvβ N)).2
  have key := sa2_arith_smooth (Bs := ∑ a, B a) (c0 := c0) (Cy := Cy) (Ct := Ct) (dd := (d : ℝ))
    (T := S.T) (ε := ε N) (q := S.qN N) (σ := S.sigma N) (E := 𝔈 N) (w := wN d N (𝔈 N) m₂)
    (Ccov := covDiscrepancyMatrix (R N).P S.T (sa2Sg S R N ts φ)
      (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N)))
    (Finset.sum_nonneg fun a _ => hB0 a) hc0 hCy hCt (Nat.cast_nonneg d) hT0 hε (sa2_q_nonneg S N) hq1
    (sa2_sigma_nonneg S N) h𝔈.le (sa2_wN_nonneg h𝔈.le hm₂) (fun _ => hcost) (fun _ => htriv)
  unfold rdRate
  exact key

end SmoothRate

end HRS.MS.MainRdStat
