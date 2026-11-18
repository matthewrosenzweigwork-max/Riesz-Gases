import HRS.MS.MainRdStatAux18

/-!
# SA2, packet 9b: the per-`N` bounds for an arbitrary finite index set, from the adjoint input
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- the sum of the uniformly local norms of a family of tests -/
def sa2X (χ : Euc d → ℝ) (φ : ι → Euc d → ℝ) : ℝ := ∑ a, (ulocNormE (mStar d) χ (φ a)).toReal

theorem sa2X_nonneg (χ : Euc d → ℝ) (φ : ι → Euc d → ℝ) : 0 ≤ sa2X χ φ :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

section Fam

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa2_smooth_iota (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cq Ct Cy : ℝ}
    (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ)
    (hTest : Sa2Test d S.s χ C₀c Ct) (hY : Sa2Y0 d χ Cy) {Kad : ℝ}
    (hA : AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 (S.coeff N) S.T Kad)
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : ι → Euc d → ℝ) (hφ : ∀ a, (ulocClass (mStar d) χ).mem (φ a))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    smoothDist 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      (1 / 2 * (Cq * ((d : ℝ) * d * MB)) * S.T + Cy + Ct * S.T + 2 * d * S.T) *
        (max Kad 0 * sa2X χ φ + (max Kad 0 * sa2X χ φ) ^ 2) *
        rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) 0 := by
  have hN1 : 1 ≤ N := by omega
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ts₂ : Fin (Fintype.card ι) → ℝ := fun j => ts (e.symm j) with hts₂
  set φ₂ : Fin (Fintype.card ι) → Euc d → ℝ := fun j => φ (e.symm j) with hφ₂
  have hts2 : ∀ j, ts₂ j ∈ Set.Icc (0 : ℝ) S.T := fun j => hts _
  have hφ2 : ∀ j, (ulocClass (mStar d) χ).mem (φ₂ j) := fun j => hφ _
  obtain ⟨hcl, hB, hU⟩ := sa2_family hχ hA ts₂ hts2 φ₂ hφ2
  have hB0 := fun j => sa2_norm_nonneg_B (Kad := Kad) (χ := χ) φ₂ j
  obtain ⟨hmeas, hpsd⟩ := sa2_iota_basics hS hN1 ts₂ hts2 φ₂ (fun j => (hφ _).1) hB0 hB
  have hη := hIF.η_meas N
  have hcore := sa2_smooth_rate hS hd hN hLm hcomm hCq hC₀c hCt hCy hC₀ hTest hY hm₂ hmom ts₂ hts2 φ₂
    (fun j => (hφ _).1) hB0 hB hU hcl hIF (fun j => hΨ _)
  rw [sa2_stat_law_reindex e _ _ _ _ ts φ hmeas, sa2_surr_law_reindex e _ _ _ _ ts φ _ hη hpsd]
  have hsum : ∑ j, max Kad 0 * (ulocNormE (mStar d) χ (φ₂ j)).toReal = max Kad 0 * sa2X χ φ := by
    rw [← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp e.symm (fun a => (ulocNormE (mStar d) χ (φ a)).toReal)
  rw [hsum] at hcore
  haveI : IsProbabilityMeasure (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts₂ φ₂) :=
    inferInstanceAs (IsProbabilityMeasure ((R N).P.map _))
  haveI : IsProbabilityMeasure (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts₂ φ₂
      (R N).P (R N).η) := by
    unfold surrogateStatLawRd
    infer_instance
  exact (HRS.Main.A8P.a8p_smoothDist_relabel e _ _).trans hcore

theorem sa2_wass1_iota (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cq Ct Cy : ℝ}
    (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ)
    (hTest : Sa2Test d S.s χ C₀c Ct) (hY : Sa2Y0 d χ Cy) {Kad : ℝ}
    (hA : AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 (S.coeff N) S.T Kad)
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : ι → Euc d → ℝ) (hφ : ∀ a, (ulocClass (mStar d) χ).mem (φ a))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    wassersteinE 1 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      ENNReal.ofReal ((Cy + Real.sqrt (2 * Ct * S.T) + 1 / 2 * (Cq * ((d : ℝ) * d * MB)) * S.T) *
        (max Kad 0 * sa2X χ φ) *
        rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) 0) := by
  have hN1 : 1 ≤ N := by omega
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ts₂ : Fin (Fintype.card ι) → ℝ := fun j => ts (e.symm j) with hts₂
  set φ₂ : Fin (Fintype.card ι) → Euc d → ℝ := fun j => φ (e.symm j) with hφ₂
  have hts2 : ∀ j, ts₂ j ∈ Set.Icc (0 : ℝ) S.T := fun j => hts _
  have hφ2 : ∀ j, (ulocClass (mStar d) χ).mem (φ₂ j) := fun j => hφ _
  obtain ⟨hcl, hB, hU⟩ := sa2_family hχ hA ts₂ hts2 φ₂ hφ2
  have hB0 := fun j => sa2_norm_nonneg_B (Kad := Kad) (χ := χ) φ₂ j
  obtain ⟨hmeas, hpsd⟩ := sa2_iota_basics hS hN1 ts₂ hts2 φ₂ (fun j => (hφ _).1) hB0 hB
  have hη := hIF.η_meas N
  have hcore := sa2_wass1_rate hS hd hN hLm hcomm hCq hC₀c hCt hCy hC₀ hTest hY hm₂ hmom ts₂ hts2 φ₂
    (fun j => (hφ _).1) hB0 hB hU hcl hIF (fun j => hΨ _)
  rw [sa2_stat_law_reindex e _ _ _ _ ts φ hmeas, sa2_surr_law_reindex e _ _ _ _ ts φ _ hη hpsd]
  have hsum : ∑ j, max Kad 0 * (ulocNormE (mStar d) χ (φ₂ j)).toReal = max Kad 0 * sa2X χ φ := by
    rw [← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp e.symm (fun a => (ulocNormE (mStar d) χ (φ a)).toReal)
  rw [hsum] at hcore
  haveI : IsProbabilityMeasure (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts₂ φ₂) :=
    inferInstanceAs (IsProbabilityMeasure ((R N).P.map _))
  haveI : IsProbabilityMeasure (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts₂ φ₂
      (R N).P (R N).η) := by
    unfold surrogateStatLawRd
    infer_instance
  exact (HRS.Main.A8P.a8p_wass_relabel e 1 le_rfl _ _).trans hcore

theorem sa2_wass2_iota (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cq Ct Cy : ℝ}
    (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ)
    (hTest : Sa2Test d S.s χ C₀c Ct) (hY : Sa2Y0 d χ Cy) {Kad : ℝ}
    (hA : AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 (S.coeff N) S.T Kad)
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ} {m₂ : ℝ}
    (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : ι → Euc d → ℝ) (hφ : ∀ a, (ulocClass (mStar d) χ).mem (φ a))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ) (hE2 : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    wassersteinE 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      ENNReal.ofReal ((Cy + Real.sqrt (2 * Ct * S.T) + 1 / 2 * (Cq * ((d : ℝ) * d * MB)) * S.T) *
        (max Kad 0 * sa2X χ φ) *
        rdRate (ε2 N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈' N) 0) := by
  have hN1 : 1 ≤ N := by omega
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ts₂ : Fin (Fintype.card ι) → ℝ := fun j => ts (e.symm j) with hts₂
  set φ₂ : Fin (Fintype.card ι) → Euc d → ℝ := fun j => φ (e.symm j) with hφ₂
  have hts2 : ∀ j, ts₂ j ∈ Set.Icc (0 : ℝ) S.T := fun j => hts _
  have hφ2 : ∀ j, (ulocClass (mStar d) χ).mem (φ₂ j) := fun j => hφ _
  obtain ⟨hcl, hB, hU⟩ := sa2_family hχ hA ts₂ hts2 φ₂ hφ2
  have hB0 := fun j => sa2_norm_nonneg_B (Kad := Kad) (χ := χ) φ₂ j
  obtain ⟨hmeas, hpsd⟩ := sa2_iota_basics hS hN1 ts₂ hts2 φ₂ (fun j => (hφ _).1) hB0 hB
  have hη := hIF.η_meas N
  have hcore := sa2_wass2_rate hS hd hN hLm hcomm hCq hC₀c hCt hCy hC₀ hTest hY hm₂ hmom ts₂ hts2 φ₂
    (fun j => (hφ _).1) hB0 hB hU hcl hIF hE2 (fun j => hΨ _)
  rw [sa2_stat_law_reindex e _ _ _ _ ts φ hmeas, sa2_surr_law_reindex e _ _ _ _ ts φ _ hη hpsd]
  have hsum : ∑ j, max Kad 0 * (ulocNormE (mStar d) χ (φ₂ j)).toReal = max Kad 0 * sa2X χ φ := by
    rw [← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp e.symm (fun a => (ulocNormE (mStar d) χ (φ a)).toReal)
  rw [hsum] at hcore
  haveI : IsProbabilityMeasure (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts₂ φ₂) :=
    inferInstanceAs (IsProbabilityMeasure ((R N).P.map _))
  haveI : IsProbabilityMeasure (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts₂ φ₂
      (R N).P (R N).η) := by
    unfold surrogateStatLawRd
    infer_instance
  exact (HRS.Main.A8P.a8p_wass_relabel e 2 (by norm_num) _ _).trans hcore

end Fam

end HRS.MS.MainRdStat
