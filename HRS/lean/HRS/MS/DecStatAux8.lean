import HRS.MS.DecStatAux7

/-!
# SA4, packet 8: the per-`N` bounds for an arbitrary finite index set, from the adjoint input for `wClass`
(copies of `sa2_smooth_iota`, `sa2_wass1_iota`, `sa2_wass2_iota`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas HRS.MS.MainRdStat
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

section Fam

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the sum of the `W^{m,p}` norms of a family of tests -/
def sa4X (m : ℕ) (p : ℝ) (φ : ι → Euc d → ℝ) : ℝ := ∑ a, (wClass (d := d) m p).norm (φ a)

theorem sa4X_nonneg (φ : ι → Euc d → ℝ) : 0 ≤ sa4X m p φ :=
  Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

theorem sa4_norm_nonneg_B {Kad : ℝ} {q : ℕ} (φ : Fin q → Euc d → ℝ) (a : Fin q) :
    0 ≤ max Kad 0 * (wClass (d := d) m p).norm (φ a) :=
  mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg

theorem sa4_family {C : WholeCoeff d} {Kad T : ℝ} (hm : mStar d ≤ m)
    (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) C T Kad) {q : ℕ}
    (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (φ : Fin q → Euc d → ℝ)
    (hφ : ∀ a, (wClass m p).mem (φ a)) :
    (∀ a, IsClassicalAdjointW C (ts a) (φ a) (fun r => propagatorW C r (ts a) (φ a))) ∧
    (∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb (mStar d) (propagatorW C rr (ts a) (φ a)) ∧
      cbNorm (mStar d) (propagatorW C rr (ts a) (φ a)) ≤ max Kad 0 * (wClass m p).norm (φ a)) := by
  have hφ2 : ∀ a, ContDiff ℝ 2 (φ a) := fun a =>
    (hφ a).1.of_le (by exact_mod_cast (by have := hm; unfold mStar at this; omega : 2 ≤ m))
  refine ⟨fun a => ?_, fun a rr hr => ?_⟩
  · exact sa2_isClassical_prop (hA 0 (ts a) le_rfl (hts a).1 (hts a).2 (φ a) (hφ2 a) (hφ a)).1
  · obtain ⟨-, -, -, hcb, hcbn⟩ := hA rr (ts a) hr.1 hr.2 (hts a).2 (φ a) (hφ2 a) (hφ a)
    refine ⟨hcb, hcbn.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg

/-- real and imaginary parts of admissible complex tests are admissible -/
theorem sa4_realIm_mem {n : ℕ} {φ : Fin (n + 1) → Euc d → ℂ}
    (h : ∀ a, (wClass (d := d) m p).memC (φ a)) (ab : Fin (n + 1) × Bool) :
    (wClass (d := d) m p).mem (realImPartsRd φ ab) := by
  obtain ⟨a, b⟩ := ab
  cases b
  · exact (h a).1
  · exact (h a).2

/-- the sum of the norms of the real and imaginary parts is dominated by twice the complex norms -/
theorem sa4_realIm_X {n : ℕ} (φ : Fin (n + 1) → Euc d → ℂ) :
    sa4X m p (realImPartsRd φ) ≤ 2 * ∑ a, (wClass (d := d) m p).normC (φ a) := by
  unfold sa4X
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Fintype.sum_bool]
  have hre : realImPartsRd φ (a, false) = fun x => (φ a x).re := by
    funext x; simp [realImPartsRd]
  have him : realImPartsRd φ (a, true) = fun x => (φ a x).im := by
    funext x; simp [realImPartsRd]
  rw [hre, him]
  unfold TestClassRd.normC
  set u := (wClass (d := d) m p).norm (fun x => (φ a x).re) with hu
  set v := (wClass (d := d) m p).norm (fun x => (φ a x).im) with hv
  have hu0 : 0 ≤ u := ENNReal.toReal_nonneg
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  have h1 : u ≤ Real.sqrt (u ^ 2 + v ^ 2) := by
    calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu0).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg v])
  have h2 : v ≤ Real.sqrt (u ^ 2 + v ^ 2) := by
    calc v = Real.sqrt (v ^ 2) := (Real.sqrt_sq hv0).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg u])
  linarith

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa4_smooth_iota (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {C₀c Ct Cy c0 Cs eN : ℝ}
    (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs) (heN : 0 ≤ eN) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ}
    (hTest : Sa4Test d S.s χ C₀c Ct) (hY : Sa4Y0 d χ Cy) {Kad : ℝ} (hm : mStar d ≤ m)
    (hremU : ∀ {q : ℕ} (ts' : Fin q → ℝ) (φ' : Fin q → Euc d → ℝ), (∀ a, ts' a ∈ Set.Icc (0 : ℝ) S.T) →
      (∀ a, (wClass m p).mem (φ' a)) →
      Sa4Rem S N C₀c Λ (Cs * eN) ts' φ' (fun a => c0 * (max Kad 0 * (wClass m p).norm (φ' a))))
    (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad)
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : ι → Euc d → ℝ) (hφ : ∀ a, (wClass m p).mem (φ a))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    smoothDist 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      (c0 * S.T * (1 + Cs) + Cy + Ct * S.T + 2 * d * S.T) *
        (max Kad 0 * sa4X m p φ + (max Kad 0 * sa4X m p φ) ^ 2) *
        rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) eN := by
  have hN1 : 1 ≤ N := by omega
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ts₂ : Fin (Fintype.card ι) → ℝ := fun j => ts (e.symm j) with hts₂
  set φ₂ : Fin (Fintype.card ι) → Euc d → ℝ := fun j => φ (e.symm j) with hφ₂
  have hts2 : ∀ j, ts₂ j ∈ Set.Icc (0 : ℝ) S.T := fun j => hts _
  have hφ2 : ∀ j, (wClass m p).mem (φ₂ j) := fun j => hφ _
  obtain ⟨hcl, hB⟩ := sa4_family hm hA ts₂ hts2 φ₂ hφ2
  have hB0 := fun j => sa4_norm_nonneg_B (m := m) (p := p) (Kad := Kad) φ₂ j
  have hφc : ∀ j, Continuous (φ₂ j) := fun j => (hφ2 j).1.continuous
  have hB2 : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts₂ a), MemCb 2 (propagatorW (S.coeff N) rr (ts₂ a) (φ₂ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts₂ a) (φ₂ a)) ≤ max Kad 0 * (wClass m p).norm (φ₂ a) := fun a rr h =>
    ⟨sa2_memCb_mono sa2_two_le_mStar (hB a rr h).1,
      (sa2_cbNorm_mono sa2_two_le_mStar _).trans (hB a rr h).2⟩
  obtain ⟨hmeas, hpsd⟩ := sa2_iota_basics hS hN1 ts₂ hts2 φ₂ hφc hB0 hB2
  have hη := hIF.η_meas N
  have hcore := sa4_smooth_rate hS hd hN hc0 hCs heN hC₀c hCt hCy hC₀ hTest hY hm₂ hmom ts₂ hts2 φ₂
    hφc hB0 hB (hremU ts₂ φ₂ hts2 hφ2) hcl hIF (fun j => hΨ _)
  rw [sa2_stat_law_reindex e _ _ _ _ ts φ hmeas, sa2_surr_law_reindex e _ _ _ _ ts φ _ hη hpsd]
  have hsum : ∑ j, max Kad 0 * (wClass m p).norm (φ₂ j) = max Kad 0 * sa4X m p φ := by
    rw [← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp e.symm (fun a => (wClass m p).norm (φ a))
  rw [hsum] at hcore
  haveI : IsProbabilityMeasure (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts₂ φ₂) :=
    inferInstanceAs (IsProbabilityMeasure ((R N).P.map _))
  haveI : IsProbabilityMeasure (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts₂ φ₂
      (R N).P (R N).η) := by
    unfold surrogateStatLawRd
    infer_instance
  exact (HRS.Main.A8P.a8p_smoothDist_relabel e _ _).trans hcore

theorem sa4_wass1_iota (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {C₀c Ct Cy c0 Cs eN : ℝ}
    (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs) (heN : 0 ≤ eN) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ}
    (hTest : Sa4Test d S.s χ C₀c Ct) (hY : Sa4Y0 d χ Cy) {Kad : ℝ} (hm : mStar d ≤ m)
    (hremU : ∀ {q : ℕ} (ts' : Fin q → ℝ) (φ' : Fin q → Euc d → ℝ), (∀ a, ts' a ∈ Set.Icc (0 : ℝ) S.T) →
      (∀ a, (wClass m p).mem (φ' a)) →
      Sa4Rem S N C₀c Λ (Cs * eN) ts' φ' (fun a => c0 * (max Kad 0 * (wClass m p).norm (φ' a))))
    (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad)
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {m₂ : ℝ} (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : ι → Euc d → ℝ) (hφ : ∀ a, (wClass m p).mem (φ a))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    wassersteinE 1 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      ENNReal.ofReal ((Cy + Real.sqrt (2 * Ct * S.T) + c0 * S.T * (1 + Cs)) *
        (max Kad 0 * sa4X m p φ) *
        rdRate (ε N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈 N) eN) := by
  have hN1 : 1 ≤ N := by omega
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ts₂ : Fin (Fintype.card ι) → ℝ := fun j => ts (e.symm j) with hts₂
  set φ₂ : Fin (Fintype.card ι) → Euc d → ℝ := fun j => φ (e.symm j) with hφ₂
  have hts2 : ∀ j, ts₂ j ∈ Set.Icc (0 : ℝ) S.T := fun j => hts _
  have hφ2 : ∀ j, (wClass m p).mem (φ₂ j) := fun j => hφ _
  obtain ⟨hcl, hB⟩ := sa4_family hm hA ts₂ hts2 φ₂ hφ2
  have hB0 := fun j => sa4_norm_nonneg_B (m := m) (p := p) (Kad := Kad) φ₂ j
  have hφc : ∀ j, Continuous (φ₂ j) := fun j => (hφ2 j).1.continuous
  have hB2 : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts₂ a), MemCb 2 (propagatorW (S.coeff N) rr (ts₂ a) (φ₂ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts₂ a) (φ₂ a)) ≤ max Kad 0 * (wClass m p).norm (φ₂ a) := fun a rr h =>
    ⟨sa2_memCb_mono sa2_two_le_mStar (hB a rr h).1,
      (sa2_cbNorm_mono sa2_two_le_mStar _).trans (hB a rr h).2⟩
  obtain ⟨hmeas, hpsd⟩ := sa2_iota_basics hS hN1 ts₂ hts2 φ₂ hφc hB0 hB2
  have hη := hIF.η_meas N
  have hcore := sa4_wass1_rate hS hd hN hc0 hCs heN hC₀c hCt hCy hC₀ hTest hY hm₂ hmom ts₂ hts2 φ₂
    hφc hB0 hB (hremU ts₂ φ₂ hts2 hφ2) hcl hIF (fun j => hΨ _)
  rw [sa2_stat_law_reindex e _ _ _ _ ts φ hmeas, sa2_surr_law_reindex e _ _ _ _ ts φ _ hη hpsd]
  have hsum : ∑ j, max Kad 0 * (wClass m p).norm (φ₂ j) = max Kad 0 * sa4X m p φ := by
    rw [← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp e.symm (fun a => (wClass m p).norm (φ a))
  rw [hsum] at hcore
  haveI : IsProbabilityMeasure (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts₂ φ₂) :=
    inferInstanceAs (IsProbabilityMeasure ((R N).P.map _))
  haveI : IsProbabilityMeasure (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts₂ φ₂
      (R N).P (R N).η) := by
    unfold surrogateStatLawRd
    infer_instance
  exact (HRS.Main.A8P.a8p_wass_relabel e 1 le_rfl _ _).trans hcore

theorem sa4_wass2_iota (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N) {C₀c Ct Cy c0 Cs eN : ℝ}
    (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs) (heN : 0 ≤ eN) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ}
    (hTest : Sa4Test d S.s χ C₀c Ct) (hY : Sa4Y0 d χ Cy) {Kad : ℝ} (hm : mStar d ≤ m)
    (hremU : ∀ {q : ℕ} (ts' : Fin q → ℝ) (φ' : Fin q → Euc d → ℝ), (∀ a, ts' a ∈ Set.Icc (0 : ℝ) S.T) →
      (∀ a, (wClass m p).mem (φ' a)) →
      Sa4Rem S N C₀c Λ (Cs * eN) ts' φ' (fun a => c0 * (max Kad 0 * (wClass m p).norm (φ' a))))
    (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad)
    {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ} {m₂ : ℝ}
    (hm₂ : 0 ≤ m₂)
    (hmom : PropagatedSecondMoment S R m₂) (ts : ι → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : ι → Euc d → ℝ) (hφ : ∀ a, (wClass m p).mem (φ a))
    (hIF : InitialFluctuationRd S R χ m₀ Cin ε Ψ) (hE2 : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2)
    (hΨ : ∀ a, propagatorW (S.coeff N) 0 (ts a) (φ a) ∈ Submodule.span ℝ (Ψ N)) :
    wassersteinE 2 (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts φ (R N).P (R N).η) ≤
      ENNReal.ofReal ((Cy + Real.sqrt (2 * Ct * S.T) + c0 * S.T * (1 + Cs)) *
        (max Kad 0 * sa4X m p φ) *
        rdRate (ε2 N) (S.qN N) (S.sigma N) (wN d N (𝔈 N) m₂) (𝔈' N) eN) := by
  have hN1 : 1 ≤ N := by omega
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι with he
  set ts₂ : Fin (Fintype.card ι) → ℝ := fun j => ts (e.symm j) with hts₂
  set φ₂ : Fin (Fintype.card ι) → Euc d → ℝ := fun j => φ (e.symm j) with hφ₂
  have hts2 : ∀ j, ts₂ j ∈ Set.Icc (0 : ℝ) S.T := fun j => hts _
  have hφ2 : ∀ j, (wClass m p).mem (φ₂ j) := fun j => hφ _
  obtain ⟨hcl, hB⟩ := sa4_family hm hA ts₂ hts2 φ₂ hφ2
  have hB0 := fun j => sa4_norm_nonneg_B (m := m) (p := p) (Kad := Kad) φ₂ j
  have hφc : ∀ j, Continuous (φ₂ j) := fun j => (hφ2 j).1.continuous
  have hB2 : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts₂ a), MemCb 2 (propagatorW (S.coeff N) rr (ts₂ a) (φ₂ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts₂ a) (φ₂ a)) ≤ max Kad 0 * (wClass m p).norm (φ₂ a) := fun a rr h =>
    ⟨sa2_memCb_mono sa2_two_le_mStar (hB a rr h).1,
      (sa2_cbNorm_mono sa2_two_le_mStar _).trans (hB a rr h).2⟩
  obtain ⟨hmeas, hpsd⟩ := sa2_iota_basics hS hN1 ts₂ hts2 φ₂ hφc hB0 hB2
  have hη := hIF.η_meas N
  have hcore := sa4_wass2_rate hS hd hN hc0 hCs heN hC₀c hCt hCy hC₀ hTest hY hm₂ hmom ts₂ hts2 φ₂
    hφc hB0 hB (hremU ts₂ φ₂ hts2 hφ2) hcl hIF hE2 (fun j => hΨ _)
  rw [sa2_stat_law_reindex e _ _ _ _ ts φ hmeas, sa2_surr_law_reindex e _ _ _ _ ts φ _ hη hpsd]
  have hsum : ∑ j, max Kad 0 * (wClass m p).norm (φ₂ j) = max Kad 0 * sa4X m p φ := by
    rw [← Finset.mul_sum]
    congr 1
    exact Equiv.sum_comp e.symm (fun a => (wClass m p).norm (φ a))
  rw [hsum] at hcore
  haveI : IsProbabilityMeasure (fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts₂ φ₂) :=
    inferInstanceAs (IsProbabilityMeasure ((R N).P.map _))
  haveI : IsProbabilityMeasure (surrogateStatLawRd (S.coeff N) (S.AN N) (S.qN N) ts₂ φ₂
      (R N).P (R N).η) := by
    unfold surrogateStatLawRd
    infer_instance
  exact (HRS.Main.A8P.a8p_wass_relabel e 2 (by norm_num) _ _).trans hcore

end Fam

end HRS.MS.DecStat
