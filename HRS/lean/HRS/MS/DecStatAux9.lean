import HRS.MS.DecStatAux8

/-!
# SA4, packet 9: the conclusions (a)-(d) of `RdStatParts` for the test class `wClass m p` (copy of `sa2_parts`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas HRS.MS.MainRdStat
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ}

theorem sa4_rate_nonneg {ε q σ w E e : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q) (hw : 0 ≤ w) (hσ : 0 ≤ σ) (hE : 0 ≤ E)
    (he : 0 ≤ e) : 0 ≤ rdRate ε q σ w E e := by
  unfold rdRate
  have := Real.sqrt_nonneg q
  have := Real.sqrt_nonneg w
  positivity

section Parts

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa4_parts {m : ℕ} {p : ℝ} [Fact (2 ≤ p)] (hm : mStar d ≤ m) (hd : 1 ≤ d)
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    {C₀c Ct Cy c0 Cs Kad : ℝ} {χ : Euc d → ℝ} {e : ℕ → ℝ} (he : ∀ N, 0 ≤ e N)
    (hc0 : 0 ≤ c0) (hCs : 0 ≤ Cs) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) (hTest : Sa4Test d S.s χ C₀c Ct) (hY : Sa4Y0 d χ Cy)
    (hremU : ∀ N : ℕ, 2 ≤ N → ∀ {q : ℕ} (ts' : Fin q → ℝ) (φ' : Fin q → Euc d → ℝ),
      (∀ a, ts' a ∈ Set.Icc (0 : ℝ) S.T) → (∀ a, (wClass m p).mem (φ' a)) →
      Sa4Rem S N C₀c Λ (Cs * e N) ts' φ' (fun a => c0 * (max Kad 0 * (wClass m p).norm (φ' a))))
    (hAdj : ∀ N : ℕ, 1 ≤ N →
      AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad)
    {m₂ : ℝ} (hm₂ : 0 ≤ m₂) (hmom : PropagatedSecondMoment S R m₂) {T : ℝ} (hST : S.T = T) {Cin : ℝ} :
    RdStatParts S R
      (max 2 (2 + ((c0 * T * (1 + Cs) + Cy + Ct * T + 2 * d * T) +
        (Cy + Real.sqrt (2 * Ct * T) + c0 * T * (1 + Cs))) *
          (2 * max Kad 0 + (2 * max Kad 0) ^ 2))) 1 (wClass m p) χ Cin C₀ Λ 𝔈 m₂ e := by
  set Kp : ℝ := max Kad 0 with hKp
  set κ : ℝ := 2 * Kp with hκ
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  have hT0 : 0 ≤ T := by rw [← hST]; exact S.hT.le
  set K1 : ℝ := c0 * T * (1 + Cs) + Cy + Ct * T + 2 * d * T with hK1def
  set K2 : ℝ := Cy + Real.sqrt (2 * Ct * T) + c0 * T * (1 + Cs) with hK2def
  have hK1 : 0 ≤ K1 := by rw [hK1def]; positivity
  have hK2 : 0 ≤ K2 := by rw [hK2def]; positivity
  have hM0 : 0 ≤ κ + κ ^ 2 := by positivity
  set C : ℝ := max 2 (2 + (K1 + K2) * (κ + κ ^ 2)) with hCdef
  have hC2 : 2 ≤ C := le_max_left _ _
  have hCK1 : K1 * (κ + κ ^ 2) ≤ C :=
    le_trans (by nlinarith [mul_nonneg hK2 hM0]) (le_max_right _ _)
  have hCK2 : K2 * (κ + κ ^ 2) ≤ C :=
    le_trans (by nlinarith [mul_nonneg hK1 hM0]) (le_max_right _ _)
  have hN2 : ∀ N : ℕ, C ≤ (N : ℝ) → 2 ≤ N := fun N hN => by
    have : (2 : ℝ) ≤ N := hC2.trans hN
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a)
    intro m₀ ε t φ ht hφ hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have key := sa4_wass1_iota hS hd hN2' hc0 hCs (he N) hC₀c hCt hCy hC₀ hTest hY hm (hremU N hN2') (hAdj N hN1) hm₂ hmom
      (fun _ : Fin 1 => t) (fun _ => ht) (fun _ : Fin 1 => φ) (fun _ => hφ) hIF
      (fun a => Submodule.subset_span ⟨a, rfl⟩)
    rw [hST] at key
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have hr := sa4_rate_nonneg hε (sa2_q_nonneg S N) (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂)
      (sa2_sigma_nonneg S N) (hS.energy.pos N hN1).le (he N)
    have hX : sa4X m p (fun _ : Fin 1 => φ) = (wClass m p).norm φ := by simp [sa4X]
    have hX0 : 0 ≤ (wClass m p).norm φ := ENNReal.toReal_nonneg
    refine sa2_stat_arith hK2 hM0 hX0 hr ht.1 ?_ hCK2
    have hBs : Kp * sa4X m p (fun _ : Fin 1 => φ) ≤ κ * (wClass m p).norm φ := by
      rw [hX]
      exact mul_le_mul_of_nonneg_right (by rw [hκ]; linarith) ENNReal.toReal_nonneg
    have := sa2_Bs_final (mul_nonneg hKp0 (sa4X_nonneg _)) hBs hκ0 hX0
    nlinarith [sq_nonneg (Kp * sa4X m p (fun _ : Fin 1 => φ))]
  · -- (b)
    intro m₀ ε t pp φ hp ht hφ hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have key := sa4_smooth_iota hS hd hN2' hc0 hCs (he N) hC₀c hCt hCy hC₀ hTest hY hm (hremU N hN2') (hAdj N hN1) hm₂ hmom
      (fun _ : Fin pp => t) (fun _ => ht) φ hφ hIF (fun a => Submodule.subset_span ⟨a, rfl⟩)
    rw [hST] at key
    refine key.trans ?_
    have hr := sa4_rate_nonneg hε (sa2_q_nonneg S N) (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂)
      (sa2_sigma_nonneg S N) (hS.energy.pos N hN1).le (he N)
    have hX0 : 0 ≤ ∑ a, (wClass m p).norm (φ a) :=
      Finset.sum_nonneg fun a _ => ENNReal.toReal_nonneg
    refine sa2_stat_arith hK1 hM0 hX0 hr ht.1 ?_ hCK1
    exact sa2_Bs_final (mul_nonneg hKp0 (sa4X_nonneg _)) (mul_le_mul_of_nonneg_right
      (by rw [hκ]; linarith) (sa4X_nonneg _)) hκ0 hX0
  · -- (c)
    intro m₀ ε n ts φ hmono h0 hlast hφ hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have htsm : ∀ ab : Fin (n + 1) × Bool, ts ab.1 ∈ Set.Icc (0 : ℝ) S.T := fun ab =>
      ⟨h0.trans (hmono (Fin.zero_le _)), (hmono (Fin.le_last _)).trans hlast⟩
    have ht0 : 0 ≤ ts (Fin.last n) := h0.trans (hmono (Fin.zero_le _))
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have key := sa4_smooth_iota hS hd hN2' hc0 hCs (he N) hC₀c hCt hCy hC₀ hTest hY hm (hremU N hN2') (hAdj N hN1) hm₂ hmom
      (fun ab : Fin (n + 1) × Bool => ts ab.1) htsm (realImPartsRd φ) (sa4_realIm_mem hφ) hIF
      (fun ab => Submodule.subset_span ⟨ab, rfl⟩)
    rw [hST] at key
    refine key.trans ?_
    have hr := sa4_rate_nonneg hε (sa2_q_nonneg S N) (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂)
      (sa2_sigma_nonneg S N) (hS.energy.pos N hN1).le (he N)
    have hX0 : 0 ≤ ∑ a, (wClass m p).normC (φ a) :=
      Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _
    refine sa2_stat_arith hK1 hM0 hX0 hr ht0 ?_ hCK1
    refine sa2_Bs_final (mul_nonneg hKp0 (sa4X_nonneg _)) ?_ hκ0 hX0
    calc Kp * sa4X m p (realImPartsRd φ) ≤ Kp * (2 * ∑ a, (wClass m p).normC (φ a)) :=
          mul_le_mul_of_nonneg_left (sa4_realIm_X φ) hKp0
      _ = κ * ∑ a, (wClass m p).normC (φ a) := by rw [hκ]; ring
  · -- (d)
    intro m₀ ε 𝔈' ε2 n ts φ hmono h0 hlast hφ hIF hE2 N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have htsm : ∀ ab : Fin (n + 1) × Bool, ts ab.1 ∈ Set.Icc (0 : ℝ) S.T := fun ab =>
      ⟨h0.trans (hmono (Fin.zero_le _)), (hmono (Fin.le_last _)).trans hlast⟩
    have ht0 : 0 ≤ ts (Fin.last n) := h0.trans (hmono (Fin.zero_le _))
    have key := sa4_wass2_iota hS hd hN2' hc0 hCs (he N) hC₀c hCt hCy hC₀ hTest hY hm (hremU N hN2') (hAdj N hN1) hm₂ hmom
      (fun ab : Fin (n + 1) × Bool => ts ab.1) htsm (realImPartsRd φ) (sa4_realIm_mem hφ) hIF hE2
      (fun ab => Submodule.subset_span ⟨ab, rfl⟩)
    rw [hST] at key
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have hr := sa4_rate_nonneg (hE2.ε2_nonneg N hN1) (sa2_q_nonneg S N)
      (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂) (sa2_sigma_nonneg S N) (hE2.𝔈'_nonneg N hN1) (he N)
    have hX0 : 0 ≤ ∑ a, (wClass m p).normC (φ a) :=
      Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _
    refine sa2_stat_arith hK2 hM0 hX0 hr ht0 ?_ hCK2
    have hBs : Kp * sa4X m p (realImPartsRd φ) ≤ κ * ∑ a, (wClass m p).normC (φ a) := by
      calc Kp * sa4X m p (realImPartsRd φ) ≤ Kp * (2 * ∑ a, (wClass m p).normC (φ a)) :=
            mul_le_mul_of_nonneg_left (sa4_realIm_X φ) hKp0
        _ = κ * ∑ a, (wClass m p).normC (φ a) := by rw [hκ]; ring
    have := sa2_Bs_final (mul_nonneg hKp0 (sa4X_nonneg _)) hBs hκ0 hX0
    nlinarith [sq_nonneg (Kp * sa4X m p (realImPartsRd φ))]

end Parts

end HRS.MS.DecStat
