import HRS.MS.MainRdStatAux20

/-!
# SA2, packet 10b: the conclusions (a)-(d) of `RdStatParts` for a fixed realization sequence
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

theorem sa2_comm_mono {s Lm C₁ C₂ Cq : ℝ} (hCq : 0 ≤ Cq) (h : C₁ ≤ C₂) (hc : Sa2Comm d s Lm C₁ Cq) :
    Sa2Comm d s Lm C₂ Cq := by
  intro Λ' hΛ' N hN ρ hρ hρΛ hlog X hX v K hK
  obtain ⟨h1, h2⟩ := hc Λ' hΛ' N hN ρ hρ hρΛ hlog X hX v K hK
  refine ⟨h1, h2.trans ?_⟩
  have hK0 : 0 ≤ K := by
    obtain ⟨L, -, hL⟩ := hK
    exact (NNReal.coe_nonneg L).trans hL
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCq hK0)
  have hΛp : 0 ≤ Λ' ^ (s / d) := Real.rpow_nonneg (by linarith) _
  have hNp : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have : C₁ * Λ' ^ (s / d) * (N : ℝ) ^ (s / d - 1) ≤ C₂ * Λ' ^ (s / d) * (N : ℝ) ^ (s / d - 1) := by
    gcongr
  unfold oNΛ
  linarith

theorem sa2_rate_nonneg {ε q σ w E : ℝ} (hε : 0 ≤ ε) (hq : 0 ≤ q) (hw : 0 ≤ w) (hσ : 0 ≤ σ) (hE : 0 ≤ E) :
    0 ≤ rdRate ε q σ w E 0 := by
  unfold rdRate
  have := Real.sqrt_nonneg q
  have := Real.sqrt_nonneg w
  positivity

section Parts

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}

theorem sa2_parts (hd : 1 ≤ d) (hS : RdStanding S R MB Λ ΛV G₀ m20 (mStar d + 3) (mStar d + 4) C₀ 𝔈)
    {Lm C₀c Cq Ct Cy Kad : ℝ} {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ)
    (hLm : ∀ {N : ℕ}, 1 ≤ N → ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c) (hCt : 0 ≤ Ct) (hCy : 0 ≤ Cy)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) (hTest : Sa2Test d S.s χ C₀c Ct) (hY : Sa2Y0 d χ Cy)
    (hAdj : ∀ N : ℕ, 1 ≤ N →
      AdjointInputRd (ulocClass (mStar d) χ) (ulocClass (mStar d) χ) 2 (S.coeff N) S.T Kad)
    {m₂ : ℝ} (hm₂ : 0 ≤ m₂) (hmom : PropagatedSecondMoment S R m₂) {T : ℝ} (hST : S.T = T) {Cin : ℝ} :
    RdStatParts S R
      (max 2 (2 + ((1 / 2 * (Cq * ((d : ℝ) * d * MB)) * T + Cy + Ct * T + 2 * d * T) +
        (Cy + Real.sqrt (2 * Ct * T) + 1 / 2 * (Cq * ((d : ℝ) * d * MB)) * T)) *
          (2 * max Kad 0 + (2 * max Kad 0) ^ 2))) 1 (ulocClass (mStar d) χ) χ Cin C₀ Λ 𝔈 m₂
      (fun _ => 0) := by
  set Kp : ℝ := max Kad 0 with hKp
  set κ : ℝ := 2 * Kp with hκ
  have hKp0 : 0 ≤ Kp := le_max_right _ _
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  have hT0 : 0 ≤ T := by rw [← hST]; exact S.hT.le
  set c0 : ℝ := 1 / 2 * (Cq * ((d : ℝ) * d * MB)) with hc0def
  have hMB := sa2_cMB_nonneg (d := d) (MB := MB) (M := S.M) hS.matrix_bound
  have hc0 : 0 ≤ c0 := by rw [hc0def]; positivity
  set K1 : ℝ := c0 * T + Cy + Ct * T + 2 * d * T with hK1def
  set K2 : ℝ := Cy + Real.sqrt (2 * Ct * T) + c0 * T with hK2def
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
  have hLm' : ∀ {N : ℕ}, 2 ≤ N → ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm := fun {N} hN {t} ht => hLm (by omega) ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a)
    intro m₀ ε t φ ht hφ hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have key := sa2_wass1_iota hS hd hN2' (hLm' hN2') hcomm hCq hC₀c hCt hCy hC₀ hχ hTest hY (hAdj N hN1) hm₂ hmom
      (fun _ : Fin 1 => t) (fun _ => ht) (fun _ : Fin 1 => φ) (fun _ => hφ) hIF
      (fun a => Submodule.subset_span ⟨a, rfl⟩)
    rw [hST] at key
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have hr := sa2_rate_nonneg hε (sa2_q_nonneg S N) (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂)
      (sa2_sigma_nonneg S N) (hS.energy.pos N hN1).le
    have hX : sa2X χ (fun _ : Fin 1 => φ) = (ulocNormE (mStar d) χ φ).toReal := by simp [sa2X]
    have hX0 : 0 ≤ (ulocClass (mStar d) χ).norm φ := ENNReal.toReal_nonneg
    refine sa2_stat_arith hK2 hM0 hX0 hr ht.1 ?_ hCK2
    have hBs : Kp * sa2X χ (fun _ : Fin 1 => φ) ≤ κ * (ulocClass (mStar d) χ).norm φ := by
      rw [hX]
      exact mul_le_mul_of_nonneg_right (by rw [hκ]; linarith) ENNReal.toReal_nonneg
    have := sa2_Bs_final (mul_nonneg hKp0 (sa2X_nonneg _ _)) hBs hκ0 hX0
    nlinarith [sq_nonneg (Kp * sa2X χ (fun _ : Fin 1 => φ))]
  · -- (b)
    intro m₀ ε t p φ hp ht hφ hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have key := sa2_smooth_iota hS hd hN2' (hLm' hN2') hcomm hCq hC₀c hCt hCy hC₀ hχ hTest hY (hAdj N hN1) hm₂ hmom
      (fun _ : Fin p => t) (fun _ => ht) φ hφ hIF (fun a => Submodule.subset_span ⟨a, rfl⟩)
    rw [hST] at key
    refine key.trans ?_
    have hr := sa2_rate_nonneg hε (sa2_q_nonneg S N) (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂)
      (sa2_sigma_nonneg S N) (hS.energy.pos N hN1).le
    have hX0 : 0 ≤ ∑ a, (ulocClass (mStar d) χ).norm (φ a) :=
      Finset.sum_nonneg fun a _ => ENNReal.toReal_nonneg
    refine sa2_stat_arith hK1 hM0 hX0 hr ht.1 ?_ hCK1
    exact sa2_Bs_final (mul_nonneg hKp0 (sa2X_nonneg _ _)) (mul_le_mul_of_nonneg_right
      (by rw [hκ]; linarith) (sa2X_nonneg _ _)) hκ0 hX0
  · -- (c)
    intro m₀ ε n ts φ hmono h0 hlast hφ hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have htsm : ∀ ab : Fin (n + 1) × Bool, ts ab.1 ∈ Set.Icc (0 : ℝ) S.T := fun ab =>
      ⟨h0.trans (hmono (Fin.zero_le _)), (hmono (Fin.le_last _)).trans hlast⟩
    have ht0 : 0 ≤ ts (Fin.last n) := h0.trans (hmono (Fin.zero_le _))
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have key := sa2_smooth_iota hS hd hN2' (hLm' hN2') hcomm hCq hC₀c hCt hCy hC₀ hχ hTest hY (hAdj N hN1) hm₂ hmom
      (fun ab : Fin (n + 1) × Bool => ts ab.1) htsm (realImPartsRd φ) (sa2_realIm_mem hφ) hIF
      (fun ab => Submodule.subset_span ⟨ab, rfl⟩)
    rw [hST] at key
    refine key.trans ?_
    have hr := sa2_rate_nonneg hε (sa2_q_nonneg S N) (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂)
      (sa2_sigma_nonneg S N) (hS.energy.pos N hN1).le
    have hX0 : 0 ≤ ∑ a, (ulocClass (mStar d) χ).normC (φ a) :=
      Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _
    refine sa2_stat_arith hK1 hM0 hX0 hr ht0 ?_ hCK1
    refine sa2_Bs_final (mul_nonneg hKp0 (sa2X_nonneg _ _)) ?_ hκ0 hX0
    calc Kp * sa2X χ (realImPartsRd φ) ≤ Kp * (2 * ∑ a, (ulocClass (mStar d) χ).normC (φ a)) :=
          mul_le_mul_of_nonneg_left (sa2_realIm_X φ) hKp0
      _ = κ * ∑ a, (ulocClass (mStar d) χ).normC (φ a) := by rw [hκ]; ring
  · -- (d)
    intro m₀ ε 𝔈' ε2 n ts φ hmono h0 hlast hφ hIF hE2 N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have htsm : ∀ ab : Fin (n + 1) × Bool, ts ab.1 ∈ Set.Icc (0 : ℝ) S.T := fun ab =>
      ⟨h0.trans (hmono (Fin.zero_le _)), (hmono (Fin.le_last _)).trans hlast⟩
    have ht0 : 0 ≤ ts (Fin.last n) := h0.trans (hmono (Fin.zero_le _))
    have key := sa2_wass2_iota hS hd hN2' (hLm' hN2') hcomm hCq hC₀c hCt hCy hC₀ hχ hTest hY (hAdj N hN1) hm₂ hmom
      (fun ab : Fin (n + 1) × Bool => ts ab.1) htsm (realImPartsRd φ) (sa2_realIm_mem hφ) hIF hE2
      (fun ab => Submodule.subset_span ⟨ab, rfl⟩)
    rw [hST] at key
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have hr := sa2_rate_nonneg (hE2.ε2_nonneg N hN1) (sa2_q_nonneg S N)
      (sa2_wN_nonneg (d := d) (N := N) (hS.energy.pos N hN1).le hm₂) (sa2_sigma_nonneg S N) (hE2.𝔈'_nonneg N hN1)
    have hX0 : 0 ≤ ∑ a, (ulocClass (mStar d) χ).normC (φ a) :=
      Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _
    refine sa2_stat_arith hK2 hM0 hX0 hr ht0 ?_ hCK2
    have hBs : Kp * sa2X χ (realImPartsRd φ) ≤ κ * ∑ a, (ulocClass (mStar d) χ).normC (φ a) := by
      calc Kp * sa2X χ (realImPartsRd φ) ≤ Kp * (2 * ∑ a, (ulocClass (mStar d) χ).normC (φ a)) :=
            mul_le_mul_of_nonneg_left (sa2_realIm_X φ) hKp0
        _ = κ * ∑ a, (ulocClass (mStar d) χ).normC (φ a) := by rw [hκ]; ring
    have := sa2_Bs_final (mul_nonneg hKp0 (sa2X_nonneg _ _)) hBs hκ0 hX0
    nlinarith [sq_nonneg (Kp * sa2X χ (realImPartsRd φ))]

end Parts

end HRS.MS.MainRdStat
