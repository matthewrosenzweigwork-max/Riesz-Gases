import HRS.MC.S7FCH2E

/-!
# H2, part F: the estimate for a fixed `N` in the pair norm

`S7FCH2_main_est`: for `Q > 2`,
`E ‖(pairN).2 - toL2 (fcPartAt ..)‖^Q ≤ T^{Q/2-1} · C_Q · (T · tail_S + ∑_{k∈S} ∫_0^T φ_{L,k}(t) dt)`,
where `φ_{L,k}(t) = sup_{N ≥ 2} E |N F^{K_{k,L} - h_k}(X_N^t, μ^t)|^Q` (dominated convergence in `t`, part D).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH2

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan
  HRS.MC.Sec7.S7FCF5F HRS.MC.Sec7.S7FCF5J

variable {d : ℕ}

/-- The constant `2^{Q-1} · 2 Z^{Q/2-1}`. -/
def S7FCH2_Cq (d : ℕ) (r Q : ℝ) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (Q - 1) * (2 * ENNReal.ofReal (fcf5Z d r ^ (Q / 2 - 1)))

theorem S7FCH2_main_est (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {ε₂ c : ℝ} (K : NonzeroLattice d → ℕ → FRKernel d) (hK : FCKernelData R ε₂ c K)
    {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (X₀ : ∀ N, Ω N → Config d N)
    (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d)) (X : ∀ N, ℝ≥0 → Ω N → Config d N)
    (hreal : ∀ N, 1 ≤ N → PreparedRealization R.D (P N)
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) (X₀ N) (W N) (X N))
    (Q : ℝ) (hQ : 2 < Q) (C2 : ℝ) (hC2 : 0 ≤ C2)
    (hF2 : ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      Integrable (fun ω => |S7FCF5F_c R (X N) t k ω| ^ Q) (P N) ∧
      ∫ ω, |S7FCF5F_c R (X N) t k ω| ^ Q ∂(P N) ≤ C2 * Lattice.jp k.1 ^ (2 * Q))
    (S : Finset (NonzeroLattice d)) (L N : ℕ) (hN : 2 ≤ N) :
    ∫⁻ ω, ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2 -
        toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω)‖ₑ ^ Q
        ∂(P N) ≤
      ENNReal.ofReal (T ^ (Q / 2 - 1)) * (S7FCH2_Cq d r Q * (S7FCH2_tail d r C2 S * ENNReal.ofReal T +
        ∑ k ∈ S, ∫⁻ t in Set.Icc (0 : ℝ) T, S7FCH2_phi R Q (K k L) k P X t)) := by
  classical
  have hprep := hreal N (by omega)
  have hS := hprep.solution T
  obtain ⟨Fa, hFa, N0a, hN0am, hN0a, hkeya⟩ :=
    S7FCF5J_joint_modif R r 0 T hT le_rfl (P N) (X N) hS.adapted hS.cont
  obtain ⟨Fb, hFb, N0b, hN0bm, hN0b, hkeyb⟩ :=
    S7FCH2_joint_modif_fc R r T hT S (fun k => K k L) (P N) (X N) hS.adapted hS.cont
  set ψ : ℝ → ℝ≥0∞ := fun t => S7FCH2_Cq d r Q * (S7FCH2_tail d r C2 S +
    ∑ k ∈ S, S7FCH2_phi R Q (K k L) k P X t) with hψ
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂(P N) ≤ ψ t := by
    intro t ht
    have hpt := S7FCH2_pertime R r hr Q hQ.le (P N) (X N) t ht.1 (hS.adapted _) hK.1 S (fun k => K k L) C2 hC2
      (hF2 N hN t ht.1) (fun k => S7FCH2_phi R Q (K k L) k P X t) (fun k _ =>
        le_iSup (fun N' : {N' : ℕ // 2 ≤ N'} => S7FCH2_g R Q (K k L) k (P N'.1) (X N'.1) t) ⟨N, hN⟩)
    have hcg : ∫⁻ ω, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂(P N) =
        ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) (P N) (X N) t ω -
          fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) t ω‖ₑ ^ Q ∂(P N) := by
      refine lintegral_congr_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0a, measure_eq_zero_iff_ae_notMem.1 hN0b] with ω h1 h2
      rw [hkeya ω h1 t ht, hkeyb ω h2 t ht, zero_add]
    rw [hcg]
    refine hpt.trans ?_
    have hw := S7FCH2_wsum_le r hr Q hQ.le S C2 hC2 (fun k => S7FCH2_phi R Q (K k L) k P X t)
    have hHb : S7FCH2_Hbd d r Q (S7FCH2_wu S C2 Q (fun k => S7FCH2_phi R Q (K k L) k P X t)) ≤
        ENNReal.ofReal (fcf5Z d r ^ (Q / 2 - 1)) * (S7FCH2_tail d r C2 S +
          ∑ k ∈ S, S7FCH2_phi R Q (K k L) k P X t) := mul_le_mul' le_rfl hw
    calc (2 : ℝ≥0∞) ^ (Q - 1) * (S7FCH2_Hbd d r Q (S7FCH2_wu S C2 Q (fun k => S7FCH2_phi R Q (K k L) k P X t)) +
          S7FCH2_Hbd d r Q (S7FCH2_wu S C2 Q (fun k => S7FCH2_phi R Q (K k L) k P X t)))
        = (2 : ℝ≥0∞) ^ (Q - 1) * (2 * S7FCH2_Hbd d r Q
          (S7FCH2_wu S C2 Q (fun k => S7FCH2_phi R Q (K k L) k P X t))) := by rw [two_mul]
      _ ≤ (2 : ℝ≥0∞) ^ (Q - 1) * (2 * (ENNReal.ofReal (fcf5Z d r ^ (Q / 2 - 1)) * (S7FCH2_tail d r C2 S +
          ∑ k ∈ S, S7FCH2_phi R Q (K k L) k P X t))) := by gcongr
      _ = ψ t := by simp only [hψ, S7FCH2_Cq]; ring
  have h1 := S7FCH2_asm (P N) r T Q hT hQ Fa Fb hFa hFb ψ hbd
  have hcongr : ∀ᵐ ω ∂(P N), ‖(pairN r T 0 R.D.s R.ρ (P N) (X N) ω).2 -
        toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω)‖ₑ ^ Q =
      ‖HRS.Sec7.toL2 r T (fun t => Fa t ω) - HRS.Sec7.toL2 r T (fun t => Fb t ω)‖ₑ ^ Q := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0a, measure_eq_zero_iff_ae_notMem.1 hN0b] with ω h1 h2
    have e1 : HRS.Sec7.toL2 r T (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω) =
        HRS.Sec7.toL2 r T (fun t => Fa t ω) :=
      HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_congr r T _ _ fun t ht => (hkeya ω h1 t ht).symm
    have e2 : HRS.Sec7.toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t))
        (P N) (X N) (0 + t) ω) = HRS.Sec7.toL2 r T (fun t => Fb t ω) :=
      HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_congr r T _ _ fun t ht => (hkeyb ω h2 t ht).symm
    show ‖HRS.Sec7.toL2 r T (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) (P N) (X N) (0 + t) ω) -
        HRS.Sec7.toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t))
          (P N) (X N) (0 + t) ω)‖ₑ ^ Q = _
    rw [e1, e2]
  rw [lintegral_congr_ae hcongr]
  refine h1.trans ?_
  -- the time integral of `ψ`
  have hCq : S7FCH2_Cq d r Q ≠ ⊤ := by
    unfold S7FCH2_Cq
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofNat_ne_top)
      (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
  have hphim : ∀ k ∈ S, AEMeasurable (fun t => S7FCH2_phi R Q (K k L) k P X t) (volume.restrict (Set.Icc 0 T)) :=
    fun k _ => S7FCH2_phi_aemeasurable R T hT Q (K k L) k P X₀ W X hreal
  have hint : ∫⁻ t in Set.Icc (0 : ℝ) T, ψ t = S7FCH2_Cq d r Q * (S7FCH2_tail d r C2 S * ENNReal.ofReal T +
      ∑ k ∈ S, ∫⁻ t in Set.Icc (0 : ℝ) T, S7FCH2_phi R Q (K k L) k P X t) := by
    simp only [hψ]
    rw [lintegral_const_mul' _ _ hCq, lintegral_add_left measurable_const, lintegral_const,
      Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      lintegral_finset_sum' S hphim]
  rw [hint]

end HRS.MC.Sec7.S7FCH2

end
