import HRS.MC.S7FCH2G
import HRS.MC.S7UCDefs

/-!
# S7UCPA: H2 at window `a` (part A): joint modifications and the fixed-`N` estimate

* `S7UCP_joint_modif_fc`: a jointly measurable modification of `t ↦ fcPartAt (a+t) ω` (`S7FCH2_joint_modif_fc` with window start `a`);
* `S7UCP_modifs`: simultaneous jointly measurable modifications `Fa, Fb` of the quadratic field and of the finite-rank field;
* `S7UCP_main_est`: `S7FCH2_main_est` at window `a`, with the time integral of `φ` replaced by the constant uniform
  majorant `Φ_k ≥ sup_{t ≥ 0, N ≥ 2} g_{N,k}(t)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCP

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.FCF5Plan
  HRS.MC.Sec7.S7FCF5F HRS.MC.Sec7.S7FCF5J HRS.MC.Sec7.S7FCH2

variable {d : ℕ}

/-- A jointly measurable modification of `t ↦ fcPartAt (a+t) ω`. -/
theorem S7UCP_joint_modif_fc (R : Regime d) (r T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    ∃ Fp : ℝ → Ω → NegSobolev d r, Measurable (Function.uncurry Fp) ∧
      ∃ N0 : Set Ω, MeasurableSet N0 ∧ P N0 = 0 ∧
        ∀ ω ∉ N0, ∀ t ∈ Set.Icc (0 : ℝ) T,
          Fp t ω = fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω := by
  have hc0 : ∀ᵐ ω ∂P, ContinuousOn (fun t => X (a + t).toNNReal ω) (Set.Icc 0 T) :=
    hcont.mono fun ω hω => (continuous_pi fun i =>
      (hω i).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_id))).continuousOn
  obtain ⟨V, hVm, N0, hN0m, hN0, hVN⟩ := HRS.MC.Sec7.S7FCW12.s7fcw12_caratheodory P hT.le
    (fun t ω => X (a + t).toNNReal ω) (fun t => hadapt _) hc0 0
  set G : ℝ × Ω → NegSobolev d r := fun q =>
    fcPartTilde r S K (withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (a + q.1, y)) (V q.1 q.2)
    with hG_def
  have hGm : Measurable G :=
    HRS.MC.Sec7.S7FCW12.s7fcw12_fcPartTilde_measurable R r S K (fun q : ℝ × Ω => a + q.1) (by fun_prop)
      (fun q => V q.1 q.2) hVm
  set M : ℝ → NegSobolev d r := fun t => ∫ ω', G (t, ω') ∂P with hM_def
  have hM : Measurable M := (hGm.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  refine ⟨fun t ω => G (t, ω) - M t, hGm.sub (hM.comp measurable_fst), N0, hN0m, hN0, ?_⟩
  intro ω hω t ht
  have hat : 0 ≤ a + t := add_nonneg ha ht.1
  have hμ : withDensityReal (R.ρ (a + t)) =
      withDensityReal fun y => HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos R (a + t, y) := by
    congr 1
    funext y
    rw [HRS.MC.Sec7.S7FCW12.s7fcw12_rhoPos_eq R hat y]
  have hV1 : X (a + t).toNNReal ω = V t ω := (hVN ω hω t ht).symm
  have hV2 : ∀ᵐ ω' ∂P, X (a + t).toNNReal ω' = V t ω' := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω' hω'
    exact (hVN ω' hω' t ht).symm
  show G (t, ω) - ∫ ω', G (t, ω') ∂P = _
  show _ = fcPartTilde r S K (withDensityReal (R.ρ (a + t))) (X (a + t).toNNReal ω) -
      ∫ ω', fcPartTilde r S K (withDensityReal (R.ρ (a + t))) (X (a + t).toNNReal ω') ∂P
  rw [hμ, hV1, integral_congr_ae (hV2.mono fun ω' h' => congrArg _ h')]

/-- Simultaneous jointly measurable modifications of the quadratic field and of the finite-rank field at window `a`. -/
theorem S7UCP_modifs (R : Regime d) (r : ℝ) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    ∃ Fa Fb : ℝ → Ω → NegSobolev d r, Measurable (Function.uncurry Fa) ∧ Measurable (Function.uncurry Fb) ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
        Fa t ω = quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω ∧
        Fb t ω = fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω := by
  obtain ⟨Fa, hFa, N0a, -, hN0a, hkeya⟩ := S7FCF5J_joint_modif R r a T hT ha P X hadapt hcont
  obtain ⟨Fb, hFb, N0b, -, hN0b, hkeyb⟩ := S7UCP_joint_modif_fc R r T hT a ha S K P X hadapt hcont
  refine ⟨Fa, Fb, hFa, hFb, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0a, measure_eq_zero_iff_ae_notMem.1 hN0b] with ω h1 h2 t ht
  exact ⟨hkeya ω h1 t ht, hkeyb ω h2 t ht⟩

/-- `S7FCH2_main_est` at window `a`, with a constant uniform majorant `Φ k ≥ g_{N,k}(t)` for all `t ≥ 0`, `N ≥ 2`. -/
theorem S7UCP_main_est (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
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
    (S : Finset (NonzeroLattice d)) (L : ℕ) (Φ : NonzeroLattice d → ℝ≥0∞)
    (hΦ : ∀ k ∈ S, ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → S7FCH2_g R Q (K k L) k (P N) (X N) t ≤ Φ k)
    (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 2 ≤ N) :
    ∫⁻ ω, ‖(pairN r T a R.D.s R.ρ (P N) (X N) ω).2 -
        toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω)‖ₑ ^ Q
        ∂(P N) ≤
      ENNReal.ofReal (T ^ (Q / 2 - 1)) * (S7FCH2_Cq d r Q * (S7FCH2_tail d r C2 S + ∑ k ∈ S, Φ k) *
        ENNReal.ofReal T) := by
  classical
  have hprep := hreal N (by omega)
  have hS := hprep.solution T
  obtain ⟨Fa, Fb, hFa, hFb, hkey⟩ := S7UCP_modifs R r T hT a ha S (fun k => K k L) (P N) (X N) hS.adapted hS.cont
  set ψ0 : ℝ≥0∞ := S7FCH2_Cq d r Q * (S7FCH2_tail d r C2 S + ∑ k ∈ S, Φ k) with hψ0
  -- the per-time bound, for a fixed `ω`-independent `t`
  have hbd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫⁻ ω, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂(P N) ≤ ψ0 := by
    intro t ht
    have hat : 0 ≤ a + t := add_nonneg ha ht.1
    have hpt := S7FCH2_pertime R r hr Q hQ.le (P N) (X N) (a + t) hat (hS.adapted _) hK.1 S (fun k => K k L) C2 hC2
      (hF2 N hN (a + t) hat) Φ (fun k hk => hΦ k hk N hN (a + t) hat)
    have hcg : ∫⁻ ω, ‖Fa t ω - Fb t ω‖ₑ ^ Q ∂(P N) =
        ∫⁻ ω, ‖quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω -
          fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω‖ₑ ^ Q ∂(P N) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hkey] with ω h
      rw [(h t ht).1, (h t ht).2]
    rw [hcg]
    refine hpt.trans ?_
    have hw := S7FCH2_wsum_le r hr Q hQ.le S C2 hC2 Φ
    have hHb : S7FCH2_Hbd d r Q (S7FCH2_wu S C2 Q Φ) ≤
        ENNReal.ofReal (fcf5Z d r ^ (Q / 2 - 1)) * (S7FCH2_tail d r C2 S + ∑ k ∈ S, Φ k) := mul_le_mul' le_rfl hw
    calc (2 : ℝ≥0∞) ^ (Q - 1) * (S7FCH2_Hbd d r Q (S7FCH2_wu S C2 Q Φ) + S7FCH2_Hbd d r Q (S7FCH2_wu S C2 Q Φ))
        = (2 : ℝ≥0∞) ^ (Q - 1) * (2 * S7FCH2_Hbd d r Q (S7FCH2_wu S C2 Q Φ)) := by rw [two_mul]
      _ ≤ (2 : ℝ≥0∞) ^ (Q - 1) * (2 * (ENNReal.ofReal (fcf5Z d r ^ (Q / 2 - 1)) *
          (S7FCH2_tail d r C2 S + ∑ k ∈ S, Φ k))) := by gcongr
      _ = ψ0 := by simp only [hψ0, S7FCH2_Cq]; ring
  have h1 := S7FCH2_asm (P N) r T Q hT hQ Fa Fb hFa hFb (fun _ => ψ0) hbd
  have hcongr : ∀ᵐ ω ∂(P N), ‖(pairN r T a R.D.s R.ρ (P N) (X N) ω).2 -
        toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω)‖ₑ ^ Q =
      ‖HRS.Sec7.toL2 r T (fun t => Fa t ω) - HRS.Sec7.toL2 r T (fun t => Fb t ω)‖ₑ ^ Q := by
    filter_upwards [hkey] with ω h
    have e1 : HRS.Sec7.toL2 r T (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω) =
        HRS.Sec7.toL2 r T (fun t => Fa t ω) :=
      HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_congr r T _ _ fun t ht => ((h t ht).1).symm
    have e2 : HRS.Sec7.toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t))
        (P N) (X N) (a + t) ω) = HRS.Sec7.toL2 r T (fun t => Fb t ω) :=
      HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_congr r T _ _ fun t ht => ((h t ht).2).symm
    show ‖HRS.Sec7.toL2 r T (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) (P N) (X N) (a + t) ω) -
        HRS.Sec7.toL2 r T (fun t => fcPartAt r S (fun k => K k L) (fun t => withDensityReal (R.ρ t))
          (P N) (X N) (a + t) ω)‖ₑ ^ Q = _
    rw [e1, e2]
  rw [lintegral_congr_ae hcongr]
  refine h1.trans ?_
  rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]

/-- The difference of the two `L²` components at window `a` is `AEMeasurable`. -/
theorem S7UCP_diff_aemeasurable (R : Regime d) (r : ℝ) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d)
    {Ω : Type} [MeasurableSpace Ω] {N : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → Config d N) (hadapt : ∀ t : ℝ≥0, Measurable (X t))
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    AEMeasurable (fun ω => (pairN r T a R.D.s R.ρ P X ω).2 -
      toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω)) P := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  obtain ⟨Fa, Fb, hFa, hFb, hkey⟩ := S7UCP_modifs R r T hT a ha S K P X hadapt hcont
  have hm : AEMeasurable (fun ω => HRS.Sec7.toL2 r T (fun t => Fa t ω) -
      HRS.Sec7.toL2 r T (fun t => Fb t ω)) P :=
    (HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_measurable T Fa hFa).aemeasurable.sub
      (HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_measurable T Fb hFb).aemeasurable
  refine hm.congr ?_
  filter_upwards [hkey] with ω h
  have e1 : HRS.Sec7.toL2 r T (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω) =
      HRS.Sec7.toL2 r T (fun t => Fa t ω) :=
    HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_congr r T _ _ fun t ht => ((h t ht).1).symm
  have e2 : HRS.Sec7.toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t))
      P X (a + t) ω) = HRS.Sec7.toL2 r T (fun t => Fb t ω) :=
    HRS.MC.Sec7.S7FCW12.s7fcw12_toL2_congr r T _ _ fun t ht => ((h t ht).2).symm
  show _ = HRS.Sec7.toL2 r T (fun t => quadFieldAt r R.D.s (fun t => withDensityReal (R.ρ t)) P X (a + t) ω) -
      HRS.Sec7.toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω)
  rw [e1, e2]

end HRS.MC.Sec7.S7UCP

end
