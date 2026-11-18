import HRS.Equilibrium.Parametrix.PX4aAuxG

/-!
# Packet PX4a auxiliaries H: the chart potential is a conormal kernel of order `σ + s - d`

`kpot_chart_conormal`: for a chart source `g` (supported in `‖w‖ < 1/32`, periodic in `Y`) of class
`SrcCls σ b m`, the kernel `ofChart ((X, z) ↦ kPot k g (X - z/2, z))` is in `ConormalL (σ + s - d)
(b + 1) m`.  (`Y = X - z/2` is the left chart; the shear costs `(3/2)^c`.)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Chart

variable {s : ℝ} {k : Euc d → ℝ}

lemma kPot_zero_of_far (hk : LocKer d s k) {g : Euc d × Euc d → ℝ}
    (hz : ∀ X w : Euc d, 1 / 32 < ‖w‖ → g (X, w) = 0) (Y z : Euc d) (hzn : 1 / 16 ≤ ‖z‖) :
    kPot d k g (Y, z) = 0 := by
  unfold kPot
  refine integral_eq_zero_of_ae (Eventually.of_forall fun w => ?_)
  show k ((Y, z).2 - w) * g ((Y, z).1, w) = 0
  by_cases hw : 1 / 32 < ‖w‖
  · simp [hz Y w hw]
  · have : 1 / 64 ≤ ‖z - w‖ := by
      have := norm_sub_norm_le z w
      linarith [not_lt.mp hw]
    simp [hk.supp _ this]

lemma kPot_periodic {g : Euc d × Euc d → ℝ}
    (hper : ∀ X w n : Euc d, IsLat n → g (X + n, w) = g (X, w)) (Y z n : Euc d) (hn : IsLat n) :
    kPot d k g (Y + n, z) = kPot d k g (Y, z) := by
  unfold kPot
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [hper Y w n hn]

set_option maxHeartbeats 1600000 in
theorem kpot_chart_conormal (hd : 2 ≤ d) (hk : LocKer d s k) {σ : ℝ} (hσ : σ < d) (b m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (g : Euc d × Euc d → ℝ), 0 ≤ A → SrcCls d σ b m A g →
      (∀ X w : Euc d, 1 / 32 < ‖w‖ → g (X, w) = 0) →
      (∀ X w n : Euc d, IsLat n → g (X + n, w) = g (X, w)) →
      ConormalL (σ + s - d) (fun _ => b + 1) m (C * A)
        (ofChart (fun p => kPot d k g (shearCLM d (-(1 / 2 : ℝ)) p))) := by
  have hd1 : 1 ≤ d := by omega
  choose C hC0 hCb using fun c : ℕ => kpot_bound hd hk c hσ b m
  set Cm : ℝ := ∑ j ∈ Finset.range (m + 1), C j with hCm
  have hCm0 : 0 ≤ Cm := Finset.sum_nonneg fun j _ => hC0 j
  have hCle : ∀ j ≤ m, C j ≤ Cm := fun j hj =>
    Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.mpr (by omega))
  refine ⟨(3 / 2 : ℝ) ^ m * Cm, by positivity, fun A g hA h hz hper => ?_⟩
  have hU := isOpen_chartU (d := d)
  have hcdU : ContDiffOn ℝ (m : WithTop ℕ∞) (kPot d k g)
      {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := kPot_contDiffOn hd1 hk hσ hA h
  have hTU : ∀ p : Euc d × Euc d, p ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} →
      shearCLM d (-(1 / 2 : ℝ)) p ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := by
    intro p hp; simpa [shearCLM_apply] using hp
  have hNU : ContDiffOn ℝ (m : WithTop ℕ∞) (fun p => kPot d k g (shearCLM d (-(1 / 2 : ℝ)) p))
      {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} :=
    hcdU.comp (shearCLM d (-(1 / 2 : ℝ))).contDiff.contDiffOn hTU
  have hzero : ∀ p : Euc d × Euc d, 1 / 8 ≤ ‖p.2‖ →
      (fun p => kPot d k g (shearCLM d (-(1 / 2 : ℝ)) p)) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
    intro p hp
    filter_upwards [(isOpen_lt continuous_const (continuous_norm.comp continuous_snd)).mem_nhds
      (show (1 / 16 : ℝ) < ‖p.2‖ by linarith)] with p' hp'
    have hp'' : (1 / 16 : ℝ) < ‖p'.2‖ := hp'
    simp only [shearCLM_apply]
    exact kPot_zero_of_far hk hz _ _ hp''.le
  have hNsm : ContDiffOn ℝ (m : WithTop ℕ∞) (fun p => kPot d k g (shearCLM d (-(1 / 2 : ℝ)) p))
      {p : Euc d × Euc d | p.2 ≠ 0} := by
    intro p hp
    by_cases h8 : ‖p.2‖ < 1 / 8
    · have hpU : p ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := ⟨norm_pos_iff.mpr hp, h8⟩
      exact (hNU.contDiffAt (hU.mem_nhds hpU)).contDiffWithinAt
    · exact ((contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq (hzero p (not_lt.mp h8))).contDiffWithinAt
  refine conormalL_ofChart (mul_nonneg (by positivity) hA) hNsm ?_ ?_ ?_
  · intro X z n hn
    simp only [shearCLM_apply]
    have : X + n + (-(1 / 2 : ℝ)) • z = (X + (-(1 / 2 : ℝ)) • z) + n := by abel
    rw [this]
    exact kPot_periodic hper _ _ n hn
  · intro X w hw
    simp only [shearCLM_apply]
    exact kPot_zero_of_far hk hz _ _ hw
  · intro a c hac X z hz0 hzr
    have hzr' : ‖z‖ < 1 / 8 := by unfold r0 at hzr; exact hzr
    have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    set r : ℝ := ‖z‖ with hr
    have hq : ((X, z) : Euc d × Euc d) ∈ {p : Euc d × Euc d | 0 < ‖p.2‖ ∧ ‖p.2‖ < 1 / 8} := ⟨hzpos, hzr'⟩
    have hTq := hTU _ hq
    set W : ℕ → ℝ := fun j' => Cm * A * (1 + r ^ (-(σ + s - d + (j' : ℝ))) * lw r ^ (b + 1)) with hW
    have hWmono : ∀ j', W j' ≤ W (j' + 1) := by
      intro j'
      simp only [hW]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCm0 hA)
      have h1 : r ^ (-(σ + s - d + (j' : ℝ))) ≤ r ^ (-(σ + s - d + ((j' + 1 : ℕ) : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_ge hzpos (by linarith) (by push_cast; linarith)
      have h2 : 0 ≤ lw r ^ (b + 1) := pow_nonneg (lw_pos _).le _
      nlinarith
    have hT : ∀ i' j', i' + j' ≤ a + c →
        TB (kPot d k g) (shearCLM d (-(1 / 2 : ℝ)) (X, z)) i' j' (W j') := by
      intro i' j' hij u v
      have hj' : j' ≤ m := by omega
      have := hCb j' h hA (a := i') (by omega) hzpos hzr' (X + (-(1 / 2 : ℝ)) • z) z rfl u v
      refine this.trans ?_
      have hP : 0 ≤ (∏ i, ‖u i‖) * ∏ j, ‖v j‖ :=
        mul_nonneg (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      have hw0 : 0 ≤ 1 + r ^ (-(σ + s - d + (j' : ℝ))) * lw r ^ (b + 1) := by
        have : 0 ≤ r ^ (-(σ + s - d + (j' : ℝ))) * lw r ^ (b + 1) :=
          mul_nonneg (Real.rpow_nonneg hzpos.le _) (pow_nonneg (lw_pos _).le _)
        linarith
      have h1 : C j' * A * (1 + r ^ (-(σ + s - d + (j' : ℝ))) * lw r ^ (b + 1)) ≤ W j' := by
        simp only [hW]
        have := hCle j' hj'
        have : C j' * A ≤ Cm * A := mul_le_mul_of_nonneg_right this hA
        exact mul_le_mul_of_nonneg_right this hw0
      calc C j' * A * (1 + r ^ (-(σ + s - d + (j' : ℝ))) * lw r ^ (b + 1)) *
            ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) ≤ W j' * ((∏ i, ‖u i‖) * ∏ j, ‖v j‖) :=
            mul_le_mul_of_nonneg_right h1 hP
        _ = _ := by ring
    have hTB := tb_shear (-(1 / 2 : ℝ)) hU c a (kPot d k g) W hWmono
      (hcdU.of_le (by exact_mod_cast hac)) (X, z) hTq hT
    have hW0 : 0 ≤ (1 + |-(1 / 2 : ℝ)|) ^ c * W c := by
      simp only [hW]
      have : 0 ≤ r ^ (-(σ + s - d + (c : ℝ))) * lw r ^ (b + 1) :=
        mul_nonneg (Real.rpow_nonneg hzpos.le _) (pow_nonneg (lw_pos _).le _)
      positivity
    have hn := norm_le_of_tb hU (hNU.of_le (by exact_mod_cast hac)) hq hW0 hTB
    refine hn.trans ?_
    have hab : 1 + |-(1 / 2 : ℝ)| = 3 / 2 := by norm_num [abs_neg]
    rw [hab]
    have h1 : (3 / 2 : ℝ) ^ c ≤ (3 / 2) ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
    simp only [hW]
    have hw0 : 0 ≤ 1 + r ^ (-(σ + s - d + (c : ℝ))) * lw r ^ (b + 1) := by
      have : 0 ≤ r ^ (-(σ + s - d + (c : ℝ))) * lw r ^ (b + 1) :=
        mul_nonneg (Real.rpow_nonneg hzpos.le _) (pow_nonneg (lw_pos _).le _)
      linarith
    calc (3 / 2 : ℝ) ^ c * (Cm * A * (1 + r ^ (-(σ + s - d + (c : ℝ))) * lw r ^ (b + 1)))
        ≤ (3 / 2 : ℝ) ^ m * (Cm * A * (1 + r ^ (-(σ + s - d + (c : ℝ))) * lw r ^ (b + 1))) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg (mul_nonneg hCm0 hA) hw0)
      _ = _ := by simp only [lw]; ring

end Chart

end HRS.Parx

end
