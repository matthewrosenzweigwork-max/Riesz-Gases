import HRS.MS.SA16TMo1

/-!
# S.A.16 (SA16T) Mo2: the mollified density path satisfies `AdjointRdData` (sub case)

`sa16t_adjData`: if `AdjointRdData s m MB Λ ΛV G₀ νbar D T μ` holds and `s ≤ d - 2`, then
`AdjointRdData s m MB (sa16t_Lam1 d m Λ) ΛV G₀ νbar D T (sa16t_mu d n μ)` for every `n`, where
`sa16t_mu d n μ r = ρ_n ⋆ μ r` and `sa16t_Lam1` does not depend on `n`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P

section Mo2
variable {d : ℕ}

/-- the mollified density path -/
def sa16t_mu (d n : ℕ) (μ : ℝ → Euc d → ℝ) : ℝ → Euc d → ℝ := fun r => sa16j_conv (sa16y_rho d n) (μ r)

/-- the decay constant of `μ r` -/
def sa16t_A0 (d m : ℕ) (Λ : ℝ) : ℝ := (d : ℝ) ^ (m + 3) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)

/-- the `n`-independent regularity constant of the mollified path -/
def sa16t_Lam1 (d m : ℕ) (Λ : ℝ) : ℝ :=
  ((m + 3 : ℕ) + 2) * (((d : ℝ) + 1) ^ (m + 3) * (2 ^ ((d : ℝ) + 3) * sa16t_A0 d m Λ))

lemma sa16t_A0_nonneg (d m : ℕ) (Λ : ℝ) : 0 ≤ sa16t_A0 d m Λ := by unfold sa16t_A0; positivity

lemma sa16t_mu_decay {s Λ T : ℝ} {m : ℕ} {μ : ℝ → Euc d → ℝ} (hd : 1 ≤ d) (hμ : CoeffHypRd s m Λ T μ) {r : ℝ}
    (hr : r ∈ Icc (0 : ℝ) T) :
    ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (μ r) ∧
      ∀ j ≤ m + 3, ∀ y, ‖iteratedFDeriv ℝ j (μ r) y‖ ≤ sa16t_A0 d m Λ * sa16p_w d y := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hreg := sa16so_regDensity_of_MF hμ.regular hr
  refine ⟨hreg.1, fun j hj y => ?_⟩
  refine (sa16p_regular_bounds hreg j hj y).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (sa16p_w_pos y).le
  have : (d : ℝ) ^ j ≤ (d : ℝ) ^ (m + 3) := pow_le_pow_right₀ hd1 hj
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this (le_max_right _ _)) (by positivity)

lemma sa16t_regMF_of_density {r : ℕ} {Λ : ℝ} (hΛ : 0 ≤ Λ) {ρ : Euc d → ℝ} (h : IsRegularDensityW r Λ ρ) :
    MemCb r ρ ∧ weightedSupE r ((d : ℝ) + 3) ρ < ⊤ ∧
      cbNorm r ρ + (weightedSupE r ((d : ℝ) + 3) ρ).toReal ≤ Λ := by
  obtain ⟨-, hmem, hsum⟩ := h
  have hcb0 : 0 ≤ cbNorm r ρ := by
    unfold cbNorm
    exact Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hws : weightedSupE r ((d : ℝ) + 3) ρ ≤ ENNReal.ofReal Λ := (le_add_self).trans hsum
  have hlt : weightedSupE r ((d : ℝ) + 3) ρ < ⊤ := lt_of_le_of_lt hws ENNReal.ofReal_lt_top
  refine ⟨hmem, hlt, ?_⟩
  have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hsum
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hlt.ne, ENNReal.toReal_ofReal hcb0,
    ENNReal.toReal_ofReal hΛ] at h1
  exact h1

lemma sa16t_mu_eq_flip (n : ℕ) (g : Euc d → ℝ) (x : Euc d) :
    sa16j_conv (sa16y_rho d n) g x = ∫ y, sa16y_rho d n (x - y) * g y := by
  unfold sa16j_conv
  rw [← integral_sub_left_eq_self (fun y => sa16y_rho d n (x - y) * g y) volume x]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sub_sub_cancel]

theorem sa16t_adjData (hd : 1 ≤ d) {s MB Λ ΛV G₀ νbar T : ℝ} (hs2 : s ≤ (d : ℝ) - 2) {m : ℕ} {D : WholeDyn d}
    {μ : ℝ → Euc d → ℝ} (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ) (n : ℕ) :
    AdjointRdData s m MB (sa16t_Lam1 d m Λ) ΛV G₀ νbar D T (sa16t_mu d n μ) := by
  have hdec := fun r (hr : r ∈ Icc (0 : ℝ) T) => sa16t_mu_decay hd hD.hμ hr
  have hA0 := sa16t_A0_nonneg d m Λ
  have hΛ1 : 0 ≤ sa16t_Lam1 d m Λ := by unfold sa16t_Lam1; positivity
  have hcont : ∀ r ∈ Icc (0 : ℝ) T, Continuous (μ r) := fun r hr =>
    ((hdec r hr).1).continuous
  have hbound : ∀ r ∈ Icc (0 : ℝ) T, ∀ j ≤ m + 3, ∀ x,
      ‖iteratedFDeriv ℝ j (sa16t_mu d n μ r) x‖ ≤
        (((d : ℝ) + 1) ^ (m + 3) * (2 ^ ((d : ℝ) + 3) * sa16t_A0 d m Λ)) * sa16p_w d x :=
    fun r hr j hj x => sa16t_conv_decay_unif (hdec r hr).1 (hdec r hr).2 n hj x
  have hregd : ∀ r ∈ Icc (0 : ℝ) T, IsRegularDensityW (m + 3) (sa16t_Lam1 d m Λ) (sa16t_mu d n μ r) := fun r hr =>
    sa16t_regular_of_decay (contDiff_infty.1 (sa16y_mollify_smooth n (hcont r hr)) (m + 3)) (hbound r hr)
  have hnonneg : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ sa16t_mu d n μ r x := fun r hr x =>
    integral_nonneg fun z => mul_nonneg (sa16y_rho_nonneg n z) ((hD.hμ.prob r hr).nonneg _)
  have hint1 : ∀ r ∈ Icc (0 : ℝ) T, Integrable (μ r) := fun r hr =>
    Integrable.of_integral_ne_zero (by rw [(hD.hμ.prob r hr).integral_one]; exact one_ne_zero)
  have hprob : ∀ r ∈ Icc (0 : ℝ) T, IsProbDensity (sa16t_mu d n μ r) := fun r hr => by
    refine ⟨hnonneg r hr, (sa16y_mollify_smooth n (hcont r hr)).continuous.measurable, ?_⟩
    have hconv : sa16t_mu d n μ r = fun x => (sa16y_rho d n ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] μ r) x := by
      funext x; exact sa16y_conv_eq_convolution _ _ x
    rw [hconv, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (sa16y_rho_integrable n) (hint1 r hr),
      sa16y_rho_int, (hD.hμ.prob r hr).integral_one]
    simp
  have hcn : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * sa16t_mu d n μ r x) (Icc (0 : ℝ) T) := by
    rintro ψ hψ ⟨B, hB⟩
    obtain ⟨Cρ, hCρ⟩ := (sa16y_rho_smooth (d := d) n).continuous.bounded_above_of_compact_support
      (sa16y_rho_compact n)
    refine continuousOn_of_dominated (bound := fun x => B * ((((d : ℝ) + 1) ^ (m + 3) *
      (2 ^ ((d : ℝ) + 3) * sa16t_A0 d m Λ)) * sa16p_w d x)) (fun r hr => ?_) (fun r hr => ?_) ?_ ?_
    · exact (hψ.mul (sa16y_mollify_smooth n (hcont r hr)).continuous).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [norm_mul]
      have h1 := hbound r hr 0 (Nat.zero_le _) x
      rw [norm_iteratedFDeriv_zero] at h1
      exact mul_le_mul (by simpa [Real.norm_eq_abs] using hB x) h1 (norm_nonneg _)
        ((abs_nonneg _).trans (hB 0))
    · exact (sa16p_w_integrable.const_mul _).const_mul _
    · refine Eventually.of_forall fun x => ?_
      have hc : ContinuousOn (fun r => ∫ y, sa16y_rho d n (x - y) * μ r y) (Icc (0 : ℝ) T) :=
        hD.hμ.cont (fun y => sa16y_rho d n (x - y))
          ((sa16y_rho_smooth n).continuous.comp (continuous_const.sub continuous_id))
          ⟨Cρ, fun y => by simpa [Real.norm_eq_abs] using hCρ (x - y)⟩
      refine continuousOn_const.mul (hc.congr fun r hr => ?_)
      exact sa16t_mu_eq_flip n (μ r) x
  exact ⟨hD.hs, hD.hM, hD.hV, ⟨hprob, ⟨fun r hr => sa16t_regMF_of_density hΛ1 (hregd r hr),
    fun h => absurd h (by linarith)⟩, hcn⟩, hD.hT, hD.hν⟩

end Mo2

end HRS.Whole.AppendixA.Phase2SA16R
