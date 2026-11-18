import HRS.MS.SA12X3C7B5

/-!
# S.A.12 C7 (SA12X3), part C1 (7C): a box cutoff for the periodic kernel

For `0 < h` and `a < L` there is a smooth compactly supported `ρ` with `ρ = 1` on `{‖u‖ ≥ h/2, |u_i| ≤ a}` whose
support lies in the open set `{‖u‖ > h/8, |u_i| < L}` (which avoids all lattice points `L k`); consequently
`ρ γ` is smooth for a periodic Riesz kernel `γ` (smooth off the lattice).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- The open set `{‖u‖ > h/8, |u_i| < L}`. -/
def sa12x3_Om (d : ℕ) (L h : ℝ) : Set (Euc d) := {u | h / 8 < ‖u‖ ∧ ∀ i, |u i| < L}

theorem sa12x3_Om_open (L h : ℝ) : IsOpen (sa12x3_Om d L h) := by
  refine IsOpen.inter (isOpen_lt continuous_const continuous_norm) ?_
  have : {u : Euc d | ∀ i, |u i| < L} = ⋂ i, {u : Euc d | |u i| < L} := by ext u; simp
  show IsOpen {u : Euc d | ∀ i, |u i| < L}
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt (continuous_abs.comp (EuclideanSpace.proj i).continuous) continuous_const

theorem sa12x3_Om_nonlattice {L h : ℝ} (hh : 0 < h) {u : Euc d} (hu : u ∈ sa12x3_Om d L h) :
    ∀ z : Fin d → ℤ, u ≠ L • latticePt z := by
  intro z hz
  by_cases hz0 : z = 0
  · have : u = 0 := by rw [hz, hz0]; ext i; simp [latticePt]
    have := hu.1
    rw [‹u = 0›] at this
    simp at this
    linarith
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hz0 (funext hcon)
    have h1 := hu.2 i
    rw [hz] at h1
    have hL : 0 < L := by
      have := (abs_nonneg (u i)).trans_lt (hu.2 i)
      exact this
    simp [latticePt, abs_mul, abs_of_pos hL] at h1
    have : (1 : ℝ) ≤ |(z i : ℝ)| := by
      have : (1 : ℤ) ≤ |z i| := Int.one_le_abs hi
      exact_mod_cast this
    nlinarith

theorem sa12x3_box_cutoff {L h a : ℝ} (hh : 0 < h) (haL : a < L) (ha0 : 0 < a) :
    ∃ ρ : Euc d → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      (∀ u : Euc d, h / 2 ≤ ‖u‖ → (∀ i, |u i| ≤ a) → ρ u = 1) ∧ tsupport ρ ⊆ sa12x3_Om d L h := by
  let β : ContDiffBump (0 : ℝ) := ⟨a, (a + L) / 2, ha0, by linarith⟩
  let b : ContDiffBump (0 : Euc d) := ⟨h / 4, h / 2, by linarith, by linarith⟩
  have hβ : ContDiff ℝ ∞ (⇑β) := β.contDiff
  have hb : ContDiff ℝ ∞ (⇑b) := b.contDiff
  set ρb : Euc d → ℝ := fun u => ∏ i : Fin d, β (u i) with hρb
  set ρ : Euc d → ℝ := fun u => ρb u * (1 - b u) with hρ
  have hρb_cd : ContDiff ℝ ∞ ρb :=
    contDiff_prod fun i _ => hβ.comp (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have hρ_cd : ContDiff ℝ ∞ ρ := hρb_cd.mul (contDiff_const.sub hb)
  -- the support of ρ
  have hsupp : ∀ u, ρ u ≠ 0 → h / 4 < ‖u‖ ∧ ∀ i, |u i| < (a + L) / 2 := by
    intro u hu
    have h1 : ρb u ≠ 0 := left_ne_zero_of_mul hu
    have h2 : 1 - b u ≠ 0 := right_ne_zero_of_mul hu
    refine ⟨?_, fun i => ?_⟩
    · by_contra hcon
      push_neg at hcon
      have : b u = 1 := b.one_of_mem_closedBall (by simpa [b] using hcon)
      exact h2 (by rw [this]; ring)
    · by_contra hcon
      push_neg at hcon
      have : β (u i) = 0 := β.zero_of_le_dist (by
        have : dist (u i) 0 = |u i| := by simp [Real.dist_eq]
        rw [this]; exact hcon)
      exact h1 (Finset.prod_eq_zero (Finset.mem_univ i) this)
  have hclosed : IsClosed {u : Euc d | h / 4 ≤ ‖u‖ ∧ ∀ i, |u i| ≤ (a + L) / 2} := by
    refine IsClosed.inter (isClosed_le continuous_const continuous_norm) ?_
    have : {u : Euc d | ∀ i, |u i| ≤ (a + L) / 2} = ⋂ i, {u : Euc d | |u i| ≤ (a + L) / 2} := by ext u; simp
    show IsClosed {u : Euc d | ∀ i, |u i| ≤ (a + L) / 2}
    rw [this]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_abs.comp (EuclideanSpace.proj i).continuous) continuous_const
  have hts : tsupport ρ ⊆ {u : Euc d | h / 4 ≤ ‖u‖ ∧ ∀ i, |u i| ≤ (a + L) / 2} := by
    refine closure_minimal (fun u hu => ?_) hclosed
    obtain ⟨h1, h2⟩ := hsupp u hu
    exact ⟨h1.le, fun i => (h2 i).le⟩
  refine ⟨ρ, hρ_cd, ?_, ?_, ?_⟩
  · -- compact support
    refine HasCompactSupport.of_support_subset_isCompact (K := closedBall (0 : Euc d) (Real.sqrt (d * ((a + L) / 2) ^ 2)))
      (isCompact_closedBall _ _) fun u hu => ?_
    obtain ⟨-, h2⟩ := hsupp u hu
    rw [mem_closedBall_zero_iff, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt ?_
    calc ∑ i, ‖u i‖ ^ 2 ≤ ∑ _i : Fin d, ((a + L) / 2) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := h2 i
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (u i)]
      _ = d * ((a + L) / 2) ^ 2 := by simp
  · intro u hu1 hu2
    have e1 : ρb u = 1 := Finset.prod_eq_one fun i _ => β.one_of_mem_closedBall (by
      simp [β, Real.dist_eq, hu2 i])
    have e2 : b u = 0 := b.zero_of_le_dist (by simpa [b, dist_zero_right] using hu1)
    simp [hρ, e1, e2]
  · intro u hu
    obtain ⟨h1, h2⟩ := hts hu
    exact ⟨by linarith, fun i => by have := h2 i; linarith⟩

theorem sa12x3_cutoff_smooth {s L h : ℝ} {γ : Euc d → ℝ} (hh : 0 < h)
    (hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ) {ρ : Euc d → ℝ} (hρ : ContDiff ℝ ∞ ρ)
    (hts : tsupport ρ ⊆ sa12x3_Om d L h) : ContDiff ℝ ∞ (fun u => ρ u * γ u) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : u ∈ tsupport ρ
  · have hΩ : sa12x3_Om d L h ⊆ {x : Euc d | ∀ z : Fin d → ℤ, x ≠ L • latticePt z} :=
      fun x hx => sa12x3_Om_nonlattice hh hx
    have hat : ContDiffAt ℝ ∞ γ u :=
      (hγ.smooth.mono hΩ).contDiffAt ((sa12x3_Om_open L h).mem_nhds (hts hu))
    exact hρ.contDiffAt.mul hat
  · have : ρ =ᶠ[𝓝 u] 0 := notMem_tsupport_iff_eventuallyEq.1 hu
    have h2 : (fun u => ρ u * γ u) =ᶠ[𝓝 u] fun _ => 0 := by
      filter_upwards [this] with v hv
      simp [hv]
    exact (contDiffAt_const).congr_of_eventuallyEq h2

end HRS.MH.AdjointRd.Phase2SA12Near
