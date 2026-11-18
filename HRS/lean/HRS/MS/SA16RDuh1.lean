import HRS.MS.SA16RHeat16
import HRS.MS.SA16RVol7

/-!
# S.A.16 (SA16R) Duh1: the mild (Duhamel) solution at fixed viscosity

For `ν > 0`, a bounded strongly continuous family `K r : WmpSpace d (k+1) p →L WmpSpace d k p` and `φ ∈ WmpSpace d (k+1) p`,
`sa16r_fixedn_mild`: there is a unique `u ∈ C([0,T]; WmpSpace d (k+1) p)` with
`u τ = e^{ντΔ} φ + ∫_0^τ Γ_{ν s} K (τ-s) u (τ-s) ds` (the Duhamel formula for `∂_τ u = νΔu + K u`, `u(0) = φ`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Duh1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- time-parametrized gain operator `Γ_{ν s}` -/
def sa16r_GamT (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (ν s : ℝ) : WmpSpace d k p →L[ℝ] WmpSpace d (k + 1) p :=
  sa16r_Gam d k p (ν * s)

/-- the free term `e^{ντΔ} φ` -/
def sa16r_f0 (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (ν : ℝ) (φ : WmpSpace d (k + 1) p) (τ : ℝ) :
    WmpSpace d (k + 1) p :=
  if 0 < τ then sa16r_H d k p (ν * τ) φ else φ

/-- the constant `C` with `‖Γ_{ν s}‖ ≤ C s^{-1/2}` on `(0,T]` -/
def sa16r_Cgam (d : ℕ) (ν T : ℝ) : ℝ :=
  Real.sqrt T + d * ((4 / 3 : ℝ) ^ ((d : ℝ) / 2) * ν ^ (-(1 / 2 : ℝ)))

lemma sa16r_Cgam_nonneg (d : ℕ) {ν : ℝ} (hν : 0 < ν) (T : ℝ) : 0 ≤ sa16r_Cgam d ν T := by
  unfold sa16r_Cgam
  have : 0 ≤ (4 / 3 : ℝ) ^ ((d : ℝ) / 2) * ν ^ (-(1 / 2 : ℝ)) := by positivity
  positivity

lemma sa16r_GamT_bound {ν T : ℝ} (hν : 0 < ν) (k : ℕ) {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    ‖sa16r_GamT d k p ν s‖ ≤ sa16r_Cgam d ν T * s ^ (-(1 / 2 : ℝ)) := by
  unfold sa16r_GamT
  refine (sa16r_Gam_norm (mul_pos hν hs) k).trans ?_
  unfold sa16r_cG sa16r_Cgam
  have h1 : (1 : ℝ) ≤ Real.sqrt T * s ^ (-(1 / 2 : ℝ)) := by
    have h2 : Real.sqrt s ≤ Real.sqrt T := Real.sqrt_le_sqrt hsT
    have h3 : Real.sqrt s * s ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]; norm_num
    calc (1 : ℝ) = Real.sqrt s * s ^ (-(1 / 2 : ℝ)) := h3.symm
      _ ≤ Real.sqrt T * s ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hs.le _)
  have h4 : (ν * s) ^ (-(1 / 2 : ℝ)) = ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) :=
    Real.mul_rpow hν.le hs.le
  rw [h4]
  have : (1 : ℝ) + d * (ν ^ (-(1 / 2 : ℝ)) * s ^ (-(1 / 2 : ℝ)) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2)) =
      1 + d * ((4 / 3 : ℝ) ^ ((d : ℝ) / 2) * ν ^ (-(1 / 2 : ℝ))) * s ^ (-(1 / 2 : ℝ)) := by ring
  rw [this]
  nlinarith [h1]

lemma sa16r_GamT_cont {ν T : ℝ} (hν : 0 < ν) (k : ℕ) (y : WmpSpace d k p) :
    ContinuousOn (fun s : ℝ => sa16r_GamT d k p ν s y) (Ioc 0 T) := by
  intro s0 hs0
  have h1 := sa16r_Gam_cont (p := p) k (mul_pos hν hs0.1) y
  have h2 : Tendsto (fun s : ℝ => ν * s) (𝓝[Ioc 0 T] s0) (𝓝 (ν * s0)) :=
    ((continuous_const.mul continuous_id).tendsto s0).mono_left nhdsWithin_le_nhds
  exact h1.comp h2

lemma sa16r_f0_cont {ν T : ℝ} (hν : 0 < ν) (k : ℕ) (φ : WmpSpace d (k + 1) p) :
    ContinuousOn (sa16r_f0 d k p ν φ) (Icc 0 T) := by
  intro τ0 hτ0
  rcases lt_or_eq_of_le hτ0.1 with hpos | hzero
  · -- τ0 > 0
    have hev : ∀ᶠ τ in 𝓝[Icc 0 T] τ0, sa16r_f0 d k p ν φ τ =
        sa16r_Gam d k p (ν * τ) (sa16r_iota d k p φ) := by
      have : ∀ᶠ τ in 𝓝 τ0, 0 < τ := lt_mem_nhds hpos
      filter_upwards [nhdsWithin_le_nhds this] with τ hτ
      simp [sa16r_f0, hτ, sa16r_H]
    refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hev (by simp [sa16r_f0, hpos, sa16r_H])
    have h1 := sa16r_Gam_cont (p := p) k (mul_pos hν hpos) (sa16r_iota d k p φ)
    have h2 : Tendsto (fun s : ℝ => ν * s) (𝓝[Icc 0 T] τ0) (𝓝 (ν * τ0)) :=
      ((continuous_const.mul continuous_id).tendsto τ0).mono_left nhdsWithin_le_nhds
    exact h1.comp h2
  · -- τ0 = 0
    subst hzero
    have hf0 : sa16r_f0 d k p ν φ 0 = φ := by simp [sa16r_f0]
    show Tendsto (sa16r_f0 d k p ν φ) (𝓝[Icc 0 T] 0) (𝓝 (sa16r_f0 d k p ν φ 0))
    have hU : Icc (0 : ℝ) T ⊆ {0} ∪ Ioi 0 := fun τ hτ => by
      rcases eq_or_lt_of_le hτ.1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr h
    refine Tendsto.mono_left ?_ (nhdsWithin_mono _ hU)
    rw [nhdsWithin_union]
    refine Tendsto.sup ?_ ?_
    · rw [nhdsWithin_singleton, tendsto_pure_left]
      intro s hs
      exact mem_of_mem_nhds hs
    · rw [hf0]
      have h1 := sa16r_H_tendsto (p := p) k φ
      have hc : Continuous (fun s : ℝ => ν * s) := by fun_prop
      have h2 : Tendsto (fun s : ℝ => ν * s) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          ((hc.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin] with s hs using mul_pos hν hs
      refine (h1.comp h2).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [sa16r_f0, show 0 < s from hs]

lemma sa16r_gainData {ν T B : ℝ} (hν : 0 < ν) (k : ℕ) (K : ℝ → WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ B)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) :
    GainData T (sa16r_Cgam d ν T) B (sa16r_GamT d k p ν) K :=
  ⟨fun s hs hsT => sa16r_GamT_bound hν k hs hsT, fun y => sa16r_GamT_cont hν k y, hKb, hKc⟩

/-- **The mild solution at fixed viscosity** (existence and uniqueness in `C([0,T]; WmpSpace d (k+1) p)`). -/
theorem sa16r_fixedn_mild {ν T B : ℝ} (hν : 0 < ν) (hT : 0 < T) (hB : 0 ≤ B) (k : ℕ)
    (K : ℝ → WmpSpace d (k + 1) p →L[ℝ] WmpSpace d k p)
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ B)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (k + 1) p) :
    ∃ u : ℝ → WmpSpace d (k + 1) p, ContinuousOn u (Icc 0 T) ∧
      (∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d k p ν φ τ +
        voltOp (gainKer (sa16r_GamT d k p ν) K) u τ) ∧
      ∀ v : ℝ → WmpSpace d (k + 1) p, ContinuousOn v (Icc 0 T) →
        (∀ τ ∈ Icc (0 : ℝ) T, v τ = sa16r_f0 d k p ν φ τ +
          voltOp (gainKer (sa16r_GamT d k p ν) K) v τ) → ∀ τ ∈ Icc (0 : ℝ) T, v τ = u τ :=
  sa16r_volt_exists_unique ((sa16r_gainData hν k K hKb hKc).voltKer (sa16r_Cgam_nonneg d hν T) hB) hT
    (sa16r_f0_cont hν k φ)

end Duh1

end HRS.Whole.AppendixA.Phase2SA16R
