import HRS.MC.S7PIS1Path2
import HRS.MC.S7PIB3

/-!
# Packet piB, part 4: a bounded path with prescribed values `1_{u ≤ t_i} V^{t_i,u} b` at the observation times

Given `b ∈ E_m`, `u ∈ [0,T]` and finitely many times `t_i ∈ [0,T]`, the path `w(s) = θ(s) V^{max(s,u),u} b`, with a
continuous cut-off `θ` which vanishes at all `t_i < u` and equals `1` on `[u,T]`, satisfies `w(t_i) = V^{t_i,u} b`
for `t_i ≥ u`, `w(t_i) = 0` for `t_i < u` and `‖w‖ ≤ A ‖b‖`, `A` independent of `b,u,(t_i)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIB

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7.PIE HRS.MC.Sec7.S7PIDV HRS.MC.Sec7.S7PIS1

variable {d : ℕ}

theorem S7PIB_V_cont {J k : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (m : ℝ) (hk : 1 ≤ k) (hJ : k + 2 ≤ J) (hm0 : (k : ℝ) + 1 < m) (hm1 : m ≤ (k : ℝ) + 2)
    {u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) (b : NegSobolev d m) :
    Continuous fun s : Set.Icc (0 : ℝ) T => Vprop D μ m (max s.1 u) u b := by
  rw [continuous_iff_continuousAt]
  intro s₀
  have hmem : ∀ᶠ x in 𝓝 s₀, 0 ≤ u ∧ u ≤ max x.1 u ∧ max x.1 u ≤ T :=
    Filter.Eventually.of_forall fun x => ⟨hu, le_max_right _ _, max_le x.2.2 huT⟩
  have h₀ : 0 ≤ u ∧ u ≤ max s₀.1 u ∧ max s₀.1 u ≤ T := ⟨hu, le_max_right _ _, max_le s₀.2.2 huT⟩
  have ht : Tendsto (fun x : Set.Icc (0 : ℝ) T => max x.1 u) (𝓝 s₀) (𝓝 (max s₀.1 u)) :=
    ((continuous_subtype_val.max continuous_const) : Continuous fun x : Set.Icc (0 : ℝ) T => max x.1 u).tendsto s₀
  exact S7PIS1_V_tendsto H m k hk hJ hm0 hm1 (𝓝 s₀) (fun x => max x.1 u) (fun _ => u) (max s₀.1 u) u hmem h₀
    (fun j k' => S7PIS1_entries_tendsto H (𝓝 s₀) (fun x => max x.1 u) (fun _ => u) hmem h₀
      tendsto_const_nhds ht j k') b

/-- the cut-off vanishing at all earlier observation times -/
theorem S7PIB_cutoff {q : ℕ} (t : Fin q → ℝ) (u : ℝ) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ s, 0 ≤ θ s ∧ θ s ≤ 1) ∧ (∀ s, u ≤ s → θ s = 1) ∧
      ∀ i, t i < u → θ (t i) = 0 := by
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∀ i, t i < u → t i + δ ≤ u := by
    have h : ∀ i, ∀ᶠ δ in 𝓝[>] (0 : ℝ), t i < u → t i + δ ≤ u := by
      intro i
      by_cases hi : t i < u
      · have : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ≤ u - t i :=
          nhdsWithin_le_nhds (Iic_mem_nhds (by linarith : (0 : ℝ) < u - t i))
        filter_upwards [this] with δ hδ _ using by linarith
      · exact Filter.Eventually.of_forall fun δ h => absurd h hi
    obtain ⟨δ, hδ1, hδ2⟩ := ((Filter.eventually_all.2 h).and self_mem_nhdsWithin).exists
    exact ⟨δ, hδ2, hδ1⟩
  obtain ⟨δ, hδ0, hδ⟩ := hδ
  refine ⟨fun s => min 1 (max 0 ((s - (u - δ)) / δ)), by fun_prop, fun s => ⟨?_, min_le_left _ _⟩, fun s hs => ?_,
    fun i hi => ?_⟩
  · exact le_min zero_le_one (le_max_left _ _)
  · refine min_eq_left (le_max_of_le_right ?_)
    rw [le_div_iff₀ hδ0]
    linarith
  · have : (t i - (u - δ)) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith [hδ i hi]) hδ0.le
    simp [max_eq_left this]

theorem S7PIB_path_exists (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (b : NegSobolev d m) (u : ℝ), u ∈ Set.Icc (0 : ℝ) T → ∀ {q : ℕ} (t : Fin q → ℝ),
      ∃ w : PathSpace d m T, ‖w‖ ≤ A * ‖b‖ ∧ ∀ i, t i ∈ Set.Icc (0 : ℝ) T →
        pathAt w (t i) = if u ≤ t i then Vprop R.D R.ρ m (t i) u b else 0 := by
  obtain ⟨J, k, hk1, hkJ, hm0, hm1, H⟩ := S7PIS1_data R m hm T hT
  obtain ⟨A, hA1, hAb⟩ := S7PIDV_finBd_unif H m (k + 1) (by omega) (by omega)
    (by push_cast; linarith) (by push_cast; linarith)
  have hA : 0 ≤ A := by linarith
  refine ⟨A, hA, fun b u hu q t => ?_⟩
  obtain ⟨θ, hθc, hθb, hθ1, hθ0⟩ := S7PIB_cutoff t u
  have hcont : Continuous fun s : Set.Icc (0 : ℝ) T => θ s.1 • Vprop R.D R.ρ m (max s.1 u) u b :=
    (hθc.comp continuous_subtype_val).smul (S7PIB_V_cont H m hk1 hkJ hm0 hm1 hu.1 hu.2 b)
  let w : PathSpace d m T :=
    (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from ⟨_, hcont⟩)
  refine ⟨w, ?_, fun i hi => ?_⟩
  · show ‖(show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from ⟨_, hcont⟩)‖ ≤ A * ‖b‖
    refine (ContinuousMap.norm_le _ (mul_nonneg hA (norm_nonneg _))).2 fun s => ?_
    show ‖θ s.1 • Vprop R.D R.ρ m (max s.1 u) u b‖ ≤ A * ‖b‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hθb s.1).1]
    have hV := pie_Vbound_of_finBd R.D R.ρ m (max s.1 u) u hA
      (hAb u (max s.1 u) hu.1 (le_max_right _ _) (max_le s.2.2 hu.2)) b
    calc θ s.1 * ‖Vprop R.D R.ρ m (max s.1 u) u b‖ ≤ 1 * (A * ‖b‖) :=
          mul_le_mul (hθb s.1).2 hV (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · have : pathAt w (t i) = θ (t i) • Vprop R.D R.ρ m (max (t i) u) u b := by
      unfold pathAt
      rw [dif_pos hi]
      rfl
    rw [this]
    by_cases h : u ≤ t i
    · rw [if_pos h, hθ1 _ h, one_smul, max_eq_left h]
    · rw [if_neg h, hθ0 i (not_le.1 h), zero_smul]

end HRS.MC.Sec7.S7PIB

end
