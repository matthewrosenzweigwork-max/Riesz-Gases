import HRS.MS.S111X2Aux44
import HRS.MS.S111X2Aux40

/-!
# S11.1 X2, packet H02 (part 7): the quadratic bound for the response Gram matrix of the orbit
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111X2

open HRS HRS.Whole HRS.MS.R2Interp
open HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_node_val {T : ℝ} (hT : 0 < T) (L i : ℕ) (hi : i ≤ 2 ^ L) :
    ((s102_node hT L i : Set.Icc (0 : ℝ) T) : ℝ) = i * T / 2 ^ L := by
  have h2 : (0 : ℝ) < 2 ^ L := by positivity
  have hi' : (i : ℝ) ≤ 2 ^ L := by exact_mod_cast hi
  unfold s102_node
  rw [Set.projIcc_of_mem _ ⟨by positivity, by rw [div_le_iff₀ h2]; nlinarith⟩]

theorem s111x2_gram_bound {g : Euc d → ℝ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {Mg : ℝ} (hK : KRep g μ K Mg) {θ Γ : ℝ} (hθ : 0 ≤ θ) (hθΓ : θ ≤ Γ)
    {T : ℝ} (hT : 0 < T) (L : ℕ) (U : ℝ → MultiIndex d → Euc d → ℝ)
    (hU : ∀ τ, 0 ≤ τ → ∀ α, MemLp (U τ α) 2 μ) {u κ B : ℝ} (hu : 0 ≤ u) (hB : 0 ≤ B)
    (h1 : ∀ (S : Finset (MultiIndex d)) (τ₁ : ℝ), 0 ≤ τ₁ →
      ∑ α ∈ S, s111x2_centeredSquare μ (U τ₁ α) ≤ B * Real.exp (-2 * κ * τ₁))
    (h2 : ∀ (S : Finset (MultiIndex d)) (τ₁ τ₂ : ℝ), 0 ≤ τ₁ → τ₁ ≤ τ₂ →
      ∑ α ∈ S, s111x2_centeredSquare μ (fun x => U τ₂ α x - U τ₁ α x) ≤
        B * (τ₂ - τ₁) ^ 2 * Real.exp (-2 * κ * τ₁))
    (hκ : 0 ≤ κ) (M : OscPath d (wholeSpaceIndex d : ℝ) T [×2]→L[ℝ] ℝ) (hM : ‖M‖ ≤ 1) :
    |∑ p ∈ s102_idx d L, ∑ q ∈ s102_idx d L,
        HRS.Whole.susceptibilityCov g μ θ
          (U (u + ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ)) p.2)
          (U (u + ((s102_node hT L q.1 : Set.Icc (0 : ℝ) T) : ℝ)) q.2) *
        M ![s102_bpath (m := (wholeSpaceIndex d : ℝ)) T L p, s102_bpath (m := (wholeSpaceIndex d : ℝ)) T L q]| ≤
      (2 * B + 2 * B * T ^ 2) * Real.exp (-2 * κ * u) := by
  classical
  have hRF := s111x2_responseForm hK hθ hθΓ
  set A := (multiIndex_sublevel_finite d L).toFinset with hA
  have hid : s102_idx d L = (Finset.range (2 ^ L + 1)) ×ˢ A := rfl
  set F : ℕ × MultiIndex d → Euc d → ℝ := fun p =>
    U (u + ((s102_node hT L p.1 : Set.Icc (0 : ℝ) T) : ℝ)) p.2 with hF
  have hnode0 : ∀ i, 0 ≤ ((s102_node hT L i : Set.Icc (0 : ℝ) T) : ℝ) := fun i => (s102_node hT L i).2.1
  have hFm : ∀ p, MemLp (F p) 2 μ := fun p => hU _ (by linarith [hnode0 p.1]) _
  set Kk : ℕ × MultiIndex d → ℕ × MultiIndex d → ℝ := fun p q =>
    HRS.Whole.susceptibilityCov g μ θ (F p) (F q) with hKk
  have hsymm : ∀ p ∈ s102_idx d L, ∀ q ∈ s102_idx d L, Kk p q = Kk q p := fun p _ q _ =>
    hRF.symmetry _ _ (hFm p) (hFm q)
  have hpsd : ∀ c : ℕ × MultiIndex d → ℝ, 0 ≤ ∑ p ∈ s102_idx d L, ∑ q ∈ s102_idx d L, c p * c q * Kk p q :=
    fun c => s111x2_gram_psd_fin hK hθ (s102_idx d L) F hFm c
  have hQ := s111x2_quad_bound hT L A M hM Kk (by simpa [hid] using hsymm) (by simpa [hid] using hpsd)
  rw [hid]
  refine hQ.trans ?_
  set N : ℕ := 2 ^ L with hN
  have hN0 : (0 : ℝ) < N := by positivity
  have hexp := Real.exp_pos (-2 * κ * u)
  -- first term
  have t1 : ∑ α ∈ A, Kk (0, α) (0, α) ≤ B * Real.exp (-2 * κ * u) := by
    refine le_trans (Finset.sum_le_sum fun α _ => ?_) (h1 A u hu)
    have hn0 : ((s102_node hT L 0 : Set.Icc (0 : ℝ) T) : ℝ) = 0 := by
      rw [s111x2_node_val hT L 0 (Nat.zero_le _)]; simp
    simp only [hKk, hF, hn0, add_zero]
    exact (hRF.coercive _ (hU u hu α)).2
  -- increments
  have t2 : ∀ j ∈ Finset.range N, ∑ α ∈ A, (Kk (j + 1, α) (j + 1, α) - 2 * Kk (j, α) (j + 1, α) +
      Kk (j, α) (j, α)) ≤ B * (T / N) ^ 2 * Real.exp (-2 * κ * u) := by
    intro j hj
    have hj1 : j + 1 ≤ N := Finset.mem_range.1 hj
    have hj0 : j ≤ N := by omega
    have hv1 := s111x2_node_val hT L (j + 1) hj1
    have hv0 := s111x2_node_val hT L j hj0
    have hdiff : ((s102_node hT L (j + 1) : Set.Icc (0 : ℝ) T) : ℝ) -
        ((s102_node hT L j : Set.Icc (0 : ℝ) T) : ℝ) = T / N := by
      have hNc : (N : ℝ) = 2 ^ L := by simp [hN]
      rw [hv1, hv0, hNc]; push_cast; field_simp; ring
    have hτ1 : 0 ≤ u + ((s102_node hT L j : Set.Icc (0 : ℝ) T) : ℝ) := by linarith [hnode0 j]
    have hle : u + ((s102_node hT L j : Set.Icc (0 : ℝ) T) : ℝ) ≤
        u + ((s102_node hT L (j + 1) : Set.Icc (0 : ℝ) T) : ℝ) := by
      have : (0 : ℝ) ≤ T / N := by positivity
      linarith
    refine le_trans (Finset.sum_le_sum fun α _ => ?_) ((h2 A _ _ hτ1 hle).trans ?_)
    · have e : Kk (j + 1, α) (j + 1, α) - 2 * Kk (j, α) (j + 1, α) + Kk (j, α) (j, α) =
          HRS.Whole.susceptibilityCov g μ θ (fun x => F (j + 1, α) x - F (j, α) x)
            (fun x => F (j + 1, α) x - F (j, α) x) := by
        rw [s111x2_susc_sub hK hθ (hFm _) (hFm _)]
        simp only [hKk]
        rw [hRF.symmetry _ _ (hFm (j, α)) (hFm (j + 1, α))]
        ring
      rw [e]
      have hmd : MemLp (fun x => F (j + 1, α) x - F (j, α) x) 2 μ := (hFm _).sub (hFm _)
      exact (hRF.coercive _ hmd).2
    · have hsq : (u + ((s102_node hT L (j + 1) : Set.Icc (0 : ℝ) T) : ℝ) -
          (u + ((s102_node hT L j : Set.Icc (0 : ℝ) T) : ℝ))) = T / N := by linarith
      rw [hsq]
      have hexp' : Real.exp (-2 * κ * (u + ((s102_node hT L j : Set.Icc (0 : ℝ) T) : ℝ))) ≤
          Real.exp (-2 * κ * u) := by
        apply Real.exp_le_exp.2
        nlinarith [hnode0 j]
      exact mul_le_mul_of_nonneg_left hexp' (by positivity)
  have t2' : ∑ j ∈ Finset.range N, ∑ α ∈ A, (Kk (j + 1, α) (j + 1, α) - 2 * Kk (j, α) (j + 1, α) +
      Kk (j, α) (j, α)) ≤ N * (B * (T / N) ^ 2 * Real.exp (-2 * κ * u)) := by
    refine (Finset.sum_le_sum t2).trans ?_
    simp
  have : (2 * N : ℝ) * (N * (B * (T / N) ^ 2 * Real.exp (-2 * κ * u))) = 2 * B * T ^ 2 * Real.exp (-2 * κ * u) := by
    field_simp
  calc 2 * ∑ α ∈ A, Kk (0, α) (0, α) + 2 * (N : ℝ) * ∑ j ∈ Finset.range N, ∑ α ∈ A,
        (Kk (j + 1, α) (j + 1, α) - 2 * Kk (j, α) (j + 1, α) + Kk (j, α) (j, α))
      ≤ 2 * (B * Real.exp (-2 * κ * u)) + 2 * (N : ℝ) * (N * (B * (T / N) ^ 2 * Real.exp (-2 * κ * u))) := by
        gcongr
    _ = (2 * B + 2 * B * T ^ 2) * Real.exp (-2 * κ * u) := by
        have h' : 2 * (N : ℝ) * (N * (B * (T / N) ^ 2 * Real.exp (-2 * κ * u))) =
            2 * B * T ^ 2 * Real.exp (-2 * κ * u) := by
          rw [← this]
        rw [h']; ring

end HRS.MS.S111X2
