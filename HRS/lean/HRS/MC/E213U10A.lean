import HRS.MC.E213Defs
import HRS.MC.E213U1a
import HRS.MC.E213U1b
import HRS.MC.E213U2
import HRS.MC.E213U5a
import HRS.MC.E213U5b
import HRS.MC.E213U6
import HRS.MC.E213U7b

/-!
# Packet e213u10 (Theorem 2.13, Wave 4): `near_estimate`.  Part A: window infrastructure.

## Outline of the proof of `near_estimate` (implemented in `E213U10A`-`E213U10E`)

Fix `Rw > 0`, `N ≥ 2`, `a ≥ 0`, `Φ` in the unit ball, `b = max (a-Rw) 0`, `L = Rw+T` (so `a+T ≤ b+L`, `a-b ≤ Rw`).

1. *Pair space.*  `Bsp = 𝒳_{r,L} × L²([0,L];E_r)` (level `r = rLvl d`); the particle pair `pairN r L b` and the Gaussian pair
   `pairLim r L b` live there; `chaos_conv` (`p = 2`, window `Rw+T`) gives `⨆_a W₂ → 0` for them and for `η_N`, `η`.
2. *Window functionals* (part B).  `liftW : 𝒳_{r,L} →L 𝒳_{m,a+T}` (`w ↦ embed (w (max (· - b) 0))`), the near coefficient
   `bqf Bq = 1_{[b,b+L]} Bq(· - b)` of an `L²` element, `zrf w = w (max (· - b) 0)`.  On the uniform partition `u_i = iH/n`
   (`H = a+T`) with clamped tags `τ_i = min (max u_i b) u_{i+1}` put
   `GD n (w,Bq) = ∑_i DU_{τ_i}(winPred (liftW w) τ_i)[winDrift (near (bqf Bq)) u_i u_{i+1}]`,
   `GJ n w = ∑_i ⟨D²U_{τ_i}(winPred (liftW w) τ_i), winJ (near (zrf w)) (u_i,u_{i+1}]⟩`.
   These are continuous (Lipschitz) on `Bsp`, with the explicit bounds
   `|GD n x - GD n x'| ≤ c₁ ‖x.1-x'.1‖ ‖x.2‖ + c₂ ‖x.2-x'.2‖`, `|GD n x| ≤ c₂ ‖x.2‖`,
   `|GJ n w - GJ n w'| ≤ c₃ ‖w-w'‖ (1+‖w'‖)`, `|GJ n w| ≤ c₃ ‖w‖` from `winDrift_near`, `winDrift_add`, `winJ_near`, `winJ_add`,
   `Ucan_regular` (`‖D^jU‖ ≤ 1`), `‖winPred w τ‖ ≤ C_Y ‖w‖` (`vprop_stable_of_prepared`).
3. *Localisation* (part C).  A.s. (particles: `PreparedRealization`, `N ≥ 2`; Gaussian: `gd.limit`, `gd.B_L2`) the actual Riemann sums of
   `rsA`, `rsJ` for the near coefficients (partition `u_i`, tags `τ_i`) equal `GD n (pair ω)`, resp. `GJ n (ζ-window ω) + E_n(ω)` with
   `|E_n| ≤ C ‖m_N‖` (`η_N = ζ_N + m_N`, `S7UCD.s7_UC_D5_mean_window_proof`, `winJ_add`, `winJ_near`), because `winPred w τ`
   depends only on `w|[b,a+T]` for `τ ≥ b` and `winDrift`, `winJ` depend on the coefficient only a.e. / on the interval.  The Riemann sums
   converge to `rsA`, `rsJ` by `IsRS` (`rs_split_*`, resp. `e213u7_drift_exists`) and `rsLim_eq`.
4. *Coupling* (part D).  For a coupling `π` of the two pair laws of cost `≤ W₂ + ε`: `∫ GD n dlaw₁ - ∫ GD n dlaw₂ = ∫ (GD n x - GD n x') dπ`
   is bounded by Cauchy--Schwarz using `E‖pairN.2‖² ≤ C` (`fcf5_F6c_B_moments`), `E‖zetaWin‖² ≤ C` (`fcf5_E3b_F5_zeta_moments`);
   let `n → ∞` (dominated convergence on both sides) and `ε → 0`.  `‖m_N‖ ≤ W₂(η_N,η)`.
5. *Assembly* (part E).  `e N = W₂^{pair}_N + W₂^{η}_N` (`toReal`) for `N ≥ N₀`; for `N < N₀` a crude bound from the particle moments and the
   Gaussian moment bound transferred from `N₀` by the coupling.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

/-! ### Clamp and lift -/

/-- The clamp `t ↦ max (t - b) 0` as a continuous map `[0,H] → [0,L]` (needs `H ≤ b + L`). -/
def u10_clamp (b L H : ℝ) (hL : 0 ≤ L) (hH : H ≤ b + L) : C(Set.Icc (0 : ℝ) H, Set.Icc (0 : ℝ) L) :=
  ⟨fun t => ⟨max (t.1 - b) 0, le_max_right _ _, max_le (by linarith [t.2.2]) hL⟩, by
    exact Continuous.subtype_mk (by fun_prop) _⟩

theorem u10_clamp_val (b L H : ℝ) (hL : 0 ≤ L) (hH : H ≤ b + L) (t : Set.Icc (0 : ℝ) H) :
    ((u10_clamp b L H hL hH t : Set.Icc (0 : ℝ) L) : ℝ) = max (t.1 - b) 0 := rfl

/-- The lift of a window path `w ∈ 𝒳_{r,L}` to `𝒳_{m,H}`: `t ↦ embed (w (max (t-b) 0))`. -/
def u10_liftLM (hE : EdgeworthHyp S β₀ m) (b L H : ℝ) (hL : 0 ≤ L) (hH : H ≤ b + L) :
    PathSpace d (rLvl d) L →ₗ[ℝ] PathSpace d m H where
  toFun w := (show C(Set.Icc (0 : ℝ) L, NegSobolev d m) from HRS.MD.EQInterp.epath (rLvl_le hE) L w).comp
    (u10_clamp b L H hL hH)
  map_add' w w' := by
    apply ContinuousMap.ext; intro t
    simp [map_add]
    rfl
  map_smul' c w := by
    apply ContinuousMap.ext; intro t
    simp [map_smul]
    rfl

theorem u10_liftLM_at' (hE : EdgeworthHyp S β₀ m) (b L H : ℝ) (hL : 0 ≤ L) (hH : H ≤ b + L)
    (w : PathSpace d (rLvl d) L) (t : Set.Icc (0 : ℝ) H) :
    (u10_liftLM hE b L H hL hH w).at' t = NegSobolev.embed m (w.at' (u10_clamp b L H hL hH t)) := rfl

/-- The lift as a continuous linear map (norm `≤ 1`). -/
def u10_liftW (hE : EdgeworthHyp S β₀ m) (b L H : ℝ) (hL : 0 ≤ L) (hH : H ≤ b + L) :
    PathSpace d (rLvl d) L →L[ℝ] PathSpace d m H :=
  LinearMap.mkContinuous (u10_liftLM hE b L H hL hH) 1 (fun w => by
    rw [one_mul]
    refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 (fun t => ?_)
    show ‖(u10_liftLM hE b L H hL hH w).at' t‖ ≤ ‖w‖
    rw [u10_liftLM_at']
    exact (NegSobolev.norm_embed_le m (rLvl_le hE) _).trans
      (ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) L, NegSobolev d (rLvl d)) from w) _))

theorem u10_liftW_apply (hE : EdgeworthHyp S β₀ m) (b L H : ℝ) (hL : 0 ≤ L) (hH : H ≤ b + L)
    (w : PathSpace d (rLvl d) L) : u10_liftW hE b L H hL hH w = u10_liftLM hE b L H hL hH w := rfl

theorem u10_liftW_norm_le (hE : EdgeworthHyp S β₀ m) (b L H : ℝ) (hL : 0 ≤ L) (hH : H ≤ b + L) :
    ‖u10_liftW hE b L H hL hH‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _


/-! ### Path evaluation helpers -/

theorem u10_pathAt_eq {T : ℝ} (w : PathSpace d m T) (t : Set.Icc (0 : ℝ) T) : pathAt w t = w.at' t := by
  unfold pathAt
  rw [dif_pos t.2]

theorem u10_path_ext {T : ℝ} {v w : PathSpace d m T}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, pathAt v t = pathAt w t) : v = w :=
  e213o_ext fun t => by rw [← u10_pathAt_eq, ← u10_pathAt_eq]; exact h t.1 t.2

theorem u10_pathAt_norm_le {T : ℝ} (w : PathSpace d m T) (t : ℝ) : ‖pathAt w t‖ ≤ ‖w‖ := by
  unfold pathAt
  by_cases h : t ∈ Set.Icc (0 : ℝ) T
  · rw [dif_pos h]
    exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w) ⟨t, h⟩
  · rw [dif_neg h]; simp

theorem u10_pathAt_sub {T : ℝ} (w₁ w₂ : PathSpace d m T) (t : ℝ) :
    pathAt (w₁ - w₂) t = pathAt w₁ t - pathAt w₂ t := by
  unfold pathAt
  by_cases h : t ∈ Set.Icc (0 : ℝ) T
  · rw [dif_pos h, dif_pos h, dif_pos h]; rfl
  · rw [dif_neg h, dif_neg h, dif_neg h]; simp

/-! ### The predicted window: linearity, bound, locality -/

section WinPred

variable (hE : EdgeworthHyp S β₀ m)

theorem u10_vprop_sub {u t : ℝ} (hu : 0 ≤ u) (hut : u ≤ t) (F G : NegSobolev d m) :
    Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u (F - G) =
      Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u F - Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m t u G := by
  obtain ⟨C, c, hC, hc, Vev, hsp⟩ := HRS.MC.E213U1.u1_vev hE
  rw [hsp.2.1 u t hu hut, hsp.2.1 u t hu hut, hsp.2.1 u t hu hut, map_sub]

theorem u10_winPred_pathAt (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (w : PathSpace d m (a + T)) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    pathAt (winPred (regime S β₀ hE) m T a ha w τ) t =
      if a + t ≤ τ then pathAt w (a + t)
      else Vprop (regime S β₀ hE).D (regime S β₀ hE).ρ m (a + t) τ (pathAt w τ) := by
  have hH : 0 < a + T := by linarith
  unfold winPred
  rw [winRestr_pathAt a ha _ ht]
  exact (HRS.MC.Sec7.S7PIS1.s7_PIS_path_facts_proof (regime S β₀ hE) m hE.m_gt (a + T) hH).1 w τ (a + t) hτ
    ⟨by linarith [ht.1], by linarith [ht.2]⟩

theorem u10_winPred_sub (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (w₁ w₂ : PathSpace d m (a + T)) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) :
    winPred (regime S β₀ hE) m T a ha (w₁ - w₂) τ =
      winPred (regime S β₀ hE) m T a ha w₁ τ - winPred (regime S β₀ hE) m T a ha w₂ τ := by
  apply u10_path_ext
  intro t ht
  rw [u10_pathAt_sub, u10_winPred_pathAt hE T hT a ha _ hτ ht, u10_winPred_pathAt hE T hT a ha _ hτ ht,
    u10_winPred_pathAt hE T hT a ha _ hτ ht]
  split_ifs with h
  · rw [u10_pathAt_sub]
  · rw [u10_pathAt_sub, u10_vprop_sub hE hτ.1 (not_le.1 h).le]

theorem u10_winPred_norm_le (T : ℝ) (hT : 0 < T) :
    ∃ CY : ℝ, 1 ≤ CY ∧ ∀ (a : ℝ) (ha : 0 ≤ a) (w : PathSpace d m (a + T)) (τ : ℝ),
      τ ∈ Set.Icc (0 : ℝ) (a + T) → ‖winPred (regime S β₀ hE) m T a ha w τ‖ ≤ CY * ‖w‖ := by
  obtain ⟨C, c, hC, hc, hV⟩ := HRS.MC.E213D.vprop_stable_of_prepared S β₀ hE m
  refine ⟨max 1 C, le_max_left _ _, fun a ha w τ hτ => ?_⟩
  refine (ContinuousMap.norm_le _ (by positivity)).2 (fun t => ?_)
  show ‖(winPred (regime S β₀ hE) m T a ha w τ).at' t‖ ≤ _
  rw [← u10_pathAt_eq, u10_winPred_pathAt hE T hT a ha w hτ t.2]
  split_ifs with h
  · exact (u10_pathAt_norm_le w _).trans (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
  · have hlt : τ ≤ a + (t : ℝ) := (not_le.1 h).le
    refine (hV τ (a + t) hτ.1 hlt _).trans ?_
    have h1 : Real.exp (-c * (a + t - τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    calc C * Real.exp (-c * (a + t - τ)) * ‖pathAt w τ‖ ≤ C * 1 * ‖w‖ := by
          gcongr
          exact u10_pathAt_norm_le w τ
      _ ≤ max 1 C * ‖w‖ := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

/-- Locality: for `τ ≥ b` the predicted window depends only on the path on `[b, a+T]` (for `b ≤ a`). -/
theorem u10_winPred_congr (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (b : ℝ) (hba : b ≤ a)
    (w₁ w₂ : PathSpace d m (a + T)) (h : ∀ t ∈ Set.Icc b (a + T), pathAt w₁ t = pathAt w₂ t) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) (a + T)) (hbτ : b ≤ τ) :
    winPred (regime S β₀ hE) m T a ha w₁ τ = winPred (regime S β₀ hE) m T a ha w₂ τ := by
  apply u10_path_ext
  intro t ht
  rw [u10_winPred_pathAt hE T hT a ha _ hτ ht, u10_winPred_pathAt hE T hT a ha _ hτ ht]
  have h1 : a + t ∈ Set.Icc b (a + T) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h2 : τ ∈ Set.Icc b (a + T) := ⟨hbτ, hτ.2⟩
  rw [h _ h1, h _ h2]

end WinPred

end HRS.MC.E213U10

end
