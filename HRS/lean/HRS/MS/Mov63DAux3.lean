import HRS.MS.Mov63DAux2

/-!
# S6.3, packet N5 (part 3): the existence theorem for the mild solution (the contraction)

Namespace `HRS.MS.Mov63`, helper prefix `mnd_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not a manuscript row.
See `Mov63DAux1` for the plan and the statement check.

**`mov63_mild_existence`** (packet N5): for `H : Mov2dTh d s β q ρ` there is a rate `c > 0` (the `L²_0`-decay rate of `T`, `c = λ` of
`movlin_L2_decay`) such that for every real `m > d/2 + 3` there are `ε, C > 0` such that for every `x₀ ∈ Σ^m` with
`⟨√ρ₀, x₀⟩ = 0` and `‖x₀‖_{Σ^m} ≤ ε` there is `v : ℝ → Σ^m` with

* `v` continuous on `[0,∞)`, `v 0 = x₀`;
* mass: `⟨√ρ₀, v_t⟩ = 0` for `t ≥ 0`;
* LINEAR amplitude and decay: `‖v_t‖_{Σ^m} ≤ C ‖x₀‖ e^{-ct/2}` (`t ≥ 0`);
* the mild equation (Duhamel form at the level `Σ^{m-a}`, `a = movA d s`, with the scale-level flow `G = mov2d_G`, `T(t) = G(t)` on
  `L²_0`): for `t ≥ 0`, `u ↦ G_{m-a}(t-u) B(v_u,v_u)` is integrable on `[0,t]` and
  `j v_t = G_{m-a}(t) j x₀ + ∫_0^t G_{m-a}(t-u) B_ext(v_u, v_u) du`, `j : Σ^m → Σ^{m-a}`.

`ε` and `C` depend on `d, s, β, q, ρ, m` only.  Positivity of `ρ₀ + √ρ₀ v` is NOT part of this theorem (N7); it is the
fixed point of the contraction in the signed class.  Uniqueness of the solution in the (small) class is the separate packet N4
(`mov_nl_unique`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction Interval

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.MovC1

variable {d : ℕ}

/-- `x ∈ Σ^r` is orthogonal to `√ρ₀` in `L²` (`r ≥ 0`). -/
def MovMassZero (ρ : Euc d → ℝ) {r : ℝ} (hr : 0 ≤ r) (x : OscSpace d r) : Prop :=
  inner ℝ (movSqrtLp ρ) (mov2d_Phi d (mov2d_j hr x)) = 0

/-- The embedding `Σ^m → Σ^{m-a}`. -/
def movJa {s β q : ℝ} {ρ : Euc d → ℝ} (H : Mov2dTh d s β q ρ) (m : ℝ) : OscSpace d m →L[ℝ] OscSpace d (m - movA d s) :=
  mov2d_j (sub_le_self m (mov2d_a_bounds d H.hd H.hsd).1)

lemma mnd_m_nonneg {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) : 0 ≤ m := by
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

lemma mnd_massZero_iff {s β q : ℝ} {ρ : Euc d → ℝ} (ψ0 : SchwartzMap (Euc d) ℝ) (H : Mov2dTh d s β q ρ)
    (hψ0 : MndSqrt ρ ψ0) {r : ℝ} (hr : 0 ≤ r) (x : OscSpace d r) :
    MovMassZero ρ hr x ↔ x ∈ mndZ ψ0 hr := by
  unfold MovMassZero
  rw [mem_mndZ, mov2d_sqrtLp H ψ0 hψ0, LinearIsometryEquiv.inner_map_map]

/-- **N5: existence of the mild solution** (contraction in `C_b([0,∞); Σ^m ∩ L²_0)` with weight `e^{ct/2}`). -/
theorem mov63_mild_existence {s β q : ℝ} {ρ : Euc d → ℝ} (H : Mov2dTh d s β q ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℝ) (hm : (d : ℝ) / 2 + 3 < m), ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
      ∀ x0 : OscSpace d m, MovMassZero ρ (mnd_m_nonneg hm) x0 → ‖x0‖ ≤ ε →
        ∃ v : ℝ → OscSpace d m, ContinuousOn v (Ici 0) ∧ v 0 = x0 ∧
          (∀ t : ℝ, 0 ≤ t → MovMassZero ρ (mnd_m_nonneg hm) (v t)) ∧
          (∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ C * ‖x0‖ * Real.exp (-(c / 2) * t)) ∧
          ∀ t : ℝ, 0 ≤ t →
            IntervalIntegrable (fun u => mov2d_G H (m - movA d s) (t - u) (mov_B_ext H hm (v u) (v u)))
                volume 0 t ∧
              movJa H m (v t) = mov2d_G H (m - movA d s) t (movJa H m x0) +
                ∫ u in (0 : ℝ)..t, mov2d_G H (m - movA d s) (t - u) (mov_B_ext H hm (v u) (v u)) := by
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  have hψ : MndSqrt ρ ψ0 := hψ0
  obtain ⟨lam, hlam, C0, hC0, hdec⟩ := movlin_L2_decay H ψ0 hψ0
  refine ⟨lam, hlam, fun m hm => ?_⟩
  have hm0 := mnd_m_nonneg hm
  have ha := mov2d_a_bounds d H.hd H.hsd
  have hma : 0 ≤ m - movA d s := mnb_sub_a_nonneg H hm
  have hle : m - movA d s ≤ m := sub_le_self m ha.1
  have hmA : movA d s ≤ m := by linarith
  obtain ⟨C1, hsb1⟩ := movlin_part_T H ψ0 hψ0 lam C0 hlam hC0 hdec hmA
  have hsb := movlin_smoothing_mono (le_max_left C1 0) hsb1
  set C : ℝ := max C1 0 with hCdef
  have hC : 0 ≤ C := le_max_right _ _
  obtain ⟨S, hSj, hSb⟩ := mnd_S_exists ψ0 H hψ hm0 hma hC hsb
  obtain ⟨B, K, hK0, hBc, hBb⟩ := mnd_B_exists ψ0 H hψ hm hm0 hma
  have hker : MndKer (mndU ψ0 H hψ hm0) S lam C C (1 - movA d s / 2) :=
    { CU_nonneg := hC
      CS_nonneg := hC
      c_pos := hlam
      θ_pos := by linarith [ha.2]
      θ_le := by linarith [ha.1]
      U_zero := fun x => mndU_zero ψ0 H hψ hm0 x
      U_cont := fun x => mndU_cont ψ0 H hψ hm0 x
      U_bound := fun t ht => by
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
        have := mnd_G_decay ψ0 H hψ hm0 hsb ht x.2
        have e : ‖mndU ψ0 H hψ hm0 t x‖ = ‖mov2d_G H m t (x : OscSpace d m)‖ := by
          show ‖((mndU ψ0 H hψ hm0 t x : mndZ ψ0 hm0) : OscSpace d m)‖ = _
          rw [mndU_coe ψ0 H hψ hm0 ht]
        rw [e]
        exact this
      S_cont := fun y => mnd_S_cont ψ0 H hψ hm0 hma hSj y
      S_bound := fun τ hτ => by
        have e : (1 - movA d s / 2) - 1 = -(movA d s) / 2 := by ring
        rw [e]
        exact hSb τ hτ }
  have hS : MndSetup (mndU ψ0 H hψ hm0) S B lam C C (1 - movA d s / 2) K := ⟨hker, hK0, hBb⟩
  obtain ⟨ε, hε, hex⟩ := mnd_abstract_exists hS
  refine ⟨ε, 2 * C + 1, hε, by positivity, fun x0 hx0 hxε => ?_⟩
  have hx0Z : x0 ∈ mndZ ψ0 hm0 := (mnd_massZero_iff ψ0 H hψ hm0 x0).1 hx0
  obtain ⟨v', hv'c, hv'0, hv'n, hv'm⟩ := hex ⟨x0, hx0Z⟩ hxε
  refine ⟨fun t => ((v' t : mndZ ψ0 hm0) : OscSpace d m), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp_continuousOn hv'c
  · simp [hv'0]
  · intro t ht
    exact (mnd_massZero_iff ψ0 H hψ hm0 _).2 (v' t).2
  · intro t ht
    have := hv'n t ht
    have h0 : ‖((v' t : mndZ ψ0 hm0) : OscSpace d m)‖ = ‖v' t‖ := rfl
    show ‖((v' t : mndZ ψ0 hm0) : OscSpace d m)‖ ≤ _
    rw [h0]
    refine this.trans ?_
    have h1 : ‖(⟨x0, hx0Z⟩ : mndZ ψ0 hm0)‖ = ‖x0‖ := rfl
    rw [h1]
    have h2 := Real.exp_pos (-(lam / 2) * t)
    have h3 := norm_nonneg x0
    nlinarith [mul_nonneg h2.le h3]
  · intro t ht
    obtain ⟨hint, hmild⟩ := hv'm t ht
    set L : mndZ ψ0 hm0 →L[ℝ] OscSpace d (m - movA d s) := (movJa H m).comp (mndZ ψ0 hm0).subtypeL with hL
    have hLapp : ∀ z : mndZ ψ0 hm0, L z = movJa H m (z : OscSpace d m) := fun z => rfl
    -- the integrand identity (a.e.)
    have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ι (0 : ℝ) t →
        L (S (t - u) (B (v' u) (v' u))) =
          mov2d_G H (m - movA d s) (t - u) (mov_B_ext H hm (v' u : OscSpace d m) (v' u : OscSpace d m)) := by
      have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({t} : Set ℝ) :=
        (Set.finite_singleton t).countable.ae_notMem _
      refine hne.mono (fun u hu hu' => ?_)
      have hu'' : u ∈ Ioc (0 : ℝ) t := by rwa [Set.uIoc_of_le ht] at hu'
      have hut : u < t := lt_of_le_of_ne hu''.2 hu
      rw [hLapp]
      have := hSj (t - u) (by linarith) (B (v' u) (v' u))
      unfold movJa
      rw [this, hBc]
    have hint' : IntervalIntegrable (fun u => L (S (t - u) (B (v' u) (v' u)))) volume 0 t := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht] at hint ⊢
      exact L.integrable_comp hint
    refine ⟨hint'.congr_ae ?_, ?_⟩
    · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      exact hae
    · have h1 := congrArg L hmild
      rw [map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm L hint] at h1
      rw [hLapp] at h1
      rw [h1]
      congr 1
      · rw [hLapp, mndU_coe ψ0 H hψ hm0 ht]
        unfold movJa
        rw [mov2d_G_compat H _ ht]
      · exact intervalIntegral.integral_congr_ae hae

end HRS.MS.Mov63

end

example := @HRS.MS.Mov63.mov63_mild_existence
