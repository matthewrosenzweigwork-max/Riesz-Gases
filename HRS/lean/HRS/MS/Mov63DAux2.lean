import HRS.MS.Mov63DAux1
import HRS.MS.Mov63BAux5
import HRS.MS.MovLinTie

/-!
# S6.3, packet N5 (part 2): the concrete spaces `Z_r = Σ^r ∩ L²_0`, the flow `U` and the bridge to `MovSmoothingBounds`

Namespace `HRS.MS.Mov63`, helper prefix `mnd_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not a manuscript row.
See `Mov63DAux1` for the plan.

* `mndEll ψ0 hr : OscSpace d r →L ℝ`, `x ↦ ⟨√ρ₀, x⟩` (through `mov2d_j : Σ^r → Σ^0`); `mndZ ψ0 hr = ker` (closed, complete).
* `mndU`: the restriction of the scale-level flow `mov2d_G H r t` to `Z_r` (`mndZ_G`: `Z_r` is invariant).
* `mnd_bridge`: `x ∈ Z_r` is `ofFun r f` for an `L²_0` element with `MemOsc r f`; `mnd_T_G`: the semigroup `mov2d_T` acts as `G`
  on the scale; `mnd_G_decay` and `mnd_smooth`: the bounds `MovSmoothingBounds` transferred to the scale-level flow.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section Spaces

/-- The pairing with `√ρ₀` at level `r ≥ 0` (through the embedding into `Σ^0 = L²`). -/
def mndEll (ψ0 : 𝓢R) {r : ℝ} (hr : 0 ≤ r) : OscSpace d r →L[ℝ] ℝ :=
  (innerSL ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ))).comp (mov2d_j hr)

/-- `Z_r = {x ∈ Σ^r : ⟨√ρ₀, x⟩ = 0}`. -/
def mndZ (ψ0 : 𝓢R) {r : ℝ} (hr : 0 ≤ r) : Submodule ℝ (OscSpace d r) := LinearMap.ker (mndEll ψ0 hr : OscSpace d r →ₗ[ℝ] ℝ)

lemma mem_mndZ (ψ0 : 𝓢R) {r : ℝ} (hr : 0 ≤ r) {x : OscSpace d r} :
    x ∈ mndZ ψ0 hr ↔ inner ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) (mov2d_j hr x) = 0 := by
  simp [mndZ, mndEll]

lemma mndZ_closed (ψ0 : 𝓢R) {r : ℝ} (hr : 0 ≤ r) : IsClosed (mndZ ψ0 hr : Set (OscSpace d r)) :=
  (mndEll ψ0 hr).isClosed_ker

instance mndZ_complete (ψ0 : 𝓢R) {r : ℝ} (hr : 0 ≤ r) : CompleteSpace (mndZ ψ0 hr) :=
  (mndZ_closed ψ0 hr).completeSpace_coe

/-- `ψ0` is the Schwartz function `√ρ₀`. -/
def MndSqrt (ρ : Euc d → ℝ) (ψ0 : 𝓢R) : Prop := (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)

variable {s β q : ℝ} {ρ : Euc d → ℝ} (ψ0 : SchwartzMap (Euc d) ℝ) (H : Mov2dTh d s β q ρ) (hψ0 : MndSqrt ρ ψ0)
include H hψ0

lemma mndZ_G {r : ℝ} (hr : 0 ≤ r) {t : ℝ} (ht : 0 ≤ t) {x : OscSpace d r} (hx : x ∈ mndZ ψ0 hr) :
    mov2d_G H r t x ∈ mndZ ψ0 hr := by
  rw [mem_mndZ] at hx ⊢
  rw [mov2d_G_compat H hr ht, mov2d_ell_inv H ψ0 hψ0 _ ht, hx]

open Classical in
/-- The flow `G(t)` restricted to `Z_r` (`t ≥ 0`). -/
def mndU {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : mndZ ψ0 hr →L[ℝ] mndZ ψ0 hr :=
  if ht : 0 ≤ t then
    ((mov2d_G H r t).comp (mndZ ψ0 hr).subtypeL).codRestrict (mndZ ψ0 hr)
      (fun x => mndZ_G ψ0 H hψ0 hr ht x.2)
  else ContinuousLinearMap.id ℝ _

lemma mndU_coe {r : ℝ} (hr : 0 ≤ r) {t : ℝ} (ht : 0 ≤ t) (x : mndZ ψ0 hr) :
    ((mndU ψ0 H hψ0 hr t x : mndZ ψ0 hr) : OscSpace d r) = mov2d_G H r t (x : OscSpace d r) := by
  unfold mndU
  rw [dif_pos ht]
  rfl

lemma mndU_zero {r : ℝ} (hr : 0 ≤ r) (x : mndZ ψ0 hr) : mndU ψ0 H hψ0 hr 0 x = x :=
  Subtype.ext (by rw [mndU_coe ψ0 H hψ0 hr le_rfl, mov2d_G_zero])

lemma mndU_cont {r : ℝ} (hr : 0 ≤ r) (x : mndZ ψ0 hr) :
    ContinuousOn (fun t => mndU ψ0 H hψ0 hr t x) (Ici 0) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  refine (mov2d_G_cont H r (x : OscSpace d r)).congr (fun t ht => ?_)
  exact mndU_coe ψ0 H hψ0 hr ht x

lemma mndU_add {r : ℝ} (hr : 0 ≤ r) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (x : mndZ ψ0 hr) :
    mndU ψ0 H hψ0 hr (a + b) x = mndU ψ0 H hψ0 hr b (mndU ψ0 H hψ0 hr a x) :=
  Subtype.ext (by
    rw [mndU_coe ψ0 H hψ0 hr (add_nonneg ha hb), mndU_coe ψ0 H hψ0 hr hb, mndU_coe ψ0 H hψ0 hr ha,
      mov2d_G_add H r ha hb])

end Spaces

section Bridge

variable {s β q : ℝ} {ρ : Euc d → ℝ} (ψ0 : SchwartzMap (Euc d) ℝ) (H : Mov2dTh d s β q ρ) (hψ0 : MndSqrt ρ ψ0)
include H hψ0

/-- An element of `Z_r` is `ofFun r f` for an `L²_0` element with `MemOsc r f`. -/
lemma mnd_bridge {r : ℝ} (hr : 0 ≤ r) {x : OscSpace d r} (hx : x ∈ mndZ ψ0 hr) :
    ∃ v : MovL2Zero ρ, MemOsc r (movFun v) ∧ OscSpace.ofFun r (movFun v) = x ∧
      OscSpace.ofFun 0 (movFun v) = mov2d_j hr x := by
  have hmem : mov2d_Phi d (mov2d_j hr x) ∈ MovL2Zero ρ := by
    rw [mov2d_mem_zero_iff, mov2d_sqrtLp H ψ0 hψ0, LinearIsometryEquiv.inner_map_map]
    exact (mem_mndZ ψ0 hr).1 hx
  refine ⟨⟨mov2d_Phi d (mov2d_j hr x), hmem⟩, ?_⟩
  have h0 : OscSpace.ofFun 0 (movFun (⟨mov2d_Phi d (mov2d_j hr x), hmem⟩ : MovL2Zero ρ)) = mov2d_j hr x := by
    have := (movlin_L2_osc (mov2d_Phi d (mov2d_j hr x))).2.2
    simpa using this
  obtain ⟨hm, he⟩ := movlin_memOsc_of_lev hr (Lp.memLp (mov2d_Phi d (mov2d_j hr x))) h0.symm
  exact ⟨hm, he, h0⟩

/-- The semigroup `mov2d_T` acts as the scale-level flow `G`. -/
lemma mnd_T_G {r' r : ℝ} (hr' : 0 ≤ r') (hrr : r' ≤ r) {t : ℝ} (ht : 0 ≤ t) (v : MovL2Zero ρ)
    (hv : MemOsc r' (movFun v)) (hT : MemOsc r (movFun (mov2d_T H ψ0 hψ0 t v))) :
    mov2d_j hrr (OscSpace.ofFun r (movFun (mov2d_T H ψ0 hψ0 t v))) =
      mov2d_G H r' t (OscSpace.ofFun r' (movFun v)) := by
  refine movlin_j_inj hr' ?_
  rw [movlin_j_comp hrr hr', mov2d_j_ofFun (hr'.trans hrr) hT, movlin_T_seq H ψ0 hψ0 ht v,
    mov2d_G_compat H hr' ht, mov2d_j_ofFun hr' hv]

/-- Decay of the scale-level flow on `Z_r` from `MovSmoothingBounds`. -/
lemma mnd_G_decay {r : ℝ} (hr : 0 ≤ r) {c C : ℝ} (hsb : MovSmoothingBounds d s ρ r c C (mov2d_T H ψ0 hψ0))
    {t : ℝ} (ht : 0 ≤ t) {x : OscSpace d r} (hx : x ∈ mndZ ψ0 hr) :
    ‖mov2d_G H r t x‖ ≤ C * Real.exp (-c * t) * ‖x‖ := by
  obtain ⟨v, hm, he, -⟩ := mnd_bridge ψ0 H hψ0 hr hx
  obtain ⟨hT, hb⟩ := hsb.1 t ht v hm
  have h1 := mnd_T_G ψ0 H hψ0 hr le_rfl ht v hm hT
  rw [mov2d_j_refl, ContinuousLinearMap.id_apply, he] at h1
  rw [← h1, OscSpace.norm_ofFun _ hT, ← he, OscSpace.norm_ofFun _ hm]
  exact hb

/-- Smoothing of the scale-level flow from `MovSmoothingBounds`. -/
lemma mnd_smooth {m : ℝ} (hm0 : 0 ≤ m) (hma : 0 ≤ m - movA d s) {c C : ℝ}
    (hsb : MovSmoothingBounds d s ρ m c C (mov2d_T H ψ0 hψ0)) {t : ℝ} (ht : 0 < t)
    {y : OscSpace d (m - movA d s)} (hy : y ∈ mndZ ψ0 hma) :
    ∃ z : OscSpace d m, z ∈ mndZ ψ0 hm0 ∧
      mov2d_j (sub_le_self m (mov2d_a_bounds d H.hd H.hsd).1) z = mov2d_G H (m - movA d s) t y ∧
      ‖z‖ ≤ C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-c * t) * ‖y‖ := by
  have hle : m - movA d s ≤ m := sub_le_self m (mov2d_a_bounds d H.hd H.hsd).1
  obtain ⟨v, hv, he, -⟩ := mnd_bridge ψ0 H hψ0 hma hy
  obtain ⟨hT, hb⟩ := hsb.2 t ht v hv
  have h1 := mnd_T_G ψ0 H hψ0 hma hle ht.le v hv hT
  rw [he] at h1
  refine ⟨OscSpace.ofFun m (movFun (mov2d_T H ψ0 hψ0 t v)), ?_, h1, ?_⟩
  · rw [mem_mndZ]
    have : mov2d_j hm0 (OscSpace.ofFun m (movFun (mov2d_T H ψ0 hψ0 t v))) =
        mov2d_j hma (mov2d_G H (m - movA d s) t y) := by
      rw [← h1, movlin_j_comp hle hma]
    rw [this]
    exact (mem_mndZ ψ0 hma).1 (mndZ_G ψ0 H hψ0 hma ht.le hy)
  · rw [OscSpace.norm_ofFun _ hT, ← he, OscSpace.norm_ofFun _ hv]
    exact hb

end Bridge

section SOp

variable {s β q : ℝ} {ρ : Euc d → ℝ} (ψ0 : SchwartzMap (Euc d) ℝ) (H : Mov2dTh d s β q ρ) (hψ0 : MndSqrt ρ ψ0)
include H hψ0

/-- The smoothing operators `S(t) : Z_{m-a} → Z_m` (`t > 0`): the scale-level flow, lifted through `j`. -/
lemma mnd_S_exists {m : ℝ} (hm0 : 0 ≤ m) (hma : 0 ≤ m - movA d s) {c C : ℝ} (hC : 0 ≤ C)
    (hsb : MovSmoothingBounds d s ρ m c C (mov2d_T H ψ0 hψ0)) :
    ∃ S : ℝ → mndZ ψ0 hma →L[ℝ] mndZ ψ0 hm0,
      (∀ t : ℝ, 0 < t → ∀ y : mndZ ψ0 hma,
        mov2d_j (sub_le_self m (mov2d_a_bounds d H.hd H.hsd).1) ((S t y : mndZ ψ0 hm0) : OscSpace d m) =
          mov2d_G H (m - movA d s) t (y : OscSpace d (m - movA d s))) ∧
      ∀ t : ℝ, 0 < t → ‖S t‖ ≤ C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-c * t) := by
  have hle : m - movA d s ≤ m := sub_le_self m (mov2d_a_bounds d H.hd H.hsd).1
  have hex : ∀ t : ℝ, ∀ y : mndZ ψ0 hma, ∃ z : mndZ ψ0 hm0, 0 < t →
      (mov2d_j hle (z : OscSpace d m) = mov2d_G H (m - movA d s) t (y : OscSpace d (m - movA d s)) ∧
        ‖z‖ ≤ C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-c * t) * ‖y‖) := by
    intro t y
    by_cases ht : 0 < t
    · obtain ⟨z, hz, h1, h2⟩ := mnd_smooth ψ0 H hψ0 hm0 hma hsb ht y.2
      exact ⟨⟨z, hz⟩, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose zf hzf using hex
  have hadd : ∀ t : ℝ, 0 < t → ∀ y1 y2 : mndZ ψ0 hma, zf t (y1 + y2) = zf t y1 + zf t y2 := by
    intro t ht y1 y2
    refine Subtype.ext (movlin_j_inj hle ?_)
    have e1 := (hzf t (y1 + y2) ht).1
    have e2 := (hzf t y1 ht).1
    have e3 := (hzf t y2 ht).1
    simp only [Submodule.coe_add, map_add] at e1 ⊢
    rw [e1, e2, e3]
  have hsm : ∀ t : ℝ, 0 < t → ∀ (a : ℝ) (y : mndZ ψ0 hma), zf t (a • y) = a • zf t y := by
    intro t ht a y
    refine Subtype.ext (movlin_j_inj hle ?_)
    have e1 := (hzf t (a • y) ht).1
    have e2 := (hzf t y ht).1
    simp only [Submodule.coe_smul, map_smul] at e1 ⊢
    rw [e1, e2]
  have hcs : ∀ t : ℝ, 0 < t → 0 ≤ C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-c * t) := by
    intro t ht
    have := Real.rpow_nonneg ht.le (-(movA d s) / 2)
    positivity
  let Sc : ℝ → mndZ ψ0 hma →L[ℝ] mndZ ψ0 hm0 := fun t =>
    if ht : 0 < t then
      LinearMap.mkContinuous
        ({ toFun := zf t, map_add' := hadd t ht, map_smul' := hsm t ht } : mndZ ψ0 hma →ₗ[ℝ] mndZ ψ0 hm0)
        (C * (1 + t ^ (-(movA d s) / 2)) * Real.exp (-c * t)) (fun y => (hzf t y ht).2)
    else 0
  have hSc : ∀ t : ℝ, 0 < t → ∀ y, Sc t y = zf t y := by
    intro t ht y
    simp only [Sc, dif_pos ht]
    rfl
  refine ⟨Sc, fun t ht y => ?_, fun t ht => ?_⟩
  · rw [hSc t ht]; exact (hzf t y ht).1
  · simp only [Sc, dif_pos ht]
    exact LinearMap.mkContinuous_norm_le _ (hcs t ht) _

/-- Strong continuity of `S` on `(0, ∞)`, from the semigroup law on the scale. -/
lemma mnd_S_cont {m : ℝ} (hm0 : 0 ≤ m) (hma : 0 ≤ m - movA d s)
    {S : ℝ → mndZ ψ0 hma →L[ℝ] mndZ ψ0 hm0}
    (hS : ∀ t : ℝ, 0 < t → ∀ y : mndZ ψ0 hma,
        mov2d_j (sub_le_self m (mov2d_a_bounds d H.hd H.hsd).1) ((S t y : mndZ ψ0 hm0) : OscSpace d m) =
          mov2d_G H (m - movA d s) t (y : OscSpace d (m - movA d s)))
    (y : mndZ ψ0 hma) : ContinuousOn (fun τ => S τ y) (Ioi 0) := by
  have hle : m - movA d s ≤ m := sub_le_self m (mov2d_a_bounds d H.hd H.hsd).1
  intro τ0 hτ0
  have hτ0' : (0 : ℝ) < τ0 := hτ0
  set ε : ℝ := τ0 / 2 with hε
  have hε0 : 0 < ε := by positivity
  set z : mndZ ψ0 hm0 := S ε y with hz
  have hrel : ∀ τ : ℝ, ε ≤ τ → S τ y = mndU ψ0 H hψ0 hm0 (τ - ε) z := by
    intro τ hτ
    have hτp : 0 < τ := lt_of_lt_of_le hε0 hτ
    refine Subtype.ext (movlin_j_inj hle ?_)
    rw [hS τ hτp y, mndU_coe ψ0 H hψ0 hm0 (by linarith), mov2d_G_compat H hle (by linarith), hz, hS ε hε0 y,
      ← mov2d_G_add H _ hε0.le (by linarith : (0 : ℝ) ≤ τ - ε)]
    congr 1
    ring
  have hc1 : ContinuousOn (fun τ : ℝ => mndU ψ0 H hψ0 hm0 (τ - ε) z) (Ici ε) :=
    (mndU_cont ψ0 H hψ0 hm0 z).comp (continuousOn_id.sub continuousOn_const)
      (fun τ hτ => by simpa using sub_nonneg.2 (show ε ≤ τ from hτ))
  have hat : ContinuousAt (fun τ : ℝ => mndU ψ0 H hψ0 hm0 (τ - ε) z) τ0 :=
    hc1.continuousAt (Ici_mem_nhds (by linarith))
  have hev : (fun τ => S τ y) =ᶠ[𝓝 τ0] fun τ => mndU ψ0 H hψ0 hm0 (τ - ε) z := by
    filter_upwards [Ici_mem_nhds (show ε < τ0 by linarith)] with τ hτ using hrel τ hτ
  exact (hat.congr hev.symm).continuousWithinAt

/-- The bilinear term on `Z_m × Z_m → Z_{m-a}`. -/
lemma mnd_B_exists {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (hm0 : 0 ≤ m) (hma : 0 ≤ m - movA d s) :
    ∃ (B : mndZ ψ0 hm0 →L[ℝ] mndZ ψ0 hm0 →L[ℝ] mndZ ψ0 hma) (K : ℝ), 0 ≤ K ∧
      (∀ x y, ((B x y : mndZ ψ0 hma) : OscSpace d (m - movA d s)) =
        mov_B_ext H hm (x : OscSpace d m) (y : OscSpace d m)) ∧ ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖ := by
  obtain ⟨K, hK0, hK⟩ := mov_B_ext_bound H hm
  have hmem : ∀ x y : OscSpace d m, mov_B_ext H hm x y ∈ mndZ ψ0 hma := by
    intro x y
    rw [mem_mndZ]
    have := mov_B_ext_mass H hm hma x y
    rwa [mov2d_sqrtLp H ψ0 hψ0, LinearIsometryEquiv.inner_map_map] at this
  let f : mndZ ψ0 hm0 →ₗ[ℝ] mndZ ψ0 hm0 →ₗ[ℝ] mndZ ψ0 hma :=
    LinearMap.mk₂ ℝ (fun x y => ⟨mov_B_ext H hm (x : OscSpace d m) (y : OscSpace d m), hmem _ _⟩)
      (fun x1 x2 y => Subtype.ext (by simp))
      (fun a x y => Subtype.ext (by simp))
      (fun x y1 y2 => Subtype.ext (by simp))
      (fun a x y => Subtype.ext (by simp))
  exact ⟨f.mkContinuous₂ K (fun x y => hK x y), K, hK0, fun x y => rfl, fun x y => hK x y⟩

end SOp

end HRS.MS.Mov63

end
