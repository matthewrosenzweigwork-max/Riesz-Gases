import HRS.MS.Mov63BAux1

/-!
# S6.3 packet N2a (2): the continuous bilinear extension `mov_B_ext`

Namespace `HRS.MS.Mov63`, helper prefix `mnb_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not a manuscript row.

For the standing thermal data `H : Mov2dTh d s β q ρ` and a real `m > d/2 + 3`:

* `mnb_bilin_ext`: abstract extension of a bounded bilinear map from a dense subspace.
* `mnb_bfun`, `mnb_bil`: the bilinear map `(c, c') ↦ ofFun_{m-a} (B (∑ c_α h_α, ∑ c'_α h_α))` on the finitely supported
  coefficient vectors (bilinear by `mnb_B_lin_left/right`, bounded by `mov_operators_B_proof`).
* `mov_B_ext H hm : OscSpace d m →L OscSpace d m →L OscSpace d (m - movA d s)`: its continuous extension.
* `mov_B_ext_hs`: the action on finite Hermite sums.
* `mov_B_ext_bound`: `‖B(v,w)‖_{Σ^{m-a}} ≤ K ‖v‖_{Σ^m} ‖w‖_{Σ^m}`.
* `mov_B_ext_schwartz`: on Schwartz data, `B_ext (ofFun m φ) (ofFun m ψ) = ofFun (m-a) (movB φ ψ)`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.MovC1

variable {d : ℕ}

/-! ## A. Abstract bilinear extension -/

section Abstract

variable {E X Y Z : Type*} [AddCommGroup E] [Module ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma mnb_clm_ext {e : E →ₗ[ℝ] X} (he : DenseRange e) {E₁ E₂ : X →L[ℝ] Z}
    (h : ∀ c, E₁ (e c) = E₂ (e c)) : E₁ = E₂ := by
  have := he.equalizer E₁.continuous E₂.continuous (funext fun c => h c)
  exact DFunLike.coe_injective this

lemma mnb_bilin_ext [CompleteSpace Y] (e : E →ₗ[ℝ] X) (he : DenseRange e) (b : E →ₗ[ℝ] E →ₗ[ℝ] Y) (K : ℝ)
    (hK : 0 ≤ K) (hb : ∀ c c', ‖b c c'‖ ≤ K * ‖e c‖ * ‖e c'‖) :
    ∃ B : X →L[ℝ] X →L[ℝ] Y, (∀ c c', B (e c) (e c') = b c c') ∧ ∀ x y, ‖B x y‖ ≤ K * ‖x‖ * ‖y‖ := by
  set T : E → X →L[ℝ] Y := fun c => (b c).extendOfNorm e with hT
  have hTe : ∀ c c', T c (e c') = b c c' := fun c c' =>
    LinearMap.extendOfNorm_eq he ⟨K * ‖e c‖, fun c' => hb c c'⟩ c'
  have hTn : ∀ c x, ‖T c x‖ ≤ K * ‖e c‖ * ‖x‖ := fun c x =>
    LinearMap.norm_extendOfNorm_apply_le he (K * ‖e c‖) (fun c' => hb c c') x
  let g : E →ₗ[ℝ] (X →L[ℝ] Y) :=
    { toFun := T
      map_add' := fun c1 c2 => mnb_clm_ext he fun c' => by
        rw [add_apply, hTe, hTe, hTe, map_add, LinearMap.add_apply]
      map_smul' := fun r c => mnb_clm_ext he fun c' => by
        rw [smul_apply, hTe, hTe, map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hg : ∀ c, ‖g c‖ ≤ K * ‖e c‖ := fun c =>
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hTn c)
  refine ⟨g.extendOfNorm e, fun c c' => ?_, fun x y => ?_⟩
  · have h1 : (g.extendOfNorm e) (e c) = T c := LinearMap.extendOfNorm_eq he ⟨K, hg⟩ c
    rw [h1, hTe]
  · have h1 := LinearMap.norm_extendOfNorm_apply_le he K hg x
    calc ‖(g.extendOfNorm e) x y‖ ≤ ‖(g.extendOfNorm e) x‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖x‖ * ‖y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

end Abstract

/-! ## B. The bilinear map on finite Hermite sums -/

section Concrete

variable {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

lemma mnb_rhoData (H : Mov2dTh d s β q ρ) : MovRhoData d ρ := by
  obtain ⟨B, D⟩ := HRS.MS.MovC2.movc2_data H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  exact D.rho

lemma mnb_Kdata (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ φ ψ : 𝓢R, MemOsc (m - movA d s) (movB d s ρ (⇑φ) (⇑ψ)) ∧
      oscNorm (m - movA d s) (movB d s ρ (⇑φ) (⇑ψ)) ≤ K * oscNorm m φ * oscNorm m ψ := by
  obtain ⟨C, hC⟩ := HRS.MS.MovC2.mov_operators_B_proof H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ m hm
  refine ⟨max C 0, le_max_right _ _, fun φ ψ => ⟨(hC φ ψ).1, (hC φ ψ).2.trans ?_⟩⟩
  have h1 : 0 ≤ oscNorm m (⇑φ : Euc d → ℝ) := Real.sqrt_nonneg _
  have h2 : 0 ≤ oscNorm m (⇑ψ : Euc d → ℝ) := Real.sqrt_nonneg _
  have := mul_nonneg h1 h2
  nlinarith [le_max_left C 0, mul_le_mul_of_nonneg_right (le_max_left C 0) this]

lemma mnb_hs_sch (c : MultiIndex d →₀ ℝ) : ∃ φ : 𝓢R, (⇑φ : Euc d → ℝ) = mov2d_hs d c :=
  mov2d_hs_schwartz c

lemma mnb_B_smul_left (H : Mov2dTh d s β q ρ) (v w : 𝓢R) (a : ℝ) (x : Euc d) :
    movB d s ρ (fun z => a * v z) (⇑w) x = a * movB d s ρ (⇑v) (⇑w) x := by
  have e : (fun z => a * v z) = fun z => a * v z + 0 * v z := by funext z; ring
  rw [e, mnb_B_lin_left (d := d) (s := s) (by have := H.hd; omega) H.hs0 H.hsd (mnb_rhoData H) v v w a 0 x]
  ring

lemma mnb_B_smul_right (H : Mov2dTh d s β q ρ) (v w : 𝓢R) (a : ℝ) (x : Euc d) :
    movB d s ρ (⇑v) (fun z => a * w z) x = a * movB d s ρ (⇑v) (⇑w) x := by
  have e : (fun z => a * w z) = fun z => a * w z + 0 * w z := by funext z; ring
  rw [e, mnb_B_lin_right (d := d) (s := s) (by have := H.hd; omega) H.hs0 H.hsd (mnb_rhoData H) v w w a 0 x]
  ring

/-- Bilinearity of `B` on the Hermite sums (pointwise, from `mnb_B_lin_*`). -/
lemma mnb_B_hs_add_left (H : Mov2dTh d s β q ρ) (c1 c2 c' : MultiIndex d →₀ ℝ) :
    movB d s ρ (mov2d_hs d (c1 + c2)) (mov2d_hs d c') = fun x =>
      movB d s ρ (mov2d_hs d c1) (mov2d_hs d c') x + movB d s ρ (mov2d_hs d c2) (mov2d_hs d c') x := by
  obtain ⟨φ1, h1⟩ := mnb_hs_sch (d := d) c1
  obtain ⟨φ2, h2⟩ := mnb_hs_sch (d := d) c2
  obtain ⟨ψ, h3⟩ := mnb_hs_sch (d := d) c'
  funext x
  have e : mov2d_hs d (c1 + c2) = fun z => 1 * φ1 z + 1 * φ2 z := by
    rw [mov2d_hs_add, ← h1, ← h2]; funext z; ring
  rw [e, ← h1, ← h2, ← h3, mnb_B_lin_left (d := d) (s := s) (by have := H.hd; omega) H.hs0 H.hsd (mnb_rhoData H)
    φ1 φ2 ψ 1 1 x]
  ring

lemma mnb_B_hs_smul_left (H : Mov2dTh d s β q ρ) (r : ℝ) (c c' : MultiIndex d →₀ ℝ) :
    movB d s ρ (mov2d_hs d (r • c)) (mov2d_hs d c') = fun x => r * movB d s ρ (mov2d_hs d c) (mov2d_hs d c') x := by
  obtain ⟨φ1, h1⟩ := mnb_hs_sch (d := d) c
  obtain ⟨ψ, h3⟩ := mnb_hs_sch (d := d) c'
  funext x
  rw [mov2d_hs_smul, ← h1, ← h3]
  exact mnb_B_smul_left H φ1 ψ r x

lemma mnb_B_hs_add_right (H : Mov2dTh d s β q ρ) (c c1 c2 : MultiIndex d →₀ ℝ) :
    movB d s ρ (mov2d_hs d c) (mov2d_hs d (c1 + c2)) = fun x =>
      movB d s ρ (mov2d_hs d c) (mov2d_hs d c1) x + movB d s ρ (mov2d_hs d c) (mov2d_hs d c2) x := by
  obtain ⟨φ1, h1⟩ := mnb_hs_sch (d := d) c1
  obtain ⟨φ2, h2⟩ := mnb_hs_sch (d := d) c2
  obtain ⟨ψ, h3⟩ := mnb_hs_sch (d := d) c
  funext x
  have e : mov2d_hs d (c1 + c2) = fun z => 1 * φ1 z + 1 * φ2 z := by
    rw [mov2d_hs_add, ← h1, ← h2]; funext z; ring
  rw [e, ← h1, ← h2, ← h3, mnb_B_lin_right (d := d) (s := s) (by have := H.hd; omega) H.hs0 H.hsd (mnb_rhoData H)
    ψ φ1 φ2 1 1 x]
  ring

lemma mnb_B_hs_smul_right (H : Mov2dTh d s β q ρ) (r : ℝ) (c c' : MultiIndex d →₀ ℝ) :
    movB d s ρ (mov2d_hs d c) (mov2d_hs d (r • c')) = fun x => r * movB d s ρ (mov2d_hs d c) (mov2d_hs d c') x := by
  obtain ⟨φ1, h1⟩ := mnb_hs_sch (d := d) c'
  obtain ⟨ψ, h3⟩ := mnb_hs_sch (d := d) c
  funext x
  rw [mov2d_hs_smul, ← h1, ← h3]
  exact mnb_B_smul_right H ψ φ1 r x

lemma mnb_memOsc_hs (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (c c' : MultiIndex d →₀ ℝ) :
    MemOsc (m - movA d s) (movB d s ρ (mov2d_hs d c) (mov2d_hs d c')) ∧
      oscNorm (m - movA d s) (movB d s ρ (mov2d_hs d c) (mov2d_hs d c')) ≤
        (mnb_Kdata H hm).choose * oscNorm m (mov2d_hs d c) * oscNorm m (mov2d_hs d c') := by
  obtain ⟨φ, h1⟩ := mnb_hs_sch (d := d) c
  obtain ⟨ψ, h2⟩ := mnb_hs_sch (d := d) c'
  rw [← h1, ← h2]
  exact (mnb_Kdata H hm).choose_spec.2 φ ψ

/-- The function-level bilinear data on finite Hermite sums. -/
def mnb_bfun (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (m : ℝ) (c c' : MultiIndex d →₀ ℝ) : OscSpace d (m - movA d s) :=
  OscSpace.ofFun (m - movA d s) (movB d s ρ (mov2d_hs d c) (mov2d_hs d c'))

/-- The bilinear map on the finitely supported coefficient vectors. -/
def mnb_bil (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) :
    (MultiIndex d →₀ ℝ) →ₗ[ℝ] (MultiIndex d →₀ ℝ) →ₗ[ℝ] OscSpace d (m - movA d s) :=
  LinearMap.mk₂ ℝ (mnb_bfun d s ρ m)
    (fun c1 c2 c' => by
      unfold mnb_bfun
      rw [mnb_B_hs_add_left H, mov2d_ofFun_add (mnb_memOsc_hs H hm c1 c').1 (mnb_memOsc_hs H hm c2 c').1])
    (fun r c c' => by
      unfold mnb_bfun
      rw [mnb_B_hs_smul_left H, mov2d_ofFun_smul r (mnb_memOsc_hs H hm c c').1])
    (fun c c1 c2 => by
      unfold mnb_bfun
      rw [mnb_B_hs_add_right H, mov2d_ofFun_add (mnb_memOsc_hs H hm c c1).1 (mnb_memOsc_hs H hm c c2).1])
    (fun r c c' => by
      unfold mnb_bfun
      rw [mnb_B_hs_smul_right H, mov2d_ofFun_smul r (mnb_memOsc_hs H hm c c').1])

lemma mnb_bil_apply (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (c c' : MultiIndex d →₀ ℝ) :
    mnb_bil H hm c c' = OscSpace.ofFun (m - movA d s) (movB d s ρ (mov2d_hs d c) (mov2d_hs d c')) := rfl

lemma mnb_bil_bound (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (c c' : MultiIndex d →₀ ℝ) :
    ‖mnb_bil H hm c c'‖ ≤ (mnb_Kdata H hm).choose * ‖mov2d_e d m c‖ * ‖mov2d_e d m c'‖ := by
  rw [mnb_bil_apply, OscSpace.norm_ofFun _ (mnb_memOsc_hs H hm c c').1, mov2d_e_norm, mov2d_e_norm]
  exact (mnb_memOsc_hs H hm c c').2

/-- Existence of the bounded bilinear extension. -/
lemma mnb_B_exists (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) :
    ∃ B : OscSpace d m →L[ℝ] OscSpace d m →L[ℝ] OscSpace d (m - movA d s),
      (∀ c c', B (OscSpace.ofFun m (mov2d_hs d c)) (OscSpace.ofFun m (mov2d_hs d c')) =
        OscSpace.ofFun (m - movA d s) (movB d s ρ (mov2d_hs d c) (mov2d_hs d c'))) ∧
      ∀ x y, ‖B x y‖ ≤ (mnb_Kdata H hm).choose * ‖x‖ * ‖y‖ := by
  obtain ⟨B, hB1, hB2⟩ := mnb_bilin_ext (mov2d_e d m) (mov2d_e_dense m) (mnb_bil H hm)
    (mnb_Kdata H hm).choose (mnb_Kdata H hm).choose_spec.1 (mnb_bil_bound H hm)
  exact ⟨B, fun c c' => by
    have := hB1 c c'
    rwa [mnb_bil_apply, mov2d_e_apply, mov2d_e_apply] at this, hB2⟩

end Concrete

end HRS.MS.Mov63

end
