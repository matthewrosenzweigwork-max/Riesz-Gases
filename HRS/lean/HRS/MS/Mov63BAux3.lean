import HRS.MS.Mov63BAux2

/-!
# S6.3 packet N2a (3): `mov_B_ext` and its agreement with `movB` on Schwartz data

Namespace `HRS.MS.Mov63`, helper prefix `mnb_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not a manuscript row.

* `mov_B_ext H hm : OscSpace d m →L OscSpace d m →L OscSpace d (m - movA d s)` for `m > d/2 + 3`.
* `mov_B_ext_hs`: `B_ext (ofFun m (∑ c_α h_α)) (ofFun m (∑ c'_α h_α)) = ofFun (m-a) (movB ...)`.
* `mov_B_ext_bound`: `‖B_ext v w‖ ≤ K ‖v‖ ‖w‖`.
* `mov_B_ext_schwartz`: for Schwartz `φ, ψ`: `B_ext (ofFun m φ) (ofFun m ψ) = ofFun (m-a) (movB d s ρ φ ψ)`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.MovOsc HRS.MS.MovLin HRS.MS.MovC1

variable {d : ℕ}

section Main

variable {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- **The continuous bilinear extension of `B`** to the scale: `Σ^m × Σ^m → Σ^{m-a}`, `m > d/2 + 3`. -/
def mov_B_ext (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) :
    OscSpace d m →L[ℝ] OscSpace d m →L[ℝ] OscSpace d (m - movA d s) :=
  (mnb_B_exists H hm).choose

/-- Action on finite Hermite sums. -/
theorem mov_B_ext_hs (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (c c' : MultiIndex d →₀ ℝ) :
    mov_B_ext H hm (OscSpace.ofFun m (mov2d_hs d c)) (OscSpace.ofFun m (mov2d_hs d c')) =
      OscSpace.ofFun (m - movA d s) (movB d s ρ (mov2d_hs d c) (mov2d_hs d c')) :=
  (mnb_B_exists H hm).choose_spec.1 c c'

/-- Boundedness: `‖B(v,w)‖_{Σ^{m-a}} ≤ K ‖v‖_{Σ^m} ‖w‖_{Σ^m}`. -/
theorem mov_B_ext_bound (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v w : OscSpace d m, ‖mov_B_ext H hm v w‖ ≤ K * ‖v‖ * ‖w‖ :=
  ⟨(mnb_Kdata H hm).choose, (mnb_Kdata H hm).choose_spec.1, (mnb_B_exists H hm).choose_spec.2⟩

/-- Uniqueness: two bilinear extensions agreeing on finite Hermite sums coincide. -/
theorem mov_B_ext_unique (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m)
    (B' : OscSpace d m →L[ℝ] OscSpace d m →L[ℝ] OscSpace d (m - movA d s))
    (h : ∀ c c' : MultiIndex d →₀ ℝ, B' (OscSpace.ofFun m (mov2d_hs d c)) (OscSpace.ofFun m (mov2d_hs d c')) =
      OscSpace.ofFun (m - movA d s) (movB d s ρ (mov2d_hs d c) (mov2d_hs d c'))) :
    B' = mov_B_ext H hm := by
  refine mnb_clm_ext (e := mov2d_e d m) (mov2d_e_dense m) fun c => ?_
  refine mnb_clm_ext (e := mov2d_e d m) (mov2d_e_dense m) fun c' => ?_
  rw [mov2d_e_apply, mov2d_e_apply] at *
  rw [h, mov_B_ext_hs]

lemma mnb_pSum_tendsto {r : ℝ} {f : Euc d → ℝ} (hf : MemOsc r f) :
    Tendsto (fun n => OscSpace.ofFun r (mo_pSum f n)) atTop (𝓝 (OscSpace.ofFun r f)) := by
  have hgm : ∀ n, MemOsc r (mo_pSum f n) := fun n => mo_hsum_memOsc r _ _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have e : ∀ n, ‖OscSpace.ofFun r (mo_pSum f n) - OscSpace.ofFun r f‖ =
      oscNorm r (fun x => f x - mo_pSum f n x) := by
    intro n
    rw [norm_sub_rev, ← mov2d_ofFun_sub hf (hgm n), OscSpace.norm_ofFun _ (mov2d_memOsc_sub hf (hgm n))]
  simp_rw [e]
  exact mo_hsum_tail r hf

lemma mnb_pSum_eq_hs (f : Euc d → ℝ) (n : ℕ) :
    mo_pSum f n = mov2d_hs d (∑ α ∈ mova2_S d n, Finsupp.single α (hermiteCoeff f α)) := by
  rw [mov2d_hs_sum]; rfl

/-- The difference estimate for `B` on Schwartz data, in the scale. -/
lemma mnb_Bs_diff (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (φ φ' ψ ψ' : 𝓢R) :
    ‖OscSpace.ofFun (m - movA d s) (movB d s ρ (⇑φ) (⇑ψ)) -
        OscSpace.ofFun (m - movA d s) (movB d s ρ (⇑φ') (⇑ψ'))‖ ≤
      (mnb_Kdata H hm).choose * ‖OscSpace.ofFun m (⇑φ) - OscSpace.ofFun m (⇑φ')‖ * ‖OscSpace.ofFun m (⇑ψ)‖ +
        (mnb_Kdata H hm).choose * ‖OscSpace.ofFun m (⇑φ')‖ *
          ‖OscSpace.ofFun m (⇑ψ) - OscSpace.ofFun m (⇑ψ')‖ := by
  have hd1 : 1 ≤ d := by have := H.hd; omega
  have hρ := mnb_rhoData H
  set σ : ℝ := m - movA d s with hσ
  set D1 : 𝓢R := φ - φ' with hD1
  set D2 : 𝓢R := ψ - ψ' with hD2
  have hK := (mnb_Kdata H hm).choose_spec
  have hpt : ∀ x, movB d s ρ (⇑φ) (⇑ψ) x - movB d s ρ (⇑φ') (⇑ψ') x =
      movB d s ρ (⇑D1) (⇑ψ) x + movB d s ρ (⇑φ') (⇑D2) x := by
    intro x
    have e1 : (⇑D1 : Euc d → ℝ) = fun z => 1 * φ z + (-1) * φ' z := by
      funext z; simp [hD1]; ring
    have e2 : (⇑D2 : Euc d → ℝ) = fun z => 1 * ψ z + (-1) * ψ' z := by
      funext z; simp [hD2]; ring
    rw [e1, e2, mnb_B_lin_left hd1 H.hs0 H.hsd hρ φ φ' ψ 1 (-1) x,
      mnb_B_lin_right hd1 H.hs0 H.hsd hρ φ' ψ ψ' 1 (-1) x]
    ring
  have hm1 := hK.2 D1 ψ
  have hm2 := hK.2 φ' D2
  have hfun : (fun x => movB d s ρ (⇑φ) (⇑ψ) x - movB d s ρ (⇑φ') (⇑ψ') x) =
      fun x => movB d s ρ (⇑D1) (⇑ψ) x + movB d s ρ (⇑φ') (⇑D2) x := funext hpt
  have hA : OscSpace.ofFun σ (movB d s ρ (⇑φ) (⇑ψ)) - OscSpace.ofFun σ (movB d s ρ (⇑φ') (⇑ψ')) =
      OscSpace.ofFun σ (movB d s ρ (⇑D1) (⇑ψ)) + OscSpace.ofFun σ (movB d s ρ (⇑φ') (⇑D2)) := by
    have hmA := (hK.2 φ ψ).1
    have hmB := (hK.2 φ' ψ').1
    rw [← mov2d_ofFun_sub hmA hmB, hfun, mov2d_ofFun_add hm1.1 hm2.1]
  rw [hA]
  refine (norm_add_le _ _).trans ?_
  rw [OscSpace.norm_ofFun _ hm1.1, OscSpace.norm_ofFun _ hm2.1]
  have e3 : ‖OscSpace.ofFun m (⇑φ) - OscSpace.ofFun m (⇑φ')‖ = oscNorm m (⇑D1) := by
    have : (⇑D1 : Euc d → ℝ) = fun z => φ z - φ' z := by funext z; simp [hD1]
    rw [this, ← mov2d_ofFun_sub (memOsc_schwartz m φ) (memOsc_schwartz m φ'),
      OscSpace.norm_ofFun _ (mov2d_memOsc_sub (memOsc_schwartz m φ) (memOsc_schwartz m φ'))]
  have e4 : ‖OscSpace.ofFun m (⇑ψ) - OscSpace.ofFun m (⇑ψ')‖ = oscNorm m (⇑D2) := by
    have : (⇑D2 : Euc d → ℝ) = fun z => ψ z - ψ' z := by funext z; simp [hD2]
    rw [this, ← mov2d_ofFun_sub (memOsc_schwartz m ψ) (memOsc_schwartz m ψ'),
      OscSpace.norm_ofFun _ (mov2d_memOsc_sub (memOsc_schwartz m ψ) (memOsc_schwartz m ψ'))]
  rw [e3, e4, OscSpace.norm_ofFun _ (memOsc_schwartz m ψ), OscSpace.norm_ofFun _ (memOsc_schwartz m φ')]
  exact add_le_add hm1.2 hm2.2

/-- **`mov_B_ext_schwartz`**: on Schwartz data, the extension is the function-level `movB`. -/
theorem mov_B_ext_schwartz (H : Mov2dTh d s β q ρ) {m : ℝ} (hm : (d : ℝ) / 2 + 3 < m) (φ ψ : 𝓢R) :
    mov_B_ext H hm (OscSpace.ofFun m (⇑φ)) (OscSpace.ofFun m (⇑ψ)) =
      OscSpace.ofFun (m - movA d s) (movB d s ρ (⇑φ) (⇑ψ)) := by
  set K : ℝ := (mnb_Kdata H hm).choose with hKdef
  have hK0 : 0 ≤ K := (mnb_Kdata H hm).choose_spec.1
  have hφ := memOsc_schwartz m φ
  have hψ := memOsc_schwartz m ψ
  have hΦ : ∀ n, ∃ Φ : 𝓢R, (⇑Φ : Euc d → ℝ) = mo_pSum (⇑φ) n := fun n => by
    rw [mnb_pSum_eq_hs]; exact mov2d_hs_schwartz _
  have hΨ : ∀ n, ∃ Ψ : 𝓢R, (⇑Ψ : Euc d → ℝ) = mo_pSum (⇑ψ) n := fun n => by
    rw [mnb_pSum_eq_hs]; exact mov2d_hs_schwartz _
  choose Φ hΦ using hΦ
  choose Ψ hΨ using hΨ
  have t1 := mnb_pSum_tendsto hφ
  have t2 := mnb_pSum_tendsto hψ
  -- the image under `B_ext`
  have t3 : Tendsto (fun n => mov_B_ext H hm (OscSpace.ofFun m (mo_pSum (⇑φ) n))
      (OscSpace.ofFun m (mo_pSum (⇑ψ) n))) atTop
      (𝓝 (mov_B_ext H hm (OscSpace.ofFun m (⇑φ)) (OscSpace.ofFun m (⇑ψ)))) :=
    ((mov_B_ext H hm).continuous₂.tendsto _).comp (t1.prodMk_nhds t2)
  have e5 : ∀ n, mov_B_ext H hm (OscSpace.ofFun m (mo_pSum (⇑φ) n)) (OscSpace.ofFun m (mo_pSum (⇑ψ) n)) =
      OscSpace.ofFun (m - movA d s) (movB d s ρ (⇑(Φ n)) (⇑(Ψ n))) := fun n => by
    rw [hΦ n, hΨ n, mnb_pSum_eq_hs, mnb_pSum_eq_hs, mov_B_ext_hs]
  simp_rw [e5] at t3
  -- the function-level side converges to the same limit
  have t4 : Tendsto (fun n => OscSpace.ofFun (m - movA d s) (movB d s ρ (⇑(Φ n)) (⇑(Ψ n)))) atTop
      (𝓝 (OscSpace.ofFun (m - movA d s) (movB d s ρ (⇑φ) (⇑ψ)))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hA : ∀ n, OscSpace.ofFun m (⇑(Φ n)) = OscSpace.ofFun m (mo_pSum (⇑φ) n) := fun n => by rw [hΦ n]
    have hB : ∀ n, OscSpace.ofFun m (⇑(Ψ n)) = OscSpace.ofFun m (mo_pSum (⇑ψ) n) := fun n => by rw [hΨ n]
    have u1 : Tendsto (fun n => ‖OscSpace.ofFun m (⇑φ) - OscSpace.ofFun m (mo_pSum (⇑φ) n)‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 t1)
      simpa [norm_sub_rev] using this
    have u2 : Tendsto (fun n => ‖OscSpace.ofFun m (⇑ψ) - OscSpace.ofFun m (mo_pSum (⇑ψ) n)‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 t2)
      simpa [norm_sub_rev] using this
    have u3 : Tendsto (fun n => ‖OscSpace.ofFun m (mo_pSum (⇑φ) n)‖) atTop (𝓝 ‖OscSpace.ofFun m (⇑φ)‖) :=
      t1.norm
    have bound : ∀ n, ‖OscSpace.ofFun (m - movA d s) (movB d s ρ (⇑(Φ n)) (⇑(Ψ n))) -
        OscSpace.ofFun (m - movA d s) (movB d s ρ (⇑φ) (⇑ψ))‖ ≤
        K * ‖OscSpace.ofFun m (⇑φ) - OscSpace.ofFun m (mo_pSum (⇑φ) n)‖ * ‖OscSpace.ofFun m (⇑ψ)‖ +
          K * ‖OscSpace.ofFun m (mo_pSum (⇑φ) n)‖ *
            ‖OscSpace.ofFun m (⇑ψ) - OscSpace.ofFun m (mo_pSum (⇑ψ) n)‖ := fun n => by
      rw [norm_sub_rev]
      have := mnb_Bs_diff H hm φ (Φ n) ψ (Ψ n)
      rw [hA n, hB n] at this
      exact this
    refine squeeze_zero (fun n => norm_nonneg _) bound ?_
    have := ((u1.const_mul K).mul_const ‖OscSpace.ofFun m (⇑ψ)‖).add
      (((u3.const_mul K)).mul u2)
    simpa using this
  exact tendsto_nhds_unique t3 t4

end Main

end HRS.MS.Mov63

end
