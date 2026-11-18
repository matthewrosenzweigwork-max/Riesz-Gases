import Mathlib
import HRS.MS.PoisLipAux1
import HRS.MS.PoisKolmAux2
import HRS.MS.PoisMarkovAux2

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace NNReal

/-!
# POIS-LIPDEC (part 2): the differential inequality at a penalised maximum point, `P_t L = L P_t`

* `ld_step`: at a spatial maximum of `u x - u y - A' f|x-y| - ε'(1+|x|²+|y|²)` with `x ≠ y`, the generator
  satisfies `L u(x) - L u(y) ≤ A'(4 f'' + c f') + ε' (4d + 2 Mb)(1+|x|²+|y|²)` where `c = pm_c q Mb`
  is the drift coefficient of `pm_ffun` (`-q r + ⟪e, B x - B y⟫ ≤ c(r)`, using `‖B‖ ≤ Mb` and
  `Lip B ≤ Mb`).
* `ld_sg_zero`: `sg 0 h = h`.
* `ld_L_commute`: `∂_t sg t h = L (sg t h)`, i.e. `sg t (L h) = L (sg t h)` for `h ∈ C²` with bounded
  `h, Dh, D²h` (the commutation `P_t L = L P_t` which `PoisKolmAux2` leaves out; it follows from the Markov
  property and `pois_kolmogorov` applied to `sg t h`).
Helper lemmas carry the prefix `ld_`.
-/

namespace HRS.MS.PoisLip

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.PoisFlow HRS.MS.PoisSg
  HRS.MS.PoisMarkov HRS.MS.PoisKolm HRS.MS.PoisMax

variable {d : ℕ}

theorem ld_bracket {q Mb r s : ℝ} (hq : 0 < q) (hr : 0 ≤ r) (h1 : s ≤ Mb * r)
    (h2 : s ≤ 2 * Mb) : -(q * r) + s ≤ pm_c q Mb r := by
  unfold pm_c
  split_ifs with h
  · unfold pm_Kc
    nlinarith
  · push Not at h
    unfold pm_R at h
    have h3 : 4 * Mb / q ≤ r - 1 := by linarith
    have h4 : 4 * Mb ≤ q * (r - 1) := by
      have := mul_le_mul_of_nonneg_left h3 hq.le
      rwa [mul_div_cancel₀ _ hq.ne'] at this
    nlinarith

theorem ld_step {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) (hd : 1 ≤ d) {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioi 0)) {A' ε' : ℝ} (hA' : 0 ≤ A') (hε' : 0 ≤ ε') {x y : Euc d}
    (hf0 : 0 ≤ deriv f ‖x - y‖) (hxy : x ≠ y)
    (hmax : ∀ x' y' : Euc d,
      u x' - u y' - A' * f ‖x' - y'‖ - ε' * ‖x'‖ ^ 2 - ε' * ‖y'‖ ^ 2 + (-ε') ≤
      u x - u y - A' * f ‖x - y‖ - ε' * ‖x‖ ^ 2 - ε' * ‖y‖ ^ 2 + (-ε')) :
    kolmL q B u x - kolmL q B u y ≤
      A' * (4 * deriv (deriv f) ‖x - y‖ + pm_c q Mb ‖x - y‖ * deriv f ‖x - y‖)
        + ε' * (4 * d + 2 * Mb) * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  obtain ⟨hfo, hlap⟩ := ld_maxpoint_pen hd u hu A' ε' ε' f hf x y (-ε') hmax hxy
  have hMb : 0 ≤ Mb := (norm_nonneg _).trans (by simpa using hB.2 0 (Nat.zero_le _) 0)
  have hBb : ∀ z, ‖B z‖ ≤ Mb := fun z => by simpa using hB.2 0 (Nat.zero_le _) z
  have hBl := pf_lip_of_cb (by omega : 1 ≤ m) hB
  set r : ℝ := ‖x - y‖ with hr
  have hrpos : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  set e : Euc d := r⁻¹ • (x - y) with he
  have hen : ‖e‖ = 1 := by
    rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hrpos.ne']
  have hexy : inner ℝ e (x - y) = r := by
    rw [he, real_inner_smul_left, real_inner_self_eq_norm_sq, ← hr]
    field_simp
  set D : ℝ := deriv f r with hD
  have e1 : ∀ z, kolmL q B u z = Laplacian.laplacian u z + fderiv ℝ u z (-q • z + B z) := by
    intro z; unfold kolmL; rw [kl_inner_gradient]
  rw [e1, e1]
  obtain ⟨hx1, -⟩ := hfo (-q • x + B x)
  obtain ⟨-, hy1⟩ := hfo (-q • y + B y)
  rw [hx1, hy1]
  -- the pairing with e
  have hs : inner ℝ e (-q • x + B x) - inner ℝ e (-q • y + B y) = -(q * r) + inner ℝ e (B x - B y) := by
    rw [← inner_sub_right, show -q • x + B x - (-q • y + B y) = -q • (x - y) + (B x - B y) by module,
      inner_add_right, inner_smul_right, hexy]
    ring
  have hB1 : inner ℝ e (B x - B y) ≤ Mb * r := by
    refine (real_inner_le_norm _ _).trans ?_
    rw [hen, one_mul]; exact hBl x y
  have hB2 : inner ℝ e (B x - B y) ≤ 2 * Mb := by
    refine (real_inner_le_norm _ _).trans ?_
    rw [hen, one_mul]
    exact (norm_sub_le _ _).trans (by linarith [hBb x, hBb y])
  have hbr := ld_bracket hq hrpos.le hB1 hB2
  have hxb : inner ℝ x (-q • x + B x) ≤ Mb * ‖x‖ := by
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have : inner ℝ x (B x) ≤ ‖x‖ * Mb := (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hBb x) (norm_nonneg _))
    nlinarith [sq_nonneg ‖x‖]
  have hyb : inner ℝ y (-q • y + B y) ≤ Mb * ‖y‖ := by
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have : inner ℝ y (B y) ≤ ‖y‖ * Mb := (real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hBb y) (norm_nonneg _))
    nlinarith [sq_nonneg ‖y‖]
  have hdr : A' * D * (inner ℝ e (-q • x + B x) - inner ℝ e (-q • y + B y)) ≤
      A' * (pm_c q Mb r * D) := by
    rw [hs]
    have := mul_le_mul_of_nonneg_left hbr (mul_nonneg hA' hf0)
    calc _ ≤ A' * D * pm_c q Mb r := this
      _ = _ := by ring
  have hnx : ‖x‖ ≤ (1 + ‖x‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
  have hny : ‖y‖ ≤ (1 + ‖y‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  have hS : 0 ≤ (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by positivity
  have hd0 : (0:ℝ) ≤ d := Nat.cast_nonneg d
  have hq1 : ε' * (2 * (inner ℝ x (-q • x + B x) + inner ℝ y (-q • y + B y))) ≤
      ε' * (2 * Mb * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hε'
    nlinarith [mul_le_mul_of_nonneg_left hnx hMb, mul_le_mul_of_nonneg_left hny hMb]
  have hq2 : ε' * (4 * d) ≤ ε' * (4 * d) * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    have : 1 ≤ 1 + ‖x‖ ^ 2 + ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]
    have h0 : 0 ≤ ε' * (4 * d) := by positivity
    calc ε' * (4 * d) = ε' * (4 * d) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this h0
  have e4 : ε' * (4 * d) * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) + ε' * (2 * Mb * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2)) =
      ε' * (4 * d + 2 * Mb) * (1 + ‖x‖ ^ 2 + ‖y‖ ^ 2) := by ring
  have e5 : 2 * (d:ℝ) * (ε' + ε') = ε' * (4 * d) := by ring
  rw [e5] at hlap
  have e6 : A' * (4 * deriv (deriv f) r) = 4 * A' * deriv (deriv f) r := by ring
  have e7 : A' * (4 * deriv (deriv f) r + pm_c q Mb r * D) =
      A' * (4 * deriv (deriv f) r) + A' * (pm_c q Mb r * D) := by ring
  rw [e7, e6]
  linarith [hlap, hdr, hq1, hq2, e4]

/-! ### `sg 0 = id` and `P_t L = L P_t` -/

section Semigroup

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem ld_sg_zero [IsProbabilityMeasure P] (hW : SgNoise W) {q Mb : ℝ} (hq : 0 ≤ q) {m : ℕ}
    (hm : 1 ≤ m) {B : Euc d → Euc d} (hB : HasCbBound m Mb B) (h : Euc d → ℝ) (x : Euc d) :
    sg P W q B 0 h x = h x := by
  unfold sg
  have : ∀ ω, flowMap q B (fun s => W s ω) 0 x = x := fun ω => by
    have H : PfHyp q Mb m B (fun s => W s ω) := ⟨hq, hm, hB, hW.cont ω, hW.zero ω⟩
    unfold flowMap
    rw [pf_Z_zero H, pf_ou_zero (hW.zero ω)]
    simp
  simp [this]

/-- `P_t L h = L P_t h` for `h ∈ C²` with bounded `h, Dh, D²h`. -/
theorem ld_L_commute {q Mb : ℝ} (hq : 0 < q) {m : ℕ} (hm : 2 ≤ m) {B : Euc d → Euc d}
    (hB : HasCbBound m Mb B) [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {h : Euc d → ℝ} (hh : ContDiff ℝ 2 h) {M : ℝ}
    (hM : ∀ i ≤ 2, ∀ y, ‖iteratedFDeriv ℝ i h y‖ ≤ M) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    sg P W q B t (kolmL q B h) x = kolmL q B (sg P W q B t h) x := by
  have hm1 : 1 ≤ m := by omega
  have hn := sgNoise_of_brownian hW
  obtain ⟨C, hC1, hC⟩ := sg_contDiff (d := d) q Mb hq m hm t ht 2 hm
  obtain ⟨hv, -, hvb⟩ := hC P W hn B hB h (by exact_mod_cast hh) M hM t ⟨ht, le_rfl⟩
  have hv2 : ContDiff ℝ 2 (sg P W q B t h) := by exact_mod_cast hv
  have hM1 : ∀ y, ‖fderiv ℝ (sg P W q B t h) y‖ ≤ C * M := fun y => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]; exact hvb 1 (by norm_num) y
  have hM2 : ∀ y, ‖iteratedFDeriv ℝ 2 (sg P W q B t h) y‖ ≤ C * M := fun y => hvb 2 le_rfl y
  have hK := (pois_kolmogorov hq hm hB hW hv2 hM1 hM2).2.1 x 0 le_rfl
  rw [ld_sg_zero hn hq.le hm1 hB] at hK
  have hh1 : ∀ y, ‖fderiv ℝ h y‖ ≤ M := fun y => by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]; exact hM 1 (by norm_num) y
  have hh2 : ∀ y, ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ M := fun y => by
    rw [kl_norm_fderiv_fderiv']; exact hM 2 le_rfl y
  have hK2 := kl_hasDerivWithinAt hq hm hB hW hh hh1 hh2 x ht
  have hK3 : HasDerivWithinAt (fun s : ℝ => sg P W q B (s + t) h x)
      (sg P W q B t (kolmL q B h) x) (Ici 0) 0 := by
    have hid : HasDerivWithinAt (fun s : ℝ => s + t) 1 (Ici 0) 0 :=
      (hasDerivWithinAt_id 0 _).add_const t
    have := (show HasDerivWithinAt (fun s => sg P W q B s h x) _ (Ici 0) (0 + t) by
      simpa using hK2).comp 0 hid (fun s hs => by simpa using add_nonneg (show (0:ℝ) ≤ s from hs) ht)
    rw [mul_one] at this
    exact this
  have hK4 : HasDerivWithinAt (fun s : ℝ => sg P W q B s (sg P W q B t h) x)
      (sg P W q B t (kolmL q B h) x) (Ici 0) 0 := by
    refine hK3.congr (fun s hs => ?_) ?_
    · exact (sg_markov_C2 hW hq.le hm1 hB hh hM (show (0:ℝ) ≤ s from hs) ht x).symm
    · exact (sg_markov_C2 hW hq.le hm1 hB hh hM (le_refl (0:ℝ)) ht x).symm
  have := hK4.derivWithin (uniqueDiffWithinAt_Ici 0)
  rw [hK.derivWithin (uniqueDiffWithinAt_Ici 0)] at this
  exact this.symm

end Semigroup

end HRS.MS.PoisLip
