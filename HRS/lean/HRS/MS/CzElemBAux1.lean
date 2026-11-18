import HRS.MS.CzElemAux4

/-!
# ELEM-B, part 1: pointwise estimates for the tensor absorption inequality

Packet ELEM-B (CZ development), namespace `HRS.CZ.ElemB`.  Helper lemmas are prefixed `elemb_`.

The frozen statement is `HRS.Whole.AppendixA.lp_tensor_absorption` (`AppendixAAdjoint.lean:953`).  The proof here
follows the supplement (`B:eq:tensor-absorption`), with one organisational change that removes every measurability
issue of the bare functions `μ`, `B`: Cauchy-Schwarz in `(x,z)` is replaced by the pointwise inequality
`X Y ≤ η X² + Y²/(4η)` inside the `z`-integral, so that only the (possibly non-measurable) function
`x ↦ ofReal (μ x) * 𝔡_p[W](x)` is integrated against a constant, and everything else is integrated as a measurable
function.

Notation: `m = d + θ`, `V(x) = |W(x)|`, `D(x,z) = |W(x) - W(x-z)|`, `k(z) = |z|^{1-m}` (the modulus of the odd kernel up
to `‖Ω‖_{S}`).  By `pvOdd_abs_le_loc_far` (`CzPvAux3`), for a Schwartz component `W_j`,
`|pvOdd W_j (x)| ≤ ‖Ω‖_S (Lx + Gx)` with the local part
`Lx = ∫_{|z|≤1} k(z) D(x,z) dz` and the far part `Gx = (k 1_{|z|>1} * V)(x)`.

* `elemb_amgm`: the real pointwise inequality for the local part.
* `elemb_local_bound`: `ofReal(√a V^{p-1}) Lx ≤ η ofReal(a) 𝔡_p(x) + (1/(4η)) ofReal(V^p) J`,
  `J = ∫_{|z|≤1} |z|^{2-d-θ} < ∞` (`θ < 2`).
* `elemb_far_bound`: `ofReal(√a V^{p-1}) Gx ≤ ofReal(√Λ)(ofReal(V^p) + Gx^p)` for `0 ≤ a ≤ Λ`.
* `elemb_pvOdd_le`: `ofReal|pvOdd W_j x| ≤ ofReal B (Lx + Gx)` for Schwartz `W_j`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.ElemB

open HRS.CZ.Pv HRS.CZ.ElemA
open HRS.Whole.AppendixA (vnorm dissipationDensity)

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-! ### `vnorm` -/

lemma elemb_vnorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℝ) : 0 ≤ vnorm v := Real.sqrt_nonneg _

lemma elemb_abs_le_vnorm {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) : |v i| ≤ vnorm v := by
  unfold vnorm
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _)
    (Finset.mem_univ i))

lemma elemb_sum_abs_le {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ∑ i, |v i| ≤ (Fintype.card ι : ℝ) * vnorm v := by
  calc ∑ i, |v i| ≤ ∑ _i : ι, vnorm v := Finset.sum_le_sum fun i _ => elemb_abs_le_vnorm v i
    _ = _ := by simp

lemma elemb_vnorm_continuous {ι : Type*} [Fintype ι] {α : Type*} [TopologicalSpace α] {f : ι → α → ℝ}
    (hf : ∀ i, Continuous (f i)) : Continuous fun a => vnorm (fun i => f i a) :=
  (continuous_finsetSum _ fun i _ => (hf i).pow 2).sqrt

/-! ### the real pointwise inequality -/

lemma elemb_young_real (X Y η : ℝ) (hη : 0 < η) : X * Y ≤ η * X ^ 2 + 1 / (4 * η) * Y ^ 2 := by
  have h : η * X ^ 2 + 1 / (4 * η) * Y ^ 2 - X * Y = (2 * η * X - Y) ^ 2 / (4 * η) := by
    field_simp
    ring
  have h2 : 0 ≤ (2 * η * X - Y) ^ 2 / (4 * η) := by positivity
  linarith

/-- the real inequality behind the local part: `√a V^{p-1} (t^{1-m} D) ≤ η a (S^{p-2} D²/t^m) + (V^p t^{2-m})/(4η)` -/
lemma elemb_amgm {a s v D t η p m : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) (hvs : v ≤ s) (hD : 0 ≤ D) (ht : 0 < t)
    (hη : 0 < η) (hp : 2 ≤ p) :
    √a * v ^ (p - 1) * (t ^ (1 - m) * D) ≤
      η * (a * (s ^ (p - 2) * D ^ 2 / t ^ m)) + 1 / (4 * η) * (v ^ p * t ^ (2 - m)) := by
  have hs : 0 ≤ s := hv.trans hvs
  set X : ℝ := √a * s ^ ((p - 2) / 2) * D * t ^ (-m / 2) with hX
  set Y : ℝ := v ^ (p / 2) * t ^ (1 - m / 2) with hY
  have h1 : v ^ (p - 1) ≤ s ^ ((p - 2) / 2) * v ^ (p / 2) := by
    have e : v ^ (p - 1) = v ^ ((p - 2) / 2) * v ^ (p / 2) := by
      rw [← Real.rpow_add' hv (by linarith)]
      congr 1
      ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hv hvs (by linarith)) (Real.rpow_nonneg hv _)
  have h2 : t ^ (1 - m) = t ^ (-m / 2) * t ^ (1 - m / 2) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  have hXY : √a * v ^ (p - 1) * (t ^ (1 - m) * D) ≤ X * Y := by
    have e : X * Y = √a * (s ^ ((p - 2) / 2) * v ^ (p / 2)) * (t ^ (1 - m) * D) := by
      rw [hX, hY, h2]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)) ?_
    exact mul_nonneg (Real.rpow_nonneg ht.le _) hD
  have hX2 : X ^ 2 = a * (s ^ (p - 2) * D ^ 2 / t ^ m) := by
    have e1 : (s ^ ((p - 2) / 2)) ^ 2 = s ^ (p - 2) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hs]
      congr 1
      push_cast
      ring
    have e2 : (t ^ (-m / 2)) ^ 2 = 1 / t ^ m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, one_div, ← Real.rpow_neg ht.le]
      congr 1
      push_cast
      ring
    have e3 : √a ^ 2 = a := Real.sq_sqrt ha
    calc X ^ 2 = √a ^ 2 * (s ^ ((p - 2) / 2)) ^ 2 * D ^ 2 * (t ^ (-m / 2)) ^ 2 := by rw [hX]; ring
      _ = a * (s ^ (p - 2) * D ^ 2 / t ^ m) := by rw [e1, e2, e3]; ring
  have hY2 : Y ^ 2 = v ^ p * t ^ (2 - m) := by
    have e1 : (v ^ (p / 2)) ^ 2 = v ^ p := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hv]
      congr 1
      push_cast
      ring
    have e2 : (t ^ (1 - m / 2)) ^ 2 = t ^ (2 - m) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1
      push_cast
      ring
    calc Y ^ 2 = (v ^ (p / 2)) ^ 2 * (t ^ (1 - m / 2)) ^ 2 := by rw [hY]; ring
      _ = _ := by rw [e1, e2]
  have := elemb_young_real X Y η hη
  rw [hX2, hY2] at this
  exact hXY.trans this


/-! ### the data attached to a tensor field -/

section Tensor

variable {ι : Type*} [Fintype ι]

/-- `V(x) = |W(x)|` -/
def elemb_V (W : ι → 𝓢(𝔼, ℝ)) (x : 𝔼) : ℝ := vnorm (fun i => W i x)

/-- `D(x,z) = |W(x) - W(x-z)|` -/
def elemb_Dd (W : ι → 𝓢(𝔼, ℝ)) (x z : 𝔼) : ℝ := vnorm (fun i => W i x - W i (x - z))

lemma elemb_V_nonneg (W : ι → 𝓢(𝔼, ℝ)) (x : 𝔼) : 0 ≤ elemb_V W x := elemb_vnorm_nonneg _

lemma elemb_Dd_nonneg (W : ι → 𝓢(𝔼, ℝ)) (x z : 𝔼) : 0 ≤ elemb_Dd W x z := elemb_vnorm_nonneg _

lemma elemb_V_continuous (W : ι → 𝓢(𝔼, ℝ)) : Continuous (elemb_V W) :=
  elemb_vnorm_continuous (f := fun i x => W i x) fun i => (W i).continuous

lemma elemb_V_measurable (W : ι → 𝓢(𝔼, ℝ)) : Measurable (elemb_V W) := (elemb_V_continuous W).measurable

/-- local part `Lx = ∫_{|z|≤1} |z|^{1-m} D(x,z) dz` -/
def elemb_Lx (θ : ℝ) (W : ι → 𝓢(𝔼, ℝ)) (x : 𝔼) : ℝ≥0∞ :=
  ∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal (‖z‖ ^ (1 - ((d : ℝ) + θ)) * elemb_Dd W x z)

/-- far part `Gx = (k 1_{|z|>1} * V)(x)`, `k = |z|^{1-m}` -/
def elemb_Gx (θ : ℝ) (W : ι → 𝓢(𝔼, ℝ)) (x : 𝔼) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (elema_kfar d ((d : ℝ) + θ - 1) 1 z) * ENNReal.ofReal (elemb_V W (x - z))

/-- `J = ∫_{|z|≤1} |z|^{2-m}` -/
def elemb_J (d : ℕ) (θ : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in closedBall (0 : EuclideanSpace ℝ (Fin d)) 1, ENNReal.ofReal (‖z‖ ^ (2 - ((d : ℝ) + θ)))

lemma elemb_J_ne_top (hd : 1 ≤ d) {θ : ℝ} (hθ2 : θ < 2) : elemb_J d θ ≠ ⊤ := by
  have hi : Integrable (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 2))) (volume.restrict (closedBall 0 1)) := by
    have : IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 2))) (ball 0 2) :=
      pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) + θ - 2) (by linarith) 2
    exact this.mono_set (closedBall_subset_ball (by norm_num))
  have e : ∀ z : 𝔼, ‖z‖ ^ (2 - ((d : ℝ) + θ)) = ‖z‖ ^ (-((d : ℝ) + θ - 2)) := fun z => by
    congr 1; ring
  unfold elemb_J
  simp_rw [e]
  exact hi.lintegral_lt_top.ne

lemma elemb_Gx_measurable (θ : ℝ) (W : ι → 𝓢(𝔼, ℝ)) : Measurable (elemb_Gx θ W) := by
  unfold elemb_Gx
  have hk : Measurable (elema_kfar d ((d : ℝ) + θ - 1) 1) := elema_kfar_measurable _ _
  have hf : Measurable (fun q : 𝔼 × 𝔼 =>
      ENNReal.ofReal (elema_kfar d ((d : ℝ) + θ - 1) 1 q.2) * ENNReal.ofReal (elemb_V W (q.1 - q.2))) :=
    (ENNReal.measurable_ofReal.comp (hk.comp measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp ((elemb_V_measurable W).comp (measurable_fst.sub measurable_snd)))
  exact hf.lintegral_prod_right'

/-! ### the far part: Young's inequality -/

lemma elemb_Gx_young (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) {p : ℝ} (hp : 1 ≤ p) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ W : ι → 𝓢(𝔼, ℝ),
      ∫⁻ x, elemb_Gx θ W x ^ p ≤ ENNReal.ofReal (Ck ^ p) * ∫⁻ x, ENNReal.ofReal (elemb_V W x ^ p) := by
  obtain ⟨Ck, hCk, hint⟩ := elema_kfar_lintegral hd (s := (d : ℝ) + θ - 1) (by linarith)
  refine ⟨Ck, hCk, fun W => ?_⟩
  have hy := HRS.Commutator.Whole.XLI.young_lintegral (d := d)
    (a := fun z => ENNReal.ofReal (elema_kfar d ((d : ℝ) + θ - 1) 1 z))
    (b := fun z => ENNReal.ofReal (elemb_V W z))
    (ENNReal.measurable_ofReal.comp (elema_kfar_measurable _ _))
    (ENNReal.measurable_ofReal.comp (elemb_V_measurable W)) hp
  have h1 := hint 1 zero_le_one
  rw [mul_one] at h1
  have hp0 : (0 : ℝ) ≤ p := by linarith
  refine hy.trans ?_
  have e : ∀ x : 𝔼, ENNReal.ofReal (elemb_V W x) ^ p = ENNReal.ofReal (elemb_V W x ^ p) := fun x =>
    ENNReal.ofReal_rpow_of_nonneg (elemb_V_nonneg W x) hp0
  simp_rw [e]
  rw [← ENNReal.ofReal_rpow_of_nonneg hCk hp0]
  exact mul_le_mul' (ENNReal.rpow_le_rpow h1 hp0) le_rfl

/-! ### the ENNReal Young inequality `a^{p-1} G ≤ a^p + G^p` -/

lemma elemb_enn_mul_le {a G : ℝ≥0∞} {p : ℝ} (hp : 1 ≤ p) : a ^ (p - 1) * G ≤ a ^ p + G ^ p := by
  have hp1 : 0 ≤ p - 1 := by linarith
  have hpa : a ^ p = a ^ (p - 1) * a := by
    have := ENNReal.rpow_add_of_nonneg (x := a) (p - 1) 1 hp1 zero_le_one
    rw [ENNReal.rpow_one] at this
    rw [← this]; congr 1; ring
  have hpG : G ^ p = G ^ (p - 1) * G := by
    have := ENNReal.rpow_add_of_nonneg (x := G) (p - 1) 1 hp1 zero_le_one
    rw [ENNReal.rpow_one] at this
    rw [← this]; congr 1; ring
  rcases le_total a G with h | h
  · calc a ^ (p - 1) * G ≤ G ^ (p - 1) * G := mul_le_mul' (ENNReal.rpow_le_rpow h hp1) le_rfl
      _ = G ^ p := hpG.symm
      _ ≤ _ := le_add_self
  · calc a ^ (p - 1) * G ≤ a ^ (p - 1) * a := mul_le_mul' le_rfl h
      _ = a ^ p := hpa.symm
      _ ≤ _ := le_self_add

/-! ### local and far bounds at a point -/

lemma elemb_pt_real (hd : 1 ≤ d) {θ p a η : ℝ} (hθ0 : 0 < θ) (hp : 2 ≤ p) (ha : 0 ≤ a) (hη : 0 < η)
    (W : ι → 𝓢(𝔼, ℝ)) (x z : 𝔼) :
    √a * elemb_V W x ^ (p - 1) * (‖z‖ ^ (1 - ((d : ℝ) + θ)) * elemb_Dd W x z) ≤
      η * (a * ((elemb_V W x + elemb_V W (x - z)) ^ (p - 2) * elemb_Dd W x z ^ 2 / ‖z‖ ^ ((d : ℝ) + θ))) +
        1 / (4 * η) * (elemb_V W x ^ p * ‖z‖ ^ (2 - ((d : ℝ) + θ))) := by
  have hV := elemb_V_nonneg W x
  have hV' := elemb_V_nonneg W (x - z)
  by_cases hz : z = 0
  · subst hz
    have h1 : (d : ℝ) + θ - 1 ≠ 0 := (pvapi_exp_pos hd hθ0).ne'
    have e : (‖(0 : 𝔼)‖) ^ (1 - ((d : ℝ) + θ)) = 0 := by
      rw [norm_zero]
      exact Real.zero_rpow (by intro h; apply h1; linarith)
    rw [e, zero_mul, mul_zero]
    have : 0 ≤ η * (a * ((elemb_V W x + elemb_V W (x - 0)) ^ (p - 2) * elemb_Dd W x 0 ^ 2 /
        ‖(0 : 𝔼)‖ ^ ((d : ℝ) + θ))) := by
      have := elemb_Dd_nonneg W x 0
      positivity
    have h3 : 0 ≤ 1 / (4 * η) * (elemb_V W x ^ p * ‖(0 : 𝔼)‖ ^ (2 - ((d : ℝ) + θ))) := by positivity
    linarith
  · exact elemb_amgm ha hV (le_add_of_nonneg_right hV') (elemb_Dd_nonneg W x z) (norm_pos_iff.2 hz) hη hp

lemma elemb_dissip_eq {θ p : ℝ} (W : ι → 𝓢(𝔼, ℝ)) (x : 𝔼) :
    dissipationDensity d θ p (fun y i => W i y) x =
      ∫⁻ z : 𝔼, ENNReal.ofReal ((elemb_V W x + elemb_V W (x - z)) ^ (p - 2) * elemb_Dd W x z ^ 2 /
        ‖z‖ ^ ((d : ℝ) + θ)) := rfl

lemma elemb_local_bound (hd : 1 ≤ d) {θ p a η : ℝ} (hθ0 : 0 < θ) (hp : 2 ≤ p) (ha : 0 ≤ a) (hη : 0 < η)
    (W : ι → 𝓢(𝔼, ℝ)) (x : 𝔼) :
    ENNReal.ofReal (√a * elemb_V W x ^ (p - 1)) * elemb_Lx θ W x ≤
      ENNReal.ofReal η * (ENNReal.ofReal a * dissipationDensity d θ p (fun y i => W i y) x) +
        ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) * elemb_J d θ) := by
  have hV := elemb_V_nonneg W x
  have hB : 0 ≤ √a * elemb_V W x ^ (p - 1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hV _)
  unfold elemb_Lx
  rw [← pvapi_ofReal_B_mul _ hB (fun z => ‖z‖ ^ (1 - ((d : ℝ) + θ)) * elemb_Dd W x z)]
  have hpt : ∀ z : 𝔼, ENNReal.ofReal (√a * elemb_V W x ^ (p - 1) *
      (‖z‖ ^ (1 - ((d : ℝ) + θ)) * elemb_Dd W x z)) ≤
      ENNReal.ofReal η * (ENNReal.ofReal a * ENNReal.ofReal ((elemb_V W x + elemb_V W (x - z)) ^ (p - 2) *
        elemb_Dd W x z ^ 2 / ‖z‖ ^ ((d : ℝ) + θ))) +
      ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) *
        ENNReal.ofReal (‖z‖ ^ (2 - ((d : ℝ) + θ)))) := fun z => by
    have h := elemb_pt_real hd hθ0 hp ha hη W x z
    have hS : 0 ≤ (elemb_V W x + elemb_V W (x - z)) ^ (p - 2) * elemb_Dd W x z ^ 2 / ‖z‖ ^ ((d : ℝ) + θ) := by
      have := elemb_V_nonneg W (x - z)
      have := elemb_Dd_nonneg W x z
      positivity
    have h2 : 0 ≤ ‖z‖ ^ (2 - ((d : ℝ) + θ)) := Real.rpow_nonneg (norm_nonneg _) _
    have h3 : 0 ≤ elemb_V W x ^ p := Real.rpow_nonneg hV _
    calc ENNReal.ofReal (√a * elemb_V W x ^ (p - 1) * (‖z‖ ^ (1 - ((d : ℝ) + θ)) * elemb_Dd W x z))
        ≤ ENNReal.ofReal (η * (a * ((elemb_V W x + elemb_V W (x - z)) ^ (p - 2) * elemb_Dd W x z ^ 2 /
          ‖z‖ ^ ((d : ℝ) + θ))) + 1 / (4 * η) * (elemb_V W x ^ p * ‖z‖ ^ (2 - ((d : ℝ) + θ)))) :=
          ENNReal.ofReal_le_ofReal h
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hη.le,
          ENNReal.ofReal_mul ha, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul h3]
  have hgm : Measurable (fun z : 𝔼 => ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) *
      ENNReal.ofReal (‖z‖ ^ (2 - ((d : ℝ) + θ))))) :=
    measurable_const.mul (measurable_const.mul
      (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)))
  calc ∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal (√a * elemb_V W x ^ (p - 1) *
        (‖z‖ ^ (1 - ((d : ℝ) + θ)) * elemb_Dd W x z))
      ≤ ∫⁻ z in closedBall (0 : 𝔼) 1, (ENNReal.ofReal η * (ENNReal.ofReal a *
        ENNReal.ofReal ((elemb_V W x + elemb_V W (x - z)) ^ (p - 2) *
        elemb_Dd W x z ^ 2 / ‖z‖ ^ ((d : ℝ) + θ))) +
        ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) *
        ENNReal.ofReal (‖z‖ ^ (2 - ((d : ℝ) + θ))))) := lintegral_mono hpt
    _ = (∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal η * (ENNReal.ofReal a *
        ENNReal.ofReal ((elemb_V W x + elemb_V W (x - z)) ^ (p - 2) *
        elemb_Dd W x z ^ 2 / ‖z‖ ^ ((d : ℝ) + θ)))) +
        ∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) *
        ENNReal.ofReal (‖z‖ ^ (2 - ((d : ℝ) + θ)))) := lintegral_add_right _ hgm
    _ ≤ ENNReal.ofReal η * (ENNReal.ofReal a * dissipationDensity d θ p (fun y i => W i y) x) +
        ENNReal.ofReal (1 / (4 * η)) * (ENNReal.ofReal (elemb_V W x ^ p) * elemb_J d θ) := by
        refine add_le_add ?_ ?_
        · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            elemb_dissip_eq]
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _))
        · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          rfl

lemma elemb_far_bound {p Λ a : ℝ} (hp : 2 ≤ p) (ha : 0 ≤ a) (haΛ : a ≤ Λ) (W : ι → 𝓢(𝔼, ℝ)) (x : 𝔼) (θ : ℝ) :
    ENNReal.ofReal (√a * elemb_V W x ^ (p - 1)) * elemb_Gx θ W x ≤
      ENNReal.ofReal (√Λ) * (ENNReal.ofReal (elemb_V W x ^ p) + elemb_Gx θ W x ^ p) := by
  have hV := elemb_V_nonneg W x
  have hp1 : 0 ≤ p - 1 := by linarith
  have e1 : ENNReal.ofReal (√a * elemb_V W x ^ (p - 1)) =
      ENNReal.ofReal (√a) * ENNReal.ofReal (elemb_V W x) ^ (p - 1) := by
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_rpow_of_nonneg hV hp1]
  have e2 : ENNReal.ofReal (elemb_V W x ^ p) = ENNReal.ofReal (elemb_V W x) ^ p :=
    (ENNReal.ofReal_rpow_of_nonneg hV (by linarith)).symm
  rw [e1, e2, mul_assoc]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt haΛ)) (elemb_enn_mul_le (by linarith))

/-- the pointwise bound of `pvOdd` of one Schwartz component -/
lemma elemb_pvOdd_le (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) (W : ι → 𝓢(𝔼, ℝ)) (j : ι) (x : 𝔼) :
    ENNReal.ofReal |HRS.Whole.AppendixA.pvOdd d θ Ω (fun y => W j y) x| ≤
      ENNReal.ofReal B * (elemb_Lx θ W x + elemb_Gx θ W x) := by
  obtain ⟨B1, L, M, hf⟩ := PvC2.of_schwartz (W j)
  have h := pvOdd_abs_le_loc_far hd hθ0 hθ2 hK hf.lipschitzWith x
  refine h.trans ?_
  rw [mul_add]
  refine add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_)
  · unfold elemb_Lx
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (norm_nonneg _) _)
    have := elemb_abs_le_vnorm (fun i => W i x - W i (x - z)) j
    rw [abs_sub_comm]
    exact this
  · unfold elemb_Gx
    rw [← lintegral_indicator pvapi_tail_meas]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ {z : 𝔼 | 1 < ‖z‖}
    · rw [Set.indicator_of_mem hz]
      have hk : elema_kfar d ((d : ℝ) + θ - 1) 1 z = ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by
        unfold elema_kfar
        rw [Set.indicator_of_mem hz, one_mul]
        congr 1; ring
      rw [hk, ← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (norm_nonneg _) _))
      exact elemb_abs_le_vnorm (fun i => W i (x - z)) j
    · rw [Set.indicator_of_notMem hz]
      exact zero_le

end Tensor

end HRS.CZ.ElemB
