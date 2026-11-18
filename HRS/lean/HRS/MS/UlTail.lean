import HRS.MS.UlTailAux2
import HRS.Whole.Adjoint

/-!
# UL-T (S5.1 convolution tails and orbit data): the statements

Infrastructure packet UL-T (supplement `W:r2:convolution-tail`, S L3300-3320; `W:r2:orbit-bounds`
data); not a manuscript row.  `K h = convGradConvW (rieszKernelGrad d s) h` is the cancellation
convolution `∇g * h` (the Bochner integral is a genuine integral: integrability is part of the
conclusion).

* `ult_conv_comp`: componentwise, `(K h) i = ultK (u2_kap d s i) h` and the integrand of `K h` is integrable.
* `tail_conv` (Schwartz `h`, `d ≥ 2`, `0 ≤ s < d`): `K h` is `C^∞`; `‖D^b (K h)(x)‖ ≤ C_b (1+‖x‖)^{-(s+1+b)}`
  (hence every derivative is bounded); the commutation `D (K h)_i = ultK κ_i (D h)`, i.e.
  `fderiv ℝ (fun x => (K h x) i) x v = ultK (u2_kap d s i) (fun y => fderiv ℝ h y v) x`, and
  `ult_conv_comp` identifies the right side with `K (∂_v h)` whenever `∂_v h` has the `U2Dec` bounds.
  The same holds for the class `UlRapid` (`tail_conv_rapid`).
* `part2_c_smoothBounded`: `IsSmoothBounded (fun x => σ x - K ρ x)` for Schwartz `ρ` and vector Schwartz `σ`.
* `orbitData_decay`: for Schwartz `f`, `L = generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0`, `c = σ - K ρ`,
  every `L^a f` is `C^∞` with `‖D^m (L^a f)(x)‖ ≤ C (1+‖x‖)^{-(s+1+m)}` (so all derivatives tend to `0`).

Helper lemmas carry the prefix `ult_`; namespace `HRS.MS.Ul`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.Ul

open HRS HRS.Whole

variable {d : ℕ}

/-- The integrand of `convGradConvW`. -/
def ultInt (s : ℝ) (h : Euc d → ℝ) (x y : Euc d) : Euc d :=
  if ‖x - y‖ ≤ 1 / 4 then (h y - h x) • rieszKernelGrad d s (x - y)
  else h y • rieszKernelGrad d s (x - y)

lemma ult_conv_unfold (s : ℝ) (h : Euc d → ℝ) (x : Euc d) :
    convGradConvW (rieszKernelGrad d s) h x = ∫ y, ultInt s h x y := rfl

lemma ult_int_meas (s : ℝ) {h : Euc d → ℝ} (hc : Continuous h) (x : Euc d) :
    AEStronglyMeasurable (ultInt s h x) volume := by
  refine Measurable.aestronglyMeasurable ?_
  refine Measurable.ite (measurableSet_le (measurable_const.sub measurable_id).norm
    measurable_const) ?_ ?_
  · exact (hc.measurable.sub measurable_const).smul
      ((u2_K_measurable s).comp (measurable_const.sub measurable_id))
  · exact hc.measurable.smul ((u2_K_measurable s).comp (measurable_const.sub measurable_id))

lemma ult_conv_comp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {L A : ℝ}
    (hL : (d : ℝ) < L) (hA : 0 ≤ A) {h : Euc d → ℝ} (hdec : U2Dec 1 L A h) (x : Euc d) :
    Integrable (ultInt s h x) volume ∧
      ∀ i : Fin d, convGradConvW (rieszKernelGrad d s) h x i = ultK (u2_kap d s i) h x := by
  have hker := fun i : Fin d => ult_ker_kap hs0 hsd i
  have hF : ∀ (i : Fin d) (y : Euc d), ultInt s h x y i =
      (fun z => ultKN (u2_kap d s i) z • (h (x - z) - h x) +
        ultKF (u2_kap d s i) z • h (x - z)) (x - y) := by
    intro i y
    simp only [sub_sub_cancel, ultInt, ultKN, ultKF, u2_kap]
    by_cases hy : ‖x - y‖ ≤ 1 / 4
    · simp only [if_pos hy, PiLp.smul_apply, smul_eq_mul, zero_smul, add_zero]; ring
    · simp only [if_neg hy, PiLp.smul_apply, smul_eq_mul, zero_smul, zero_add]; ring
  have hint : ∀ i : Fin d, Integrable (fun y => ultInt s h x y i) volume := by
    intro i
    obtain ⟨n, f⟩ := ult_K_integrable hd (hker i) hL hA hdec x
    have := (n.add f).comp_sub_left x
    exact this.congr (Filter.Eventually.of_forall fun y => (hF i y).symm)
  have hI : Integrable (ultInt s h x) volume :=
    u2_integrable_of_coord (ult_int_meas s hdec.1.continuous x) hint
  refine ⟨hI, fun i => ?_⟩
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) hI
  rw [ult_conv_unfold]
  have e1 : (∫ y, ultInt s h x y) i = ∫ y, ultInt s h x y i := by simpa using this.symm
  rw [e1]
  simp only [hF i]
  rw [integral_sub_left_eq_self (fun z => ultKN (u2_kap d s i) z • (h (x - z) - h x) +
    ultKF (u2_kap d s i) z • h (x - z)) volume x]
  obtain ⟨n, f⟩ := ult_K_integrable hd (hker i) hL hA hdec x
  rw [integral_add n f]
  rfl

/-! ### The class of rapidly decreasing smooth functions and Schwartz functions -/

lemma ult_schwartz_rapid (h : SchwartzMap (Euc d) ℝ) : UlRapid (d := d) ⇑h := by
  refine ⟨h.smooth _, fun m N => ?_⟩
  refine ⟨2 ^ N * (Finset.Iic (N, m)).sup (schwartzSeminormFamily ℝ (Euc d) ℝ) h, fun x => ?_⟩
  exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, m)) (k := N) (n := m)
    le_rfl le_rfl h x

lemma ult_norm_le_sum_abs (w : Euc d) : ‖w‖ ≤ ∑ i, |w i| := by
  have hv : w = ∑ i : Fin d, (w i) • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  calc ‖w‖ = ‖∑ i : Fin d, (w i) • (EuclideanSpace.single i (1 : ℝ) : Euc d)‖ := by rw [← hv]
    _ ≤ ∑ i : Fin d, ‖(w i) • (EuclideanSpace.single i (1 : ℝ) : Euc d)‖ := norm_sum_le _ _
    _ = ∑ i, |w i| := by simp [norm_smul]

/-- The derivatives of a vector valued function are bounded by those of its components. -/
lemma ult_norm_iter_le_sum {c : Euc d → Euc d} (hc : ContDiff ℝ ∞ c) (j : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j c x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => c y i) x‖ := by
  have hcomp : ∀ i : Fin d, iteratedFDeriv ℝ j (fun y => c y i) x =
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).compContinuousMultilinearMap
        (iteratedFDeriv ℝ j c x) := by
    intro i
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).iteratedFDeriv_comp_left
      (hc.contDiffAt) (by exact_mod_cast le_top)
  refine ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) ?_
  intro v
  calc ‖iteratedFDeriv ℝ j c x v‖ ≤ ∑ i, |(iteratedFDeriv ℝ j c x v) i| := ult_norm_le_sum_abs _
    _ ≤ ∑ i, ‖iteratedFDeriv ℝ j (fun y => c y i) x‖ * ∏ l, ‖v l‖ := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := (iteratedFDeriv ℝ j (fun y => c y i) x).le_opNorm v
        rw [hcomp i] at this ⊢
        simpa using this
    _ = (∑ i, ‖iteratedFDeriv ℝ j (fun y => c y i) x‖) * ∏ l, ‖v l‖ := by rw [Finset.sum_mul]

/-! ### `tail_conv` -/

lemma ult_K_iter_apply (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) {L A : ℝ}
    (hL : (d : ℝ) < L) (hA : 0 ≤ A) {k : ℕ} {h : Euc d → ℝ} (hdec : U2Dec (k + 1) L A h)
    {m : ℕ} (hm : m ≤ k) (v : Fin m → Euc d) (x : Euc d) :
    iteratedFDeriv ℝ m (ultK κ h) x v = ultK κ (fun y => iteratedFDeriv ℝ m h y v) x := by
  have hL0 := u2_wt_L0 hL
  obtain ⟨hit, _⟩ := ult_K_iter hd hK hL hA hdec
  rw [hit m hm x]
  have hcm : Continuous (iteratedFDeriv ℝ m h) :=
    hdec.1.continuous_iteratedFDeriv (by exact_mod_cast (by omega : m ≤ k + 1))
  have hn := ult_near_integrable hd hK hcm hA (ult_iter_lip hL0 hA hdec (by omega)) x
  have hf := u2_conv_integrable (ult_far_U2Ker hd hK) hL hcm hA (hdec.2 m (by omega)) x
  have := ult_K_clm (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Euc d) ℝ v)
    κ (iteratedFDeriv ℝ m h) x hn hf
  exact this

theorem tail_conv_rapid (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {h : Euc d → ℝ}
    (hh : UlRapid h) :
    (∀ x, Integrable (ultInt s h x) volume) ∧
    ContDiff ℝ ∞ (convGradConvW (rieszKernelGrad d s) h) ∧
    (∀ b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d,
      ‖iteratedFDeriv ℝ b (convGradConvW (rieszKernelGrad d s) h) x‖ ≤
        C * (1 + ‖x‖) ^ (-(s + 1 + b))) ∧
    (∀ b : ℕ, ∃ B : ℝ, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ b (convGradConvW (rieszKernelGrad d s) h) x‖ ≤ B) ∧
    (∀ (i : Fin d) (x v : Euc d),
      fderiv ℝ (fun x => convGradConvW (rieszKernelGrad d s) h x i) x v =
        ultK (u2_kap d s i) (fun y => fderiv ℝ h y v) x) := by
  have hker := fun i : Fin d => ult_ker_kap hs0 hsd i
  -- a uniform choice of constants
  have hL1 : ∀ k : ℕ, (d : ℝ) < (d : ℝ) + k + s + 4 := fun k => by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hfun : ∀ i : Fin d, (fun x => convGradConvW (rieszKernelGrad d s) h x i) =
      ultK (u2_kap d s i) h := by
    intro i
    obtain ⟨A, hA, hdec⟩ := ult_rapid_U2Dec hh 1 ((d : ℝ) + 1)
    funext x
    exact (ult_conv_comp hd hs0 hsd (by linarith) hA hdec x).2 i
  -- bounds for each order
  have key : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i : Fin d, ContDiff ℝ k (ultK (u2_kap d s i) h) ∧
      ∀ j ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (ultK (u2_kap d s i) h) x‖ ≤
        C * (1 + ‖x‖) ^ (-(s + 1 + j)) := by
    intro k
    have hL : (d : ℝ) + k + s + 3 < (d : ℝ) + k + s + 4 := by linarith
    obtain ⟨A, hA, hdec⟩ := ult_rapid_U2Dec hh (k + 1) ((d : ℝ) + k + s + 4)
    choose Ci hCi0 hCi using fun i : Fin d => ult_core hd (hker i) k hL
    refine ⟨(∑ i, Ci i) * A, mul_nonneg (Finset.sum_nonneg fun i _ => hCi0 i) hA, fun i => ?_⟩
    obtain ⟨hcd, hb⟩ := hCi i A h hA hdec
    refine ⟨hcd, fun j hj x => ?_⟩
    refine (hb j hj x).trans ?_
    have hle : Ci i ≤ ∑ i, Ci i :=
      Finset.single_le_sum (f := Ci) (fun i _ => hCi0 i) (Finset.mem_univ i)
    have : 0 ≤ (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) := Real.rpow_nonneg (by positivity) _
    nlinarith [mul_nonneg hA this]
  have hcdi : ∀ k : ℕ, ∀ i : Fin d, ContDiff ℝ k (ultK (u2_kap d s i) h) := fun k i => by
    obtain ⟨C, _, hC⟩ := key k
    exact (hC i).1
  have hcdVec : ContDiff ℝ ∞ (convGradConvW (rieszKernelGrad d s) h) := by
    rw [contDiff_infty]
    intro k
    refine contDiff_euclidean.2 fun i => ?_
    rw [hfun i]
    exact hcdi k i
  refine ⟨fun x => ?_, hcdVec, ?_, ?_, ?_⟩
  · obtain ⟨A, hA, hdec⟩ := ult_rapid_U2Dec hh 1 ((d : ℝ) + 1)
    exact (ult_conv_comp hd hs0 hsd (by linarith) hA hdec x).1
  · intro b
    obtain ⟨C, hC0, hC⟩ := key b
    refine ⟨d * C, by positivity, fun x => ?_⟩
    refine (ult_norm_iter_le_sum hcdVec b x).trans ?_
    have : ∀ i : Fin d, ‖iteratedFDeriv ℝ b (fun y => convGradConvW (rieszKernelGrad d s) h y i) x‖ ≤
        C * (1 + ‖x‖) ^ (-(s + 1 + (b : ℝ))) := by
      intro i
      rw [hfun i]
      exact (hC i).2 b le_rfl x
    refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · intro b
    obtain ⟨C, hC0, hC⟩ := key b
    refine ⟨d * C, fun x => ?_⟩
    refine (ult_norm_iter_le_sum hcdVec b x).trans ?_
    have h1 : (1 + ‖x‖) ^ (-(s + 1 + (b : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
        (by have : (0 : ℝ) ≤ b := Nat.cast_nonneg b; linarith)
    have : ∀ i : Fin d, ‖iteratedFDeriv ℝ b (fun y => convGradConvW (rieszKernelGrad d s) h y i) x‖ ≤
        C := by
      intro i
      rw [hfun i]
      refine ((hC i).2 b le_rfl x).trans ?_
      nlinarith
    refine (Finset.sum_le_sum fun i _ => this i).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · -- commutation
    intro i x v
    rw [hfun i]
    obtain ⟨A, hA, hdec⟩ := ult_rapid_U2Dec hh 2 ((d : ℝ) + 1)
    have hdL : (d : ℝ) < (d : ℝ) + 1 := by linarith
    have hit := ult_K_iter_apply hd (hker i) hdL hA (k := 1) hdec (m := 1) le_rfl (fun _ => v) x
    simpa [iteratedFDeriv_one_apply] using hit

/-- **`tail_conv`** (`W:r2:convolution-tail`): for a Schwartz function `h`, `d ≥ 2`, `0 ≤ s < d`, the cancellation
convolution `∇g * h` is `C^∞` with `‖D^b (∇g*h)(x)‖ ≤ C_b (1+‖x‖)^{-(s+1+b)}` (so all derivatives are bounded),
its defining integrals are genuine integrals, and `D (∇g*h)_i = ultK κ_i (D h)`. -/
theorem tail_conv (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (h : SchwartzMap (Euc d) ℝ) :
    (∀ x, Integrable (ultInt s ⇑h x) volume) ∧
    ContDiff ℝ ∞ (convGradConvW (rieszKernelGrad d s) ⇑h) ∧
    (∀ b : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d,
      ‖iteratedFDeriv ℝ b (convGradConvW (rieszKernelGrad d s) ⇑h) x‖ ≤
        C * (1 + ‖x‖) ^ (-(s + 1 + b))) ∧
    (∀ b : ℕ, ∃ B : ℝ, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ b (convGradConvW (rieszKernelGrad d s) ⇑h) x‖ ≤ B) ∧
    (∀ (i : Fin d) (x v : Euc d),
      fderiv ℝ (fun x => convGradConvW (rieszKernelGrad d s) ⇑h x i) x v =
        ultK (u2_kap d s i) (fun y => fderiv ℝ ⇑h y v) x) :=
  tail_conv_rapid (by omega) hs0 hsd (ult_schwartz_rapid h)

/-! ### Symbol-type classes, the generator step, `part2_c_smoothBounded` and `orbitData_decay` -/

/-- Symbol-type bounds of order `p`. -/
def UlSym (p : ℝ) (g : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ g ∧ ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d,
    ‖iteratedFDeriv ℝ m g x‖ ≤ C * (1 + ‖x‖) ^ (p - m)

lemma ult_cdat {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (m : ℕ) (x : Euc d) :
    ContDiffAt ℝ m g x :=
  (hg.of_le (by exact_mod_cast le_top)).contDiffAt

lemma ult_w_pos (x : Euc d) : 0 < 1 + ‖x‖ := by positivity

lemma ult_sym_mono {p q : ℝ} {g : Euc d → ℝ} (hpq : p ≤ q) (hg : UlSym p g) : UlSym q g := by
  refine ⟨hg.1, fun m => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hg.2 m
  refine ⟨C, hC0, fun x => (hC x).trans (mul_le_mul_of_nonneg_left ?_ hC0)⟩
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x]) (by linarith)

lemma ult_sym_add {p : ℝ} {f g : Euc d → ℝ} (hf : UlSym p f) (hg : UlSym p g) :
    UlSym p (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun m => ?_⟩
  obtain ⟨C1, hC10, hC1⟩ := hf.2 m
  obtain ⟨C2, hC20, hC2⟩ := hg.2 m
  refine ⟨C1 + C2, by positivity, fun x => ?_⟩
  have e : (fun x => f x + g x) = f + g := rfl
  rw [e, iteratedFDeriv_add_apply (ult_cdat hf.1 m x) (ult_cdat hg.1 m x)]
  refine (norm_add_le _ _).trans ?_
  nlinarith [hC1 x, hC2 x]

lemma ult_sym_smul {p : ℝ} {g : Euc d → ℝ} (c : ℝ) (hg : UlSym p g) :
    UlSym p (fun x => c * g x) := by
  refine ⟨contDiff_const.mul hg.1, fun m => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hg.2 m
  refine ⟨|c| * C, by positivity, fun x => ?_⟩
  have e : (fun x => c * g x) = fun x => c • g x := rfl
  rw [e, iteratedFDeriv_const_smul_apply' (ult_cdat hg.1 m x), norm_smul, Real.norm_eq_abs]
  calc |c| * ‖iteratedFDeriv ℝ m g x‖ ≤ |c| * (C * (1 + ‖x‖) ^ (p - m)) :=
        mul_le_mul_of_nonneg_left (hC x) (abs_nonneg c)
    _ = |c| * C * (1 + ‖x‖) ^ (p - m) := by ring

lemma ult_sym_neg {p : ℝ} {g : Euc d → ℝ} (hg : UlSym p g) : UlSym p (fun x => -g x) := by
  have := ult_sym_smul (-1) hg
  simpa using this

lemma ult_sym_zero (p : ℝ) : UlSym p (fun _ : Euc d => (0 : ℝ)) := by
  refine ⟨contDiff_const, fun m => ⟨0, le_rfl, fun x => ?_⟩⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [iteratedFDeriv_const_of_ne hm.ne']; simp

lemma ult_sym_sum {p : ℝ} {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ)
    (hf : ∀ i ∈ S, UlSym p (f i)) : UlSym p (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using ult_sym_zero p
  | insert a S ha ih =>
    have := ult_sym_add (hf a (Finset.mem_insert_self a S))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using this

lemma ult_sym_mul {p q : ℝ} {f g : Euc d → ℝ} (hf : UlSym p f) (hg : UlSym q g) :
    UlSym (p + q) (fun x => f x * g x) := by
  refine ⟨hf.1.mul hg.1, fun m => ?_⟩
  choose Cf hCf0 hCf using hf.2
  choose Cg hCg0 hCg using hg.2
  refine ⟨∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * Cf i * Cg (m - i),
    Finset.sum_nonneg fun i _ => by have := hCf0 i; have := hCg0 (m - i); positivity, fun x => ?_⟩
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := f) (g := g) (N := (m : ℕ∞ω))
    (hf.1.of_le (by exact_mod_cast le_top)) (hg.1.of_le (by exact_mod_cast le_top)) x
    (n := m) le_rfl
  refine hmul.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hw := ult_w_pos x
  have e : (1 + ‖x‖) ^ (p + q - (m : ℝ)) =
      (1 + ‖x‖) ^ (p - (i : ℝ)) * (1 + ‖x‖) ^ (q - ((m - i : ℕ) : ℝ)) := by
    rw [← Real.rpow_add hw, Nat.cast_sub hi']; congr 1; ring
  rw [e]
  have h1 := hCf i x
  have h2 := hCg (m - i) x
  calc (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) g x‖
      ≤ (m.choose i : ℝ) * (Cf i * (1 + ‖x‖) ^ (p - (i : ℝ))) *
        (Cg (m - i) * (1 + ‖x‖) ^ (q - ((m - i : ℕ) : ℝ))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (norm_nonneg _) ?_
        have := hCf0 i
        positivity
    _ = (m.choose i : ℝ) * Cf i * Cg (m - i) *
        ((1 + ‖x‖) ^ (p - (i : ℝ)) * (1 + ‖x‖) ^ (q - ((m - i : ℕ) : ℝ))) := by ring

lemma ult_sym_partial {p : ℝ} {g : Euc d → ℝ} (u : Euc d) (hg : UlSym p g) :
    UlSym (p - 1) (fun y => fderiv ℝ g y u) := by
  refine ⟨((contDiff_infty_iff_fderiv.1 hg.1).2).clm_apply contDiff_const, fun m => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hg.2 (m + 1)
  refine ⟨‖u‖ * C, by positivity, fun x => ?_⟩
  have hL : ‖(ContinuousLinearMap.apply ℝ ℝ u : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ)‖ ≤ ‖u‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun f => by
      simpa [mul_comm] using f.le_opNorm u
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg.1).2
  have h1 := (ContinuousLinearMap.apply ℝ ℝ u).norm_iteratedFDeriv_comp_left (f := fderiv ℝ g)
    (x := x) (N := ∞) (n := m) (hfd.contDiffAt) (by exact_mod_cast le_top)
  have e : (fun y => fderiv ℝ g y u) = (ContinuousLinearMap.apply ℝ ℝ u) ∘ (fderiv ℝ g) := rfl
  rw [e]
  refine h1.trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have h2 := hC x
  have e2 : (1 + ‖x‖) ^ (p - ((m + 1 : ℕ) : ℝ)) = (1 + ‖x‖) ^ (p - 1 - (m : ℝ)) := by
    congr 1; push_cast; ring
  rw [e2] at h2
  calc _ ≤ ‖u‖ * ‖iteratedFDeriv ℝ (m + 1) g x‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ ≤ ‖u‖ * (C * (1 + ‖x‖) ^ (p - 1 - (m : ℝ))) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg u)
    _ = ‖u‖ * C * (1 + ‖x‖) ^ (p - 1 - (m : ℝ)) := by ring

lemma ult_rapid_sym {h : Euc d → ℝ} (hh : UlRapid h) (p : ℝ) : UlSym p h := by
  refine ⟨hh.1, fun m => ?_⟩
  obtain ⟨C, hC⟩ := hh.2 m ⌈(m : ℝ) - p⌉₊
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have hw := ult_w_pos x
  have h1 : ‖iteratedFDeriv ℝ m h x‖ ≤ max C 0 * (1 + ‖x‖) ^ (-(⌈(m : ℝ) - p⌉₊ : ℝ)) := by
    rw [Real.rpow_neg hw.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ‖iteratedFDeriv ℝ m h x‖ * (1 + ‖x‖) ^ ⌈(m : ℝ) - p⌉₊ =
        (1 + ‖x‖) ^ ⌈(m : ℝ) - p⌉₊ * ‖iteratedFDeriv ℝ m h x‖ := by ring
      _ ≤ C := hC x
      _ ≤ max C 0 := le_max_left _ _
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ (le_max_right _ _))
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
    (by have := Nat.le_ceil ((m : ℝ) - p); linarith)

lemma ult_sym_rapid {g : Euc d → ℝ} (hg : ∀ p, UlSym p g) : UlRapid g := by
  refine ⟨(hg 0).1, fun m N => ?_⟩
  obtain ⟨C, hC0, hC⟩ := (hg ((m : ℝ) - N)).2 m
  refine ⟨C, fun x => ?_⟩
  have hw := ult_w_pos x
  calc (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ m g x‖
      ≤ (1 + ‖x‖) ^ N * (C * (1 + ‖x‖) ^ ((m : ℝ) - N - m)) :=
        mul_le_mul_of_nonneg_left (hC x) (by positivity)
    _ = C := by
        rw [show (m : ℝ) - N - m = -(N : ℝ) by ring, Real.rpow_neg hw.le, Real.rpow_natCast]
        field_simp

lemma ult_sym_clm (L : Euc d →L[ℝ] ℝ) : UlSym 1 (fun x => L x) := by
  refine ⟨L.contDiff, fun m => ⟨‖L‖, norm_nonneg _, fun x => ?_⟩⟩
  have hw : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hw0 := ult_w_pos x
  rcases m with _ | n
  · rw [norm_iteratedFDeriv_zero]
    simp only [Nat.cast_zero, sub_zero, Real.rpow_one]
    calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  · have hfd : fderiv ℝ (fun x => L x) = fun _ => L := funext fun y => L.fderiv
    rw [← norm_iteratedFDeriv_fderiv, hfd]
    rcases n with _ | n
    · rw [norm_iteratedFDeriv_zero]
      simp only [Nat.cast_zero, zero_add, sub_self, Real.rpow_zero, mul_one]
      push_cast
      simp
    · rw [iteratedFDeriv_const_of_ne (by omega)]
      simp only [Pi.zero_apply, norm_zero]
      positivity

lemma ult_lap_sym {p : ℝ} {g : Euc d → ℝ} (hg : UlSym p g) :
    UlSym (p - 2) (fun x => Laplacian.laplacian g x) := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ g) := (contDiff_infty_iff_fderiv.1 hg.1).2
  have hfun : (fun x => Laplacian.laplacian g x) = fun x => ∑ i : Fin d,
      fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) := by
    funext x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g
      (EuclideanSpace.basisFun (Fin d) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply]
    have hd1 : DifferentiableAt ℝ (fderiv ℝ g) x := (hfd.differentiable (by simp)) x
    have := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).hasFDerivAt.comp x
      hd1.hasFDerivAt
    have e : (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))) ∘ (fderiv ℝ g) := rfl
    rw [e, this.fderiv]
    simp
  rw [hfun]
  have := ult_sym_sum Finset.univ
    (fun i x => fderiv ℝ (fun y => fderiv ℝ g y (EuclideanSpace.single i (1 : ℝ))) x
      (EuclideanSpace.single i (1 : ℝ)))
    (fun i _ => ult_sym_partial _ (ult_sym_partial _ hg))
  have e : p - 1 - 1 = p - 2 := by ring
  rw [e] at this
  exact this

lemma ult_grad_apply (φ : Euc d → ℝ) (y : Euc d) (j : Fin d) :
    gradient φ y j = fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ)) := by
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Euc d)
    (x := EuclideanSpace.single j (1 : ℝ)) (y := fderiv ℝ φ y)
  have h2 : inner ℝ (gradient φ y) (EuclideanSpace.single j (1 : ℝ)) = gradient φ y j := by
    rw [EuclideanSpace.inner_single_right]; simp
  rw [← h2]
  exact this

lemma ult_matVec_neg_one (v : Euc d) (j : Fin d) :
    (Torus.matVec ((-1 : Matrix (Fin d) (Fin d) ℝ).transpose) v) j = -(v j) := by
  have : Torus.matVec ((-1 : Matrix (Fin d) (Fin d) ℝ).transpose) v = -v := by
    simp [Torus.matVec]
  rw [this]; rfl

lemma ult_fderiv_decomp (L : Euc d →L[ℝ] ℝ) (v : Euc d) :
    L v = ∑ i : Fin d, v i * L (EuclideanSpace.single i (1 : ℝ)) := by
  have hv : v = ∑ i : Fin d, (v i) • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  conv_lhs => rw [hv]
  simp [map_sum, map_smul]

lemma ult_gen_eq (s ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (c : Euc d → Euc d) (ρ : Euc d → ℝ)
    (g : Euc d → ℝ) (x : Euc d) :
    generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x =
      ν * Laplacian.laplacian g x +
        ∑ i : Fin d, (-(Torus.matVec Q x) + c x) i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)) -
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))))) x) j := by
  have hin : inner ℝ (-(Torus.matVec Q x) + c x) (gradient g x) =
      ∑ i : Fin d, (-(Torus.matVec Q x) + c x) i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ)) := by
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ult_grad_apply]
    simp [mul_comm]
  have hdef : generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x =
      ν * Laplacian.laplacian g x + inner ℝ (-(Torus.matVec Q x) + c x) (gradient g x) -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
          (fun y => ρ y * (Torus.matVec ((-1 : Matrix (Fin d) (Fin d) ℝ).transpose)
            (gradient g y)) j) x) j := rfl
  rw [hdef, hin]
  simp only [ult_matVec_neg_one, ult_grad_apply]

lemma ult_norm_iter_comp_le {c : Euc d → Euc d} (hc : ContDiff ℝ ∞ c) (j : ℕ) (x : Euc d)
    (i : Fin d) : ‖iteratedFDeriv ℝ j (fun y => c y i) x‖ ≤ ‖iteratedFDeriv ℝ j c x‖ := by
  have hp : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa using PiLp.norm_apply_le v i
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left (f := c) (x := x)
    (N := ∞) (n := j) hc.contDiffAt (by exact_mod_cast le_top)
  have e : (fun y => c y i) = (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) ∘ c := rfl
  rw [e]
  refine this.trans ?_
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ j c x‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = _ := one_mul _

lemma ult_K_comp_sym (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {h : Euc d → ℝ}
    (hh : UlRapid h) (j : Fin d) :
    UlSym (-(s + 1)) (fun x => convGradConvW (rieszKernelGrad d s) h x j) := by
  obtain ⟨_, hcd, hb, _, _⟩ := tail_conv_rapid hd hs0 hsd hh
  refine ⟨contDiff_euclidean.1 hcd j, fun m => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hb m
  refine ⟨C, hC0, fun x => ?_⟩
  refine (ult_norm_iter_comp_le hcd m x j).trans ((hC x).trans (le_of_eq ?_))
  congr 2; ring

section Gen

variable {s : ℝ} {ν : ℝ} {Q : Matrix (Fin d) (Fin d) ℝ} {ρ : Euc d → ℝ} {σ : Euc d → Euc d}

theorem ult_gen_sym (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (hρ : UlRapid ρ)
    (hσ : ∀ i, UlRapid (fun x => σ x i)) {c : Euc d → Euc d}
    (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) {g : Euc d → ℝ}
    (hg : UlSym (-(s + 1)) g) :
    UlSym (-(s + 1)) (fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x) := by
  set P : ℝ := -(s + 1) with hP
  have hP1 : P ≤ 1 := by simp only [hP]; linarith
  have e : (fun x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x) = fun x =>
      (ν * Laplacian.laplacian g x +
        ∑ i : Fin d, (-(Torus.matVec Q x) + c x) i * fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) +
      (-1) * ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))))) x) j := by
    funext x
    rw [ult_gen_eq]; ring
  rw [e]
  -- the Laplacian term
  have T1 : UlSym P (fun x => ν * Laplacian.laplacian g x) :=
    ult_sym_smul ν (ult_sym_mono (by linarith) (ult_lap_sym hg))
  -- the transport term
  have hb : ∀ i : Fin d, UlSym 1 (fun x => (-(Torus.matVec Q x) + c x) i) := by
    intro i
    have hL := ult_sym_clm ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Q)))
    have hK := ult_sym_mono hP1 (ult_K_comp_sym hd hs0 hsd hρ i)
    have h3 := ult_sym_add (ult_sym_add (ult_sym_neg hL) (ult_rapid_sym (hσ i) 1))
      (ult_sym_neg hK)
    refine (show (fun x => (-(Torus.matVec Q x) + c x) i) = _ from ?_) ▸ h3
    funext x
    subst hc
    simp [Torus.matVec]
    ring
  have T2 : UlSym P (fun x => ∑ i : Fin d, (-(Torus.matVec Q x) + c x) i *
      fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) := by
    refine ult_sym_sum Finset.univ _ fun i _ => ?_
    have := ult_sym_mul (hb i) (ult_sym_partial (EuclideanSpace.single i (1 : ℝ)) hg)
    have e1 : (1 : ℝ) + (P - 1) = P := by ring
    rw [e1] at this
    exact this
  -- the nonlocal term
  have T3 : UlSym P (fun x => ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
      (fun y => ρ y * (-(fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))))) x) j) := by
    refine ult_sym_sum Finset.univ _ fun j _ => ?_
    refine ult_K_comp_sym hd hs0 hsd (ult_sym_rapid fun q => ?_) j
    have h1 := ult_sym_mul (ult_rapid_sym hρ (q - (P - 1)))
      (ult_sym_neg (ult_sym_partial (EuclideanSpace.single j (1 : ℝ)) hg))
    have e1 : q - (P - 1) + (P - 1) = q := by ring
    rw [e1] at h1
    exact h1
  exact ult_sym_add (ult_sym_add T1 T2) (ult_sym_smul (-1) T3)

end Gen

/-- **`part2_c_smoothBounded`**: `c = σ - ∇g*ρ` of part 2 of S5.1 is smooth with all derivatives bounded. -/
theorem part2_c_smoothBounded (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (σ : Euc d → Euc d)
    (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i) :
    IsSmoothBounded (fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x) := by
  obtain ⟨ψ, rfl⟩ := hρ
  obtain ⟨_, hcd, _, hbdd, _⟩ := tail_conv hd hs0 hsd ψ
  choose φ hφ using hσ
  have hσc : ∀ i, ContDiff ℝ ∞ (fun x => σ x i) := fun i => by
    rw [← hφ i]; exact (φ i).smooth _
  have hKc : ∀ i, ContDiff ℝ ∞ (fun x => convGradConvW (rieszKernelGrad d s) ⇑ψ x i) :=
    fun i => contDiff_euclidean.1 hcd i
  have hcd' : ContDiff ℝ ∞ (fun x => σ x - convGradConvW (rieszKernelGrad d s) ⇑ψ x) :=
    contDiff_euclidean.2 fun i => by
      have := (hσc i).sub (hKc i)
      simpa using this
  refine ⟨hcd', fun j => ?_⟩
  choose Bk hBk using hbdd
  have hσb : ∀ i, ∃ C : ℝ, ∀ x : Euc d, ‖iteratedFDeriv ℝ j (fun y => σ y i) x‖ ≤ C := by
    intro i
    obtain ⟨C, hC⟩ := (ult_schwartz_rapid (φ i)).2 j 0
    refine ⟨C, fun x => ?_⟩
    have := hC x
    simp only [pow_zero, one_mul] at this
    rw [← hφ i]
    exact this
  choose Cσ hCσ using hσb
  refine ⟨∑ i : Fin d, (Cσ i + Bk j), fun x => ?_⟩
  refine (ult_norm_iter_le_sum hcd' j x).trans (Finset.sum_le_sum fun i _ => ?_)
  have e : (fun y => (σ y - convGradConvW (rieszKernelGrad d s) ⇑ψ y) i) =
      (fun y => σ y i) - (fun y => convGradConvW (rieszKernelGrad d s) ⇑ψ y i) := by
    funext y; simp
  rw [e, iteratedFDeriv_sub_apply (ult_cdat (hσc i) j x) (ult_cdat (hKc i) j x)]
  refine (norm_sub_le _ _).trans (add_le_add (hCσ i x) ?_)
  exact (ult_norm_iter_comp_le hcd j x i).trans (hBk j x)

/-- **`orbitData_decay`**: the orbit data `L^a f` of `W:r2:orbit-bounds`, `L = generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0`,
`c = σ - ∇g*ρ`, `f` Schwartz.  Every `L^a f` is `C^∞`, `‖D^m (L^a f)(x)‖ ≤ C (1+‖x‖)^{-(s+1+m)}` and
every derivative tends to `0` at infinity (the decay form feeding `ulClosure_of_decay`). -/
theorem orbitData_decay (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (ν : ℝ)
    (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ)
    (σ : Euc d → Euc d) (hσ : ∀ i, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = fun x => σ x i)
    (c : Euc d → Euc d) (hc : c = fun x => σ x - convGradConvW (rieszKernelGrad d s) ρ x)
    (f : SchwartzMap (Euc d) ℝ) (a : ℕ) :
    ContDiff ℝ ∞ ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a] ⇑f) ∧
    (∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Euc d,
      ‖iteratedFDeriv ℝ m ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a]
        ⇑f) x‖ ≤ C * (1 + ‖x‖) ^ (-(s + 1 + m))) ∧
    (∀ m : ℕ, ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ m ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ρ) 0 g x)^[a]
        ⇑f) x‖ ≤ ε) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ψ, rfl⟩ := hρ
  choose φ hφ using hσ
  have hσr : ∀ i, UlRapid (fun x => σ x i) := fun i => by
    rw [← hφ i]; exact ult_schwartz_rapid (φ i)
  have key : ∀ a : ℕ, UlSym (-(s + 1))
      ((fun g x => generatorW (fixedViscosityCoeff s (-1) Q ν c ⇑ψ) 0 g x)^[a] ⇑f) := by
    intro a
    induction a with
    | zero => exact ult_rapid_sym (ult_schwartz_rapid f) _
    | succ a ih =>
      rw [Function.iterate_succ_apply']
      exact ult_gen_sym hd1 hs0 hsd (ult_schwartz_rapid ψ) hσr hc ih
  have hk := key a
  refine ⟨hk.1, fun m => ?_, fun m ε hε => ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hk.2 m
    refine ⟨C, hC0, fun x => (hC x).trans (le_of_eq ?_)⟩
    congr 2; ring
  · obtain ⟨C, hC0, hC⟩ := hk.2 m
    refine ⟨C / ε, fun x hx => ?_⟩
    have hw : 1 + ‖x‖ ≤ (1 + ‖x‖) ^ (1 : ℝ) := by simp
    have h1 : (1 + ‖x‖) ^ (-(s + 1) - (m : ℝ)) ≤ (1 + ‖x‖)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg x])
        (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
    have hpos : 0 < 1 + ‖x‖ := ult_w_pos x
    have hCe : 0 ≤ C / ε := by positivity
    have hx1 : C / ε ≤ 1 + ‖x‖ := by linarith [norm_nonneg x, hx]
    calc ‖iteratedFDeriv ℝ m _ x‖ ≤ C * (1 + ‖x‖) ^ (-(s + 1) - (m : ℝ)) := hC x
      _ ≤ C * (1 + ‖x‖)⁻¹ := mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ ε := by
          rw [← div_eq_mul_inv, div_le_iff₀ hpos]
          calc C = (C / ε) * ε := by field_simp
            _ ≤ (1 + ‖x‖) * ε := mul_le_mul_of_nonneg_right hx1 hε.le
            _ = ε * (1 + ‖x‖) := by ring


end HRS.MS.Ul
