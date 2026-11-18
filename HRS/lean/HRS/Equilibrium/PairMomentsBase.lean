/-
# HRS.Equilibrium.PairMomentsBase -- generic machinery for Proposition 4.12 (`pair_moments`, EQ-01b)

Generic lemmas about the pinned weak ensemble `R = pinnedLaw V (β/N) N ∅`:
* Wu's single-site resampling for ordered pair sums and for ordered triple sums,
* second moment of a row `∑_{j≠i} v(x_i,x_j)`.
-/
import HRS.Equilibrium.QuadraticVariance
import HRS.Equilibrium.PinLinf

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad

variable {d : ℕ}

/-! ### Pair sums -/

/-- The part of the ordered pair sum not involving the index `i`. -/
def pairRest (b : Torus d → Torus d → ℝ) {N : ℕ} (i : Fin N) (Y : Config d N) : ℝ :=
  ∑ a ∈ Finset.univ.erase i, ∑ c ∈ (Finset.univ.erase i).erase a, b (Y a) (Y c)

theorem pairRest_update (b : Torus d → Torus d → ℝ) {N : ℕ} (i : Fin N) (Y : Config d N) (z : Torus d) :
    pairRest b i (update Y i z) = pairRest b i Y := by
  unfold pairRest
  have h1 : ∀ a ∈ Finset.univ.erase i, update Y i z a = Y a := fun a ha =>
    update_of_ne (Finset.ne_of_mem_erase ha) _ _
  refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => ?_
  rw [h1 a ha, h1 c (Finset.mem_of_mem_erase hc)]

theorem pairSum_update (b : Torus d → Torus d → ℝ) (hsym : ∀ x y, b x y = b y x) {N : ℕ} (i : Fin N)
    (Y : Config d N) (z : Torus d) :
    pairSumOrdered b (update Y i z) =
      2 * ∑ j ∈ Finset.univ.erase i, b z (Y j) + pairRest b i Y := by
  unfold pairSumOrdered
  rw [sum_sum_erase_split i (fun a c => b (update Y i z a) (update Y i z c))]
  have h1 : ∀ a ∈ Finset.univ.erase i, update Y i z a = Y a := fun a ha =>
    update_of_ne (Finset.ne_of_mem_erase ha) _ _
  have e1 : ∑ c ∈ Finset.univ.erase i, b (update Y i z i) (update Y i z c)
      = ∑ j ∈ Finset.univ.erase i, b z (Y j) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [h1 c hc, update_self]
  have e2 : ∑ a ∈ Finset.univ.erase i, b (update Y i z a) (update Y i z i)
      = ∑ j ∈ Finset.univ.erase i, b z (Y j) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [h1 a ha, update_self, hsym]
  have e3 : ∑ a ∈ Finset.univ.erase i, ∑ c ∈ (Finset.univ.erase i).erase a,
      b (update Y i z a) (update Y i z c) = pairRest b i Y := by
    rw [← pairRest_update b i Y z]
    unfold pairRest
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun c hc => ?_
    rfl
  rw [e1, e2, e3]; ring

theorem measurable_pairSumOrdered {b : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry b))
    {N : ℕ} : Measurable (fun X : Config d N => pairSumOrdered b X) := by
  unfold pairSumOrdered
  exact Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => measurable_h_pair hm i j

theorem measurable_rowSum {v : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry v))
    {N : ℕ} (i : Fin N) :
    Measurable (fun Y : Config d N => ∑ j ∈ Finset.univ.erase i, v (Y i) (Y j)) :=
  Finset.measurable_sum _ fun j _ => measurable_h_pair hm i j

theorem enorm_sq_mul_real (a r : ℝ) : ‖a * r‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) * ‖r‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow, ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg a)]

section Resample

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- **Single-site resampling for ordered pair sums**:
`Var_R(c ∑_{i≠j} b(x_i,x_j)) ≤ 8 c² ∑_i E_R |∑_{j≠i} b(x_i,x_j)|²`. -/
theorem evariance_pairSum_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN0 : 0 < N)
    (hκ : weakKappa V β ≤ 1 / 2) {b : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry b))
    (hsym : ∀ x y, b x y = b y x) (c : ℝ) :
    evariance (fun X : Config d N => c * pairSumOrdered b X)
        (pinnedLaw V (β / N) N (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal (8 * c ^ 2) * ∑ i, ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  set S := fieldSpec (V := V) hψ hlam N with hS
  have hSP : S.P = pinnedLaw V (β / N) N (fun e : Empty => e.elim) := rfl
  have hF : Measurable (fun X : Config d N => c * pairSumOrdered b X) :=
    measurable_const.mul (measurable_pairSumOrdered hm)
  have h1 := weak_resampling (B := Empty) V hβ hN0 (by simp) (fun e : Empty => e.elim) hκ _ hF
  refine h1.trans ?_
  have hper : ∀ i : Fin N, ∫⁻ x, evariance (fun z => c * pairSumOrdered b (update x i z))
      (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (4 * c ^ 2) * ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
    intro i
    have hG : ∀ x, siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x = S.G i x :=
      fun x => rfl
    have hrow := measurable_rowSum hm (N := N) i
    have hpt : ∀ x, evariance (fun z => c * pairSumOrdered b (update x i z))
        (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
        ≤ ∫⁻ z, ENNReal.ofReal (4 * c ^ 2) *
            ‖∑ j ∈ Finset.univ.erase i, b (update x i z i) (update x i z j)‖ₑ ^ 2 ∂(S.G i x) := by
      intro x
      rw [hG]
      refine (evariance_le_lintegral_sub (S.G i x)
        (hF.comp (measurable_update x)).aestronglyMeasurable (c * pairRest b i x)).trans (le_of_eq ?_)
      refine lintegral_congr fun z => ?_
      have e1 := pairSum_update b hsym i x z
      have e2 : ∑ j ∈ Finset.univ.erase i, b (update x i z i) (update x i z j)
          = ∑ j ∈ Finset.univ.erase i, b z (x j) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [update_self, update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [e2]
      simp only [Function.comp]
      rw [e1]
      have : c * (2 * ∑ j ∈ Finset.univ.erase i, b z (x j) + pairRest b i x) - c * pairRest b i x
          = (2 * c) * ∑ j ∈ Finset.univ.erase i, b z (x j) := by ring
      rw [this, enorm_sq_mul_real]
      ring_nf
    calc _ ≤ ∫⁻ x, ∫⁻ z, ENNReal.ofReal (4 * c ^ 2) *
            ‖∑ j ∈ Finset.univ.erase i, b (update x i z i) (update x i z j)‖ₑ ^ 2 ∂(S.G i x)
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := lintegral_mono hpt
      _ = ∫⁻ Y, ENNReal.ofReal (4 * c ^ 2) * ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
        rw [← hSP]
        exact S.invariant i (fun Y => ENNReal.ofReal (4 * c ^ 2) *
          ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2)
          (measurable_const.mul (hrow.enorm.pow_const 2))
      _ = _ := by
        rw [lintegral_const_mul _ (hrow.enorm.pow_const 2)]
  calc 2 * ∑ i, ∫⁻ x, evariance (fun z => c * pairSumOrdered b (update x i z))
        (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ 2 * ∑ i : Fin N, (ENNReal.ofReal (4 * c ^ 2) * ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))) := by
        gcongr with i _
        exact hper i
    _ = _ := by
        rw [← Finset.mul_sum, ← mul_assoc]
        congr 1
        rw [show (8 : ℝ) * c ^ 2 = 2 * (4 * c ^ 2) by ring, ENNReal.ofReal_mul (by norm_num)]
        simp

end Resample

/-! ### Row second moment -/

section Row

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- **Row second moment** (a.e. form of `HRS.Quad.row_lintegral_le`, no centering): if for `μ`-a.e. pin
value `x` the variance integral `∫ |v(x,y)|² e^{M'+βγ+ψ_x(y)} dμ(y) ≤ 𝒱` and the conditional mean
`|∑_k ∫ v(x,·) dπ^x_k| ≤ 𝓜`, then `E_R |∑_{j≠i} v(x_i,x_j)|² ≤ 2n 𝒱 + 𝓜²`. -/
theorem row_moment_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n]
    (hκ : weakKappa V β ≤ 1 / 2) {v : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry v))
    (i : Fin (n + 1)) {𝒱 : ℝ≥0∞} {𝓜 : ℝ}
    (hV : ∀ᵐ x ∂μ, ∫⁻ y, ‖v x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂μ ≤ 𝒱)
    (hM : ∀ᵐ x ∂μ, |∑ k : Fin n, ∫ y, v x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))| ≤ 𝓜) :
    ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, v (Y i) (Y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have hΦ : Measurable fun Y : Fin (n + 1) → Torus d => ‖∑ j ∈ Finset.univ.erase i, v (Y i) (Y j)‖ₑ ^ 2 :=
    (measurable_rowSum hm i).enorm.pow_const 2
  rw [lintegral_pinned_succ V hlam (fun e : Empty => e.elim) i hΦ]
  have hx : ∀ x : Torus d,
      (∫⁻ y, ‖v x x‖ₑ ^ 0 * 0 ∂μ ≤ 𝒱) → True := fun _ _ => trivial
  have hmain : ∀ x : Torus d,
      ∫⁻ y, ‖v x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂μ ≤ 𝒱 →
      |∑ k : Fin n, ∫ y, v x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))| ≤ 𝓜 →
      ∫⁻ y, ‖∑ j ∈ Finset.univ.erase i, v (insertAt i x y i) (insertAt i x y j)‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x))
      ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
    intro x hVx hMx
    have hrow : ∀ y : Fin n → Torus d, ∑ j ∈ Finset.univ.erase i, v (insertAt i x y i) (insertAt i x y j)
        = ∑ k, v x (y k) - 0 := by
      intro y
      rw [insertAt_same, sum_erase_insertAt i x y (fun z => v x z), sub_zero]
    simp_rw [hrow]
    have hcm : Measurable (v x) := measurable_h_x hm x
    have hcard : n + Fintype.card (Option Empty) ≤ n + 1 := by simp
    refine (second_moment_pinned (B := Option Empty) V hβ (N := n + 1) hN0 hcard
      (pinsWith (fun e : Empty => e.elim) x) hκ hcm 0).trans ?_
    refine add_le_add (mul_le_mul' le_rfl hVx) (ENNReal.ofReal_le_ofReal ?_)
    have := abs_le.1 hMx
    have h2 : (∑ k, ∫ z, v x z ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun y => y k)) - 0) ^ 2 ≤ 𝓜 ^ 2 := by
      rw [sub_zero]; exact sq_le_sq' this.1 this.2
    exact h2
  calc ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x *
        ∫⁻ y, ‖∑ j ∈ Finset.univ.erase i, v (insertAt i x y i) (insertAt i x y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)) ∂μ
      ≤ ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x *
        (ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2)) ∂μ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hV, hM] with x hVx hMx
        exact mul_le_mul' le_rfl (hmain x hVx hMx)
    _ ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
        by_cases hC : ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) = ⊤
        · rw [hC]; exact le_top
        · rw [lintegral_mul_const' _ _ hC, lintegral_pinWeight V hlam (fun e : Empty => e.elim) i (0 : Fin n),
            one_mul]

end Row

/-! ### Retained poles -/

section Poles

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- The uniform bounds on a weak potential used throughout: `M ≤ Mmax`, `M' ≤ M'max`, `γ ≤ γmax`
and the lower envelope `q(x,y) ≥ g_+(x-y) - C_q` of the pair kernel off the diagonal. -/
structure PotBound (s c Mmax M'max γmax Cq : ℝ) (V : WeakPotential μ) : Prop where
  hM : V.M ≤ Mmax
  hM' : V.M' ≤ M'max
  hγ : V.γ ≤ γmax
  hq : ∀ x y : Torus d, x ≠ y → gPlus d s c (x - y) - Cq ≤ V.q x y

theorem gPlus_neg (s c : ℝ) (z : Torus d) : gPlus d s c (-z) = gPlus d s c z := by
  unfold gPlus
  rw [periodicRiesz_neg]

/-- **Retained pole** (one pin): for `y ≠ x`,
`M' + βγ + ψ_x(y) ≤ M₀ - λ g_+(x-y)`. -/
theorem pole_exponent_le {s c Mmax M'max γmax Cq : ℝ} {V : WeakPotential μ}
    (hV : PotBound (d := d) s c Mmax M'max γmax Cq V) {β lam : ℝ} (hβ : 0 ≤ β) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ β) (hCq : 0 ≤ Cq) (a : Option Empty → Torus d) {x y : Torus d} (hxy : y ≠ x)
    (ha : a = pinsWith (fun e : Empty => e.elim) x) :
    V.M' + β * V.γ + pinField V lam a y ≤
      (M'max + β * max γmax 0 + Mmax + β * Cq) - lam * gPlus d s c (x - y) := by
  subst ha
  rw [pinField_pinsWith, HRS.External.RefMarg.pinField_empty]
  have h2 := V.φ_le y
  have h3 := hV.hq y x hxy
  have e : gPlus d s c (y - x) = gPlus d s c (x - y) := by
    rw [← neg_sub x y, gPlus_neg]
  rw [e] at h3
  have h4 : β * V.γ ≤ β * max γmax 0 := mul_le_mul_of_nonneg_left (hV.hγ.trans (le_max_left _ _)) hβ
  have h5 : lam * Cq ≤ β * Cq := mul_le_mul_of_nonneg_right hlam hCq
  have h6 : lam * (gPlus d s c (x - y) - Cq) ≤ lam * V.q y x := mul_le_mul_of_nonneg_left h3 hlam0
  have := hV.hM'
  have := hV.hM
  nlinarith

theorem lintegral_pole_le {s c Mmax M'max γmax Cq : ℝ} {V : WeakPotential μ}
    (hV : PotBound (d := d) s c Mmax M'max γmax Cq V) {β lam : ℝ} (hβ : 0 ≤ β) (hlam0 : 0 ≤ lam)
    (hlam : lam ≤ β) (hCq : 0 ≤ Cq) {x : Torus d} (hatom : ∀ z : Torus d, μ {z} = 0) (F : Torus d → ℝ≥0∞) :
    ∫⁻ y, F y * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V lam (pinsWith (fun e : Empty => e.elim) x) y)) ∂μ ≤
      ENNReal.ofReal (Real.exp (M'max + β * max γmax 0 + Mmax + β * Cq)) *
        ∫⁻ y, F y * ENNReal.ofReal (Real.exp (-lam * gPlus d s c (x - y))) ∂μ := by
  have hae : ∀ᵐ y ∂μ, y ≠ x := HRS.External.PoleVar.ae_ne_pt hatom x
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ?_
  filter_upwards [hae] with y hy
  have h := pole_exponent_le hV hβ hlam0 hlam hCq _ hy rfl
  rw [← mul_assoc, mul_comm (ENNReal.ofReal _) (F y), mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal ?_)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  linarith

end Poles

/-! ### Marginals of pinned ensembles -/

section Marginals

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- A one-coordinate marginal of a pinned ensemble integrates a nonnegative test function against
at most `e^{M'+βγ+ψ} μ`. -/
theorem lintegral_marg_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → Torus d) (k : Fin n) {G : Torus d → ℝ≥0∞}
    (hG : Measurable G) :
    ∫⁻ z, G z ∂((pinnedLaw V (β / N) n a).map (fun y => y k)) ≤
      ∫⁻ z, G z * ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a z)) ∂μ := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hdom := pinned_marginal_le_density V hβ hN0 hN a k
  calc ∫⁻ z, G z ∂((pinnedLaw V (β / N) n a).map (fun y => y k))
      ≤ ∫⁻ z, G z ∂(μ.withDensity fun z => ENNReal.ofReal
            (Real.exp (V.M' + β * V.γ + pinField V (β / N) a z))) :=
        lintegral_mono' hdom le_rfl
    _ = _ := by
        rw [lintegral_withDensity_eq_lintegral_mul₀]
        · simp only [Pi.mul_apply]
          exact lintegral_congr fun z => mul_comm _ _
        · exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (measurable_const.add (isField_pinField V hlam a).measurable))).aemeasurable
        · exact hG.aemeasurable

/-- **Crude row mean**: `|∑_k ∫ f dπ_k| ≤ n W` whenever `∫ |f| e^{M'+βγ+ψ} dμ ≤ W`. -/
theorem abs_sum_marg_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → Torus d) {f : Torus d → ℝ} (hf : Measurable f) {W : ℝ}
    (hW0 : 0 ≤ W)
    (hW : ∫⁻ z, ‖f z‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a z)) ∂μ
      ≤ ENNReal.ofReal W) :
    |∑ k : Fin n, ∫ z, f z ∂((pinnedLaw V (β / N) n a).map (fun y => y k))| ≤ n * W := by
  have h1 : ∀ k : Fin n, |∫ z, f z ∂((pinnedLaw V (β / N) n a).map (fun y => y k))| ≤ W := by
    intro k
    have h2 := norm_integral_le_lintegral_norm (μ := (pinnedLaw V (β / N) n a).map (fun y => y k)) f
    rw [Real.norm_eq_abs] at h2
    refine h2.trans (ENNReal.toReal_le_of_le_ofReal hW0 ?_)
    refine le_trans (le_of_eq ?_) ((lintegral_marg_le V hβ hN0 hN a k hf.enorm).trans hW)
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal_abs]; rfl
  calc |∑ k : Fin n, ∫ z, f z ∂((pinnedLaw V (β / N) n a).map (fun y => y k))|
      ≤ ∑ k : Fin n, |∫ z, f z ∂((pinnedLaw V (β / N) n a).map (fun y => y k))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, W := Finset.sum_le_sum fun k _ => h1 k
    _ = n * W := by simp

/-- Integrability against a one-coordinate marginal from a finite weighted bound. -/
theorem integrable_marg (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → Torus d) (k : Fin n) {f : Torus d → ℝ} (hf : Measurable f)
    {W : ℝ≥0∞} (hWt : W ≠ ⊤)
    (hW : ∫⁻ z, ‖f z‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a z)) ∂μ ≤ W) :
    Integrable f ((pinnedLaw V (β / N) n a).map (fun y => y k)) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  exact lt_of_le_of_lt ((lintegral_marg_le V hβ hN0 hN a k hf.enorm).trans hW) (lt_top_iff_ne_top.2 hWt)

end Marginals

/-! ### The pole integrals `∫ w² e^{-λ g_+}`, `∫ w⁴ e^{-λ g_+}` against the weak ensemble -/

section PoleInt

variable {s : ℝ}

theorem logEN_pos' {N : ℕ} (hN : 1 ≤ N) : 1 ≤ logEN N := by
  rw [PairCorrAux.logEN_eq N hN]
  have := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
  linarith

theorem logEN_sq_le {N : ℕ} (hN : 1 ≤ N) : logEN N ^ 2 ≤ 4 * N := by
  rw [PairCorrAux.logEN_eq N hN]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hN0)
  have h2 : Real.log (Real.sqrt N) = Real.log N / 2 := by
    rw [Real.log_sqrt hN0.le]
  have h3 : Real.log N ≤ 2 * Real.sqrt N - 2 := by linarith
  have h4 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have h5 : (1 : ℝ) + Real.log N ≤ 2 * Real.sqrt N := by linarith [Real.sqrt_nonneg (N : ℝ)]
  have h6 : (1 + Real.log N) ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := pow_le_pow_left₀ (by linarith) h5 2
  calc (1 + Real.log N) ^ 2 ≤ (2 * Real.sqrt N) ^ 2 := h6
    _ = 4 * (Real.sqrt N) ^ 2 := by ring
    _ = 4 * N := by rw [Real.sq_sqrt hN0.le]

theorem logEN_le {N : ℕ} (hN : 1 ≤ N) : logEN N ≤ 2 * Real.sqrt N := by
  rw [PairCorrAux.logEN_eq N hN]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hN0)
  have h2 : Real.log (Real.sqrt N) = Real.log N / 2 := by
    rw [Real.log_sqrt hN0.le]
  linarith [Real.sqrt_nonneg (N : ℝ)]

end PoleInt

section PoleInt2

variable {s : ℝ}

/-- Integrals of `w²` and `w⁴` against the weak pole weight (Lemma 4.11, first display, with
`g_+` replaced via the lower envelope of `V.q`). -/
theorem pole_w_integrals (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      (∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * logEN N)) ∧
      (∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4) * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
          pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (C * (N : ℝ) ^ 2)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C0, hC0⟩ := critical_envelope_integrals hd hcrit β hβ ρ hρ c hc 1 one_pos
  set E0 : ℝ := Real.exp (M'max + β * max γmax 0 + Mmax + β * Cq) with hE0
  have hE0p : 0 < E0 := Real.exp_pos _
  refine ⟨E0 * max C0 0, by positivity, fun V hV N hN x => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNp : (0 : ℝ) < N := by linarith
  have hlam0 : 0 ≤ β / N := by positivity
  have hlam : β / N ≤ β := by
    rw [div_le_iff₀ hNp]; nlinarith
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  obtain ⟨h2, -, -⟩ := hC0 N hN
  simp only [one_mul] at h2
  have hmul : ∀ (a b : ℝ), 0 ≤ a → ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) :=
    fun a b ha => (ENNReal.ofReal_mul ha).symm
  constructor
  · refine (lintegral_pole_le hV hβ.le hlam0 hlam hCq hatom
      (fun y => ENNReal.ofReal (wEnv s x y ^ 2))).trans ?_
    have : ∀ y, ENNReal.ofReal (wEnv s x y ^ 2) * ENNReal.ofReal (Real.exp (-(β / N) * gPlus d s c (x - y)))
        = ENNReal.ofReal (wEnv s x y ^ 2 * Real.exp (-(β / N) * gPlus d s c (x - y))) := fun y =>
      (ENNReal.ofReal_mul (sq_nonneg _)).symm
    simp_rw [this]
    calc ENNReal.ofReal E0 * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2 *
          Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal E0 * ENNReal.ofReal (C0 * logEN N) := by gcongr; exact (h2 x).1
      _ = ENNReal.ofReal (E0 * (C0 * logEN N)) := (ENNReal.ofReal_mul hE0p.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := logEN_pos' (N := N) (by omega)
          have : C0 ≤ max C0 0 := le_max_left _ _
          nlinarith [mul_nonneg hE0p.le (sub_nonneg.2 this)]
  · refine (lintegral_pole_le hV hβ.le hlam0 hlam hCq hatom
      (fun y => ENNReal.ofReal (wEnv s x y ^ 4))).trans ?_
    have : ∀ y, ENNReal.ofReal (wEnv s x y ^ 4) * ENNReal.ofReal (Real.exp (-(β / N) * gPlus d s c (x - y)))
        = ENNReal.ofReal (wEnv s x y ^ 4 * Real.exp (-(β / N) * gPlus d s c (x - y))) := fun y =>
      (ENNReal.ofReal_mul (by positivity)).symm
    simp_rw [this]
    calc ENNReal.ofReal E0 * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4 *
          Real.exp (-(β / N) * gPlus d s c (x - y))) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal E0 * ENNReal.ofReal (C0 * (N : ℝ) ^ 2) := by gcongr; exact (h2 x).2
      _ = ENNReal.ofReal (E0 * (C0 * (N : ℝ) ^ 2)) := (ENNReal.ofReal_mul hE0p.le).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have : C0 ≤ max C0 0 := le_max_left _ _
          nlinarith [mul_nonneg hE0p.le (sub_nonneg.2 this), sq_nonneg (N : ℝ)]

end PoleInt2

/-! ### Part (b): the repeated-pair term under the reference -/

section PartB

variable {s : ℝ}

theorem rpow_sq_neg (N : ℕ) (hN : 0 < N) (a : ℝ) :
    ((N : ℝ) ^ (-a)) ^ 2 = 1 / (N : ℝ) ^ (2 * a) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN'.le]
  have : -a * ((2 : ℕ) : ℝ) = -(2 * a) := by push_cast; ring
  rw [this, Real.rpow_neg hN'.le, one_div]

theorem real_partb (N n C0 K L : ℝ) (hN : 1 ≤ N) (hn : 0 ≤ n) (hnN : n ≤ N) (hL0 : 0 ≤ L)
    (hL2 : L ^ 2 ≤ 4 * N) (hC0 : 0 ≤ C0) :
    8 * (1 / N ^ 5) * (N * (2 * n * (K ^ 2 * (C0 * N ^ 2)) + (n * (|K| * (C0 * L))) ^ 2))
      ≤ 8 * (2 * C0 + 4 * C0 ^ 2) * K ^ 2 / N := by
  have hN0 : 0 < N := by linarith
  have hX : 2 * n * (K ^ 2 * (C0 * N ^ 2)) + (n * (|K| * (C0 * L))) ^ 2
      ≤ K ^ 2 * N ^ 3 * (2 * C0 + 4 * C0 ^ 2) := by
    have h1 : 2 * n * (K ^ 2 * (C0 * N ^ 2)) ≤ 2 * C0 * K ^ 2 * N ^ 3 := by
      have : n * (K ^ 2 * (C0 * N ^ 2)) ≤ N * (K ^ 2 * (C0 * N ^ 2)) :=
        mul_le_mul_of_nonneg_right hnN (by positivity)
      nlinarith
    have h2 : (n * (|K| * (C0 * L))) ^ 2 ≤ 4 * C0 ^ 2 * K ^ 2 * N ^ 3 := by
      have e : (n * (|K| * (C0 * L))) ^ 2 = n ^ 2 * K ^ 2 * C0 ^ 2 * L ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, sq_abs]; ring
      rw [e]
      have h3 : n ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hn hnN 2
      have h4 : 0 ≤ K ^ 2 * C0 ^ 2 := by positivity
      calc n ^ 2 * K ^ 2 * C0 ^ 2 * L ^ 2 = (n ^ 2 * L ^ 2) * (K ^ 2 * C0 ^ 2) := by ring
        _ ≤ (N ^ 2 * (4 * N)) * (K ^ 2 * C0 ^ 2) := by
            refine mul_le_mul_of_nonneg_right ?_ h4
            exact mul_le_mul h3 hL2 (by positivity) (by positivity)
        _ = 4 * C0 ^ 2 * K ^ 2 * N ^ 3 := by ring
    nlinarith
  calc 8 * (1 / N ^ 5) * (N * (2 * n * (K ^ 2 * (C0 * N ^ 2)) + (n * (|K| * (C0 * L))) ^ 2))
      ≤ 8 * (1 / N ^ 5) * (N * (K ^ 2 * N ^ 3 * (2 * C0 + 4 * C0 ^ 2))) := by
        gcongr
    _ = 8 * (2 * C0 + 4 * C0 ^ 2) * K ^ 2 / N := by
        field_simp

/-- Variance of the repeated-pair term under the weak reference. -/
theorem partb_ref (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ n : ℕ, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      ∀ (K : ℝ) (b : Torus d → Torus d → ℝ), Measurable (Function.uncurry b) → (∀ x y, b x y = b y x) →
      (∀ x y, x ≠ y → |b x y| ≤ K * wEnv s x y ^ 2) →
        evariance (fun X : Config d (n + 1) => ((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X)
            (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * K ^ 2 / ((n + 1 : ℕ) : ℝ)) := by
  have hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C0, hC00, hC0⟩ := pole_w_integrals hd hcrit β hβ ρ hρ c hc Mmax M'max γmax Cq hCq
  refine ⟨8 * (2 * C0 + 4 * C0 ^ 2), by positivity, fun V hV n hn hκ K b hm hsym hb => ?_⟩
  set N : ℕ := n + 1 with hNdef
  have hN1 : 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have hnR : (n : ℝ) ≤ N := by simp [hNdef]
  haveI : NeZero n := ⟨by omega⟩
  have hLp := logEN_pos' (N := N) hN1
  have hL2 := logEN_sq_le (N := N) hN1
  -- pointwise kernel bounds
  have hatom := fun z => Calib.atomless_withDensityReal (by omega : 1 ≤ d) ρ z
  have hae : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := fun x => HRS.External.PoleVar.ae_ne_pt hatom x
  have hsq : ∀ x y, x ≠ y → ‖b x y‖ₑ ^ 2 ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 4) := by
    intro x y hxy
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hb x y hxy
    have h2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    calc b x y ^ 2 ≤ (K * wEnv s x y ^ 2) ^ 2 := h2
      _ = _ := by ring
  have habs : ∀ x y, x ≠ y → ‖b x y‖ₑ ≤ ENNReal.ofReal |K| * ENNReal.ofReal (wEnv s x y ^ 2) := by
    intro x y hxy
    rw [← ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |b x y| ≤ K * wEnv s x y ^ 2 := hb x y hxy
      _ ≤ |K| * wEnv s x y ^ 2 := mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)
  -- row bounds
  have hlam0 : 0 ≤ β / N := by positivity
  have hVint : ∀ x : Torus d, ∫⁻ y, ‖b x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (K ^ 2 * (C0 * (N : ℝ) ^ 2)) := by
    intro x
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (wEnv s x y ^ 4)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          exact mul_le_mul' (hsq x y (Ne.symm hy)) le_rfl
      _ = ENNReal.ofReal (K ^ 2) * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 4) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal (K ^ 2) * ENNReal.ofReal (C0 * (N : ℝ) ^ 2) := by
          gcongr
          exact (hC0 V hV N hN2 x).2
      _ = _ := (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hVmean : ∀ x : Torus d, ∫⁻ y, ‖b x y‖ₑ * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (|K| * (C0 * logEN N)) := by
    intro x
    calc _ ≤ ∫⁻ y, (ENNReal.ofReal |K| * ENNReal.ofReal (wEnv s x y ^ 2)) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae x] with y hy
          exact mul_le_mul' (habs x y (Ne.symm hy)) le_rfl
      _ = ENNReal.ofReal |K| * ∫⁻ y, ENNReal.ofReal (wEnv s x y ^ 2) *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y))
          ∂(withDensityReal ρ) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine lintegral_congr fun y => ?_
          rw [mul_assoc]
      _ ≤ ENNReal.ofReal |K| * ENNReal.ofReal (C0 * logEN N) := by
          gcongr
          exact (hC0 V hV N hN2 x).1
      _ = _ := (ENNReal.ofReal_mul (abs_nonneg _)).symm
  have hcard : n + Fintype.card (Option Empty) ≤ n + 1 := by simp
  have hrow : ∀ i : Fin (n + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i, b (Y i) (Y j)‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (2 * n) * ENNReal.ofReal (K ^ 2 * (C0 * (N : ℝ) ^ 2)) +
        ENNReal.ofReal ((n * (|K| * (C0 * logEN N))) ^ 2) := by
    intro i
    refine row_moment_le V hβ.le hκ hm i (𝒱 := ENNReal.ofReal (K ^ 2 * (C0 * (N : ℝ) ^ 2)))
      (𝓜 := n * (|K| * (C0 * logEN N))) (Filter.Eventually.of_forall hVint) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    exact abs_sum_marg_le V hβ.le (by omega) hcard _ (measurable_h_x hm x)
      (by positivity) (hVmean x)
  have hWu := evariance_pairSum_le V hβ.le (by omega : 0 < n + 1) hκ hm hsym (((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)))
  refine hWu.trans ?_
  have hc2 : (((n + 1 : ℕ) : ℝ) ^ (-(5 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) ^ 5 := by
    rw [rpow_sq_neg N (by omega)]
    have : (2 * (5 / 2 : ℝ)) = ((5 : ℕ) : ℝ) := by norm_num
    rw [this, Real.rpow_natCast]
  rw [hc2]
  calc ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 5)) * ∑ i : Fin (n + 1), ∫⁻ Y, ‖∑ j ∈ Finset.univ.erase i,
        b (Y i) (Y j)‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 5)) * ∑ _i : Fin (n + 1),
          (ENNReal.ofReal (2 * n) * ENNReal.ofReal (K ^ 2 * (C0 * (N : ℝ) ^ 2)) +
            ENNReal.ofReal ((n * (|K| * (C0 * logEN N))) ^ 2)) := by
        gcongr with i _
        exact hrow i
    _ = ENNReal.ofReal (8 * (1 / (N : ℝ) ^ 5) * (N * (2 * n * (K ^ 2 * (C0 * (N : ℝ) ^ 2)) +
          (n * (|K| * (C0 * logEN N))) ^ 2))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have h1 : (0 : ℝ) ≤ 2 * n := by positivity
        rw [show (((n + 1 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal (N : ℝ) by
          rw [ENNReal.ofReal_natCast]]
        rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        exact real_partb N n C0 K (logEN N) (by exact_mod_cast hN1) (Nat.cast_nonneg n) hnR
          (by linarith) hL2 hC00

end PartB

/-! ### Refined row mean from the density comparison -/

section Mean

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- `∫ f dπ = ∫ f (dπ/dμ - 1) dμ` when `∫ f dμ = 0`. -/
theorem integral_marg_eq {π : Measure (Torus d)} [IsFiniteMeasure π] (hπ : π ≪ μ) {f : Torus d → ℝ}
    (hfμ : Integrable f μ) (hfπ : Integrable f π) (h0 : ∫ y, f y ∂μ = 0) :
    ∫ y, f y ∂π = ∫ y, f y * ((π.rnDeriv μ y).toReal - 1) ∂μ := by
  have h1 : ∫ y, f y ∂π = ∫ y, (π.rnDeriv μ y).toReal * f y ∂μ := (integral_toReal_rnDeriv_mul hπ).symm
  have h2 : Integrable (fun y => (π.rnDeriv μ y).toReal * f y) μ :=
    (integrable_toReal_rnDeriv_mul_iff hπ).2 hfπ
  rw [h1]
  have : ∀ y, f y * ((π.rnDeriv μ y).toReal - 1) = (π.rnDeriv μ y).toReal * f y - f y := fun y => by ring
  simp_rw [this]
  rw [integral_sub h2 hfμ, h0, sub_zero]

/-- `|∫ f dπ| ≤ ∫ |f| g dμ` for `|dπ/dμ - 1| ≤ g` a.e. (as a lintegral). -/
theorem abs_integral_marg_le {π : Measure (Torus d)} [IsFiniteMeasure π] (hπ : π ≪ μ) {f g : Torus d → ℝ}
    (hfμ : Integrable f μ) (hfπ : Integrable f π) (h0 : ∫ y, f y ∂μ = 0)
    (hg : ∀ᵐ y ∂μ, |(π.rnDeriv μ y).toReal - 1| ≤ g y) {W : ℝ} (hW0 : 0 ≤ W)
    (hW : ∫⁻ y, ENNReal.ofReal (|f y| * g y) ∂μ ≤ ENNReal.ofReal W) :
    |∫ y, f y ∂π| ≤ W := by
  rw [integral_marg_eq hπ hfμ hfπ h0]
  have h1 := norm_integral_le_lintegral_norm (μ := μ) (fun y => f y * ((π.rnDeriv μ y).toReal - 1))
  rw [Real.norm_eq_abs] at h1
  refine h1.trans (ENNReal.toReal_le_of_le_ofReal hW0 ?_)
  refine le_trans (lintegral_mono_ae ?_) hW
  filter_upwards [hg] with y hy
  rw [Real.norm_eq_abs, abs_mul]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hy (abs_nonneg _))

end Mean

/-! ### Crude second moment of pair sums -/

section Crude

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

theorem enorm_sq_pairSum_le {N : ℕ} (h : Torus d → Torus d → ℝ) (Y : Config d N) :
    ‖pairSumOrdered h Y‖ₑ ^ 2 ≤ ENNReal.ofReal ((N : ℝ) ^ 2) *
      ∑ i, ∑ j ∈ Finset.univ.erase i, ‖h (Y i) (Y j)‖ₑ ^ 2 := by
  have e1 : ‖pairSumOrdered h Y‖ₑ ^ 2 = ENNReal.ofReal (pairSumOrdered h Y ^ 2) := by
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  have e2 : ∀ i j : Fin N, ‖h (Y i) (Y j)‖ₑ ^ 2 = ENNReal.ofReal (h (Y i) (Y j) ^ 2) := fun i j => by
    rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
  simp_rw [e1, e2]
  have h1 := sq_sum_sum_erase_le (fun i j => h (Y i) (Y j))
  unfold pairSumOrdered
  refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => Finset.sum_nonneg
    fun j _ => sq_nonneg _)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]

/-- **Crude second moment of an ordered pair sum** (no smallness): from the pair second moments. -/
theorem lintegral_pairSum_sq_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ}
    {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h)) {𝒲 : ℝ≥0∞}
    (hW : ∀ x, ∫⁻ z, ‖h x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂μ ≤ 𝒲) :
    ∫⁻ Y, ‖pairSumOrdered h Y‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 4) * 𝒲 := by
  have hmeas : ∀ i j : Fin (n + 1), Measurable fun Y : Config d (n + 1) => ‖h (Y i) (Y j)‖ₑ ^ 2 :=
    fun i j => ((measurable_h_pair hm i j).enorm).pow_const 2
  have hpair : ∀ a b : Fin (n + 1), a ≠ b → ∫⁻ Y, ‖h (Y a) (Y b)‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤ 𝒲 :=
    fun a b hab => pair_lintegral_le V hβ a b hab hm hW
  calc ∫⁻ Y, ‖pairSumOrdered h Y‖ₑ ^ 2
        ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ∫⁻ Y, ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 2) *
          ∑ i, ∑ j ∈ Finset.univ.erase i, ‖h (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) :=
        lintegral_mono fun Y => enorm_sq_pairSum_le h Y
    _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
          ∫⁻ Y, ‖h (Y i) (Y j)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _
          fun j _ => hmeas i j)]
        congr 1
        rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ fun j _ => hmeas i j)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum _ (fun j _ => hmeas i j)]
    _ ≤ ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 2) * ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, 𝒲 := by
        gcongr with i _ j hj
        exact hpair i j (Finset.ne_of_mem_erase hj).symm
    _ ≤ ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 2) * ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), 𝒲 := by
        exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ =>
          Finset.sum_le_sum_of_subset (Finset.erase_subset i Finset.univ))
    _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) ^ 4) * 𝒲 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show (4 : ℕ) = 2 + 1 + 1 by norm_num]
        have : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal (((n + 1 : ℕ) : ℝ)) := by
          rw [ENNReal.ofReal_natCast]
        rw [this, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 3

end Crude

section PoleConst

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- The pole weight is bounded by a constant. -/
theorem poleW_le_const {s c Mmax M'max γmax Cq : ℝ} {V : WeakPotential μ}
    (hV : PotBound (d := d) s c Mmax M'max γmax Cq V) {β lam : ℝ} (hβ : 0 ≤ β) (hlam0 : 0 ≤ lam)
    {B : Type*} [Fintype B] (a : B → Torus d) (y : Torus d) :
    ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V lam a y)) ≤
      ENNReal.ofReal (Real.exp (M'max + β * max γmax 0 + Mmax)) := by
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have h1 := V.φ_le y
  have h2 : 0 ≤ lam * ∑ b, V.q y (a b) :=
    mul_nonneg hlam0 (Finset.sum_nonneg fun b _ => V.q_nonneg _ _)
  have h3 : β * V.γ ≤ β * max γmax 0 := mul_le_mul_of_nonneg_left (hV.hγ.trans (le_max_left _ _)) hβ
  have := hV.hM'
  have := hV.hM
  unfold pinField
  linarith

end PoleConst

theorem deltaN_crit {s : ℝ} (hcrit : s = (d : ℝ) / 2) (N : ℕ) :
    deltaN d s N = (N : ℝ)⁻¹ * logEN N := by
  unfold deltaN logEN
  rw [if_neg (by rw [hcrit]; exact lt_irrefl _), if_pos hcrit]

theorem N_mul_deltaN {s : ℝ} (hcrit : s = (d : ℝ) / 2) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) * deltaN d s N = logEN N := by
  rw [deltaN_crit hcrit]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

theorem min_cap_mono {N Cu q w : ℝ} (hN : 0 < N) (hCu : 0 ≤ Cu) (hw : 1 ≤ w) (hq0 : 0 ≤ q)
    (hq : q ≤ Cu * w) :
    min 1 ((1 / N) * (1 + q)) ≤ min 1 (((1 + Cu) / N) * w) := by
  refine min_le_min le_rfl ?_
  have h1 : 1 + q ≤ (1 + Cu) * w := by nlinarith
  calc (1 / N) * (1 + q) ≤ (1 / N) * ((1 + Cu) * w) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((1 + Cu) / N) * w := by ring

theorem lam_log_bound {N n Cu : ℝ} (hN : 1 ≤ N) (hn : 0 ≤ n) (hnN : n ≤ N) (hCu : 0 ≤ Cu) :
    n * (((1 + Cu) / N) * (1 + |Real.log ((1 + Cu) / N)|)) ≤
      (1 + Cu) * ((1 + |Real.log (1 + Cu)|) * (1 + Real.log N)) := by
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have h1 : |Real.log ((1 + Cu) / N)| ≤ |Real.log (1 + Cu)| + Real.log N := by
    rw [Real.log_div (by linarith) hN0.ne']
    calc |Real.log (1 + Cu) - Real.log N| ≤ |Real.log (1 + Cu)| + |Real.log N| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg hlogN]
  have h2 : 1 + |Real.log ((1 + Cu) / N)| ≤ (1 + |Real.log (1 + Cu)|) * (1 + Real.log N) := by
    nlinarith [abs_nonneg (Real.log (1 + Cu)), mul_nonneg (abs_nonneg (Real.log (1 + Cu))) hlogN]
  have h3 : n * ((1 + Cu) / N) ≤ 1 + Cu := by
    rw [mul_div_assoc', div_le_iff₀ hN0]; nlinarith
  calc n * (((1 + Cu) / N) * (1 + |Real.log ((1 + Cu) / N)|))
      = (n * ((1 + Cu) / N)) * (1 + |Real.log ((1 + Cu) / N)|) := by ring
    _ ≤ (1 + Cu) * ((1 + |Real.log (1 + Cu)|) * (1 + Real.log N)) :=
        mul_le_mul h3 h2 (by positivity) (by linarith)

end HRS.PairMom

end
