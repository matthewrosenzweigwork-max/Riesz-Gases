import HRS.MS.MovOscAux1

/-!
# MOV-A1, part 2: ladder bounds on `Σ^r`, monotonicity, log-convexity

Namespace `HRS.MS.MovOsc` (helpers `mova1_`, main statements `mo_`).

* `mo_xmul`, `mo_partial` (all real `r`): for every Schwartz `f` and coordinate `j`,
  `x_j f` resp. `∂_j f` lie in `Σ^r` and `‖x_j f‖_{Σ^r}, ‖∂_j f‖_{Σ^r} ≤ 2^{|r+1|/2} ‖f‖_{Σ^{r+1}}`
  (the constant is uniform in `j`).
  The proof compares the weights `λ_{α±e_j}` with `λ_α` (`λ_{α+e_j} = λ_α + 2`, `λ_{α-e_j} = λ_α - 2`,
  `λ ≥ 2` when `d ≥ 1`) and uses `α_j + 1 ≤ λ_α/2`.
* `mo_mono`: `r ≤ r'`, `f ∈ Σ^{r'}` implies `f ∈ Σ^r`, `‖f‖_{Σ^r} ≤ ‖f‖_{Σ^{r'}}`.
* `mo_logconvex`: `‖f‖_{Σ^{θ r + (1-θ) r'}} ≤ ‖f‖_{Σ^r}^θ ‖f‖_{Σ^{r'}}^{1-θ}` (Hölder for `tsum`).

The Schwartz operators `mova1_X j`, `mova1_D j` (multiplication by `x_j`, derivative `∂_j`) are also set up here.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovOsc

open HRS HRS.Whole

variable {d : ℕ}

/-! ### Weight comparison -/

theorem mova1_rpow_cmp (s : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≤ 2 * b)
    (hba : b ≤ 2 * a) : a ^ s ≤ 2 ^ |s| * b ^ s := by
  rcases le_total 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    calc a ^ s ≤ (2 * b) ^ s := Real.rpow_le_rpow ha.le hab hs
      _ = 2 ^ s * b ^ s := Real.mul_rpow (by norm_num) hb.le
  · rw [abs_of_nonpos hs]
    have h1 : (b / 2) ≤ a := by linarith
    calc a ^ s ≤ (b / 2) ^ s := Real.rpow_le_rpow_of_nonpos (by positivity) h1 hs
      _ = 2 ^ (-s) * b ^ s := by
        rw [Real.div_rpow hb.le (by norm_num), Real.rpow_neg (by norm_num)]
        field_simp

theorem mova1_eigen_ge (j : Fin d) (α : MultiIndex d) :
    2 * (α j : ℝ) + 2 ≤ oscEigenvalue d α := by
  have h1 : α j ≤ α.degree :=
    Finset.single_le_sum (f := α) (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  have h2 : (α j : ℝ) ≤ (α.degree : ℝ) := by exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Fin.pos j))
  unfold oscEigenvalue
  linarith

theorem mova1_eigen_two_le (j : Fin d) (α : MultiIndex d) : 2 ≤ oscEigenvalue d α := by
  have := mova1_eigen_ge j α
  have : (0 : ℝ) ≤ α j := Nat.cast_nonneg _
  linarith

/-! ### The abstract ladder bound on weighted coefficient sequences -/

theorem mova1_ladder_bound (j : Fin d) (r : ℝ) (c e A B : MultiIndex d → ℝ)
    (hA : ∀ α, A α ^ 2 ≤ oscEigenvalue d α / 4) (hB : ∀ α, B α ^ 2 ≤ oscEigenvalue d α / 4)
    (hB0 : ∀ α, α j = 0 → B α = 0)
    (he : ∀ α, e α = A α * c (mova1_up j α) + B α * c (mova1_dn j α))
    (hs : Summable fun β : MultiIndex d => oscEigenvalue d β ^ (r + 1) * c β ^ 2) :
    Summable (fun α : MultiIndex d => oscEigenvalue d α ^ r * e α ^ 2) ∧
      ∑' α : MultiIndex d, oscEigenvalue d α ^ r * e α ^ 2 ≤
        2 ^ |r + 1| * ∑' β : MultiIndex d, oscEigenvalue d β ^ (r + 1) * c β ^ 2 := by
  set u : MultiIndex d → ℝ := fun β => oscEigenvalue d β ^ (r + 1) * c β ^ 2 with hu
  have hu0 : ∀ β, 0 ≤ u β := fun β =>
    mul_nonneg (Real.rpow_nonneg (oscEigenvalue_pos β).le _) (sq_nonneg _)
  set κ : ℝ := 2 ^ |r + 1| with hκ
  have hκ0 : 0 < κ := by positivity
  set T1 : MultiIndex d → ℝ := fun α => u (mova1_up j α) with hT1def
  set T2 : MultiIndex d → ℝ := fun α => if 1 ≤ α j then u (mova1_dn j α) else 0 with hT2def
  have hinj := mova1_up_injective (d := d) j
  have hT1 : Summable T1 := hs.comp_injective hinj
  have hT1le : ∑' α, T1 α ≤ ∑' β, u β := _root_.tsum_comp_le_tsum_of_inj hs hu0 hinj
  have hT2s : ∀ α, T2 (mova1_up j α) = u α := by
    intro α
    simp [T2, mova1_up_apply, mova1_dn_up]
  have hT2supp : ∀ β ∉ Set.range (mova1_up (d := d) j), T2 β = 0 := by
    intro β hβ
    by_cases h : 1 ≤ β j
    · exact absurd (mova1_up_ne_dn_range j β h) hβ
    · simp [T2, h]
  have hT2sum : Summable T2 := by
    refine (hinj.summable_iff hT2supp).1 ?_
    have : (T2 ∘ mova1_up j) = u := funext hT2s
    rw [this]; exact hs
  have hT2eq : ∑' α, T2 α = ∑' β, u β := by
    have h := hinj.tsum_eq (f := T2) (fun β hβ => by
      by_contra h; exact hβ (hT2supp β h))
    rw [← h]
    exact tsum_congr hT2s
  have hT10 : ∀ α, 0 ≤ T1 α := fun α => hu0 _
  have hT20 : ∀ α, 0 ≤ T2 α := fun α => by
    simp only [T2]; split_ifs
    · exact hu0 _
    · exact le_refl _
  have hpt : ∀ α, oscEigenvalue d α ^ r * e α ^ 2 ≤ κ / 2 * (T1 α + T2 α) := by
    intro α
    set a := oscEigenvalue d α with ha
    have ha2 : 2 ≤ a := mova1_eigen_two_le j α
    have ha0 : 0 < a := by linarith
    have har : a ^ (r + 1) = a ^ r * a := Real.rpow_add_one ha0.ne' r
    have har0 : 0 ≤ a ^ r := Real.rpow_nonneg ha0.le r
    -- comparison with the shifted weights
    have hup : a ^ (r + 1) ≤ κ * oscEigenvalue d (mova1_up j α) ^ (r + 1) := by
      have h := mova1_rpow_cmp (r + 1) (a := a) (b := oscEigenvalue d (mova1_up j α)) ha0
        (oscEigenvalue_pos _) (by rw [mova1_eigen_up]; linarith) (by rw [mova1_eigen_up]; linarith)
      exact h
    set p := c (mova1_up j α) with hp
    set q := c (mova1_dn j α) with hq
    have hT1a : T1 α = oscEigenvalue d (mova1_up j α) ^ (r + 1) * p ^ 2 := rfl
    have hup' : a ^ (r + 1) * p ^ 2 ≤ κ * T1 α := by
      rw [hT1a, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right hup (sq_nonneg _)
    have hesq : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := fun x y => by
      nlinarith [sq_nonneg (x - y)]
    by_cases hj : 1 ≤ α j
    · have hT2a : T2 α = oscEigenvalue d (mova1_dn j α) ^ (r + 1) * q ^ 2 := by
        simp [T2, hj, u, hq]
      have hdn : a ^ (r + 1) ≤ κ * oscEigenvalue d (mova1_dn j α) ^ (r + 1) := by
        have h2 := mova1_eigen_dn j α hj
        have h3 := mova1_eigen_two_le j (mova1_dn j α)
        exact mova1_rpow_cmp (r + 1) (a := a) (b := oscEigenvalue d (mova1_dn j α)) ha0
          (oscEigenvalue_pos _) (by linarith) (by linarith)
      have hdn' : a ^ (r + 1) * q ^ 2 ≤ κ * T2 α := by
        rw [hT2a, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right hdn (sq_nonneg _)
      have h1 : e α ^ 2 ≤ a / 2 * p ^ 2 + a / 2 * q ^ 2 := by
        rw [he α]
        refine (hesq _ _).trans ?_
        have h1 : A α ^ 2 * p ^ 2 ≤ a / 4 * p ^ 2 := mul_le_mul_of_nonneg_right (hA α) (sq_nonneg _)
        have h2 : B α ^ 2 * q ^ 2 ≤ a / 4 * q ^ 2 := mul_le_mul_of_nonneg_right (hB α) (sq_nonneg _)
        nlinarith [mul_pow (A α) p 2, mul_pow (B α) q 2]
      calc a ^ r * e α ^ 2 ≤ a ^ r * (a / 2 * p ^ 2 + a / 2 * q ^ 2) :=
            mul_le_mul_of_nonneg_left h1 har0
        _ = (a ^ (r + 1) * p ^ 2 + a ^ (r + 1) * q ^ 2) / 2 := by rw [har]; ring
        _ ≤ (κ * T1 α + κ * T2 α) / 2 := by gcongr
        _ = κ / 2 * (T1 α + T2 α) := by ring
    · have hj0 : α j = 0 := by omega
      have hB00 := hB0 α hj0
      have h1 : e α ^ 2 ≤ a / 4 * p ^ 2 := by
        rw [he α, hB00, zero_mul, add_zero, mul_pow]
        exact mul_le_mul_of_nonneg_right (hA α) (sq_nonneg _)
      calc a ^ r * e α ^ 2 ≤ a ^ r * (a / 4 * p ^ 2) := mul_le_mul_of_nonneg_left h1 har0
        _ = (a ^ (r + 1) * p ^ 2) / 4 := by rw [har]; ring
        _ ≤ (κ * T1 α) / 4 := by gcongr
        _ ≤ κ / 2 * (T1 α + T2 α) := by
          have := hT10 α; have := hT20 α
          nlinarith
  have hsumb : Summable fun α => κ / 2 * (T1 α + T2 α) := (hT1.add hT2sum).mul_left _
  have hnn : ∀ α, 0 ≤ oscEigenvalue d α ^ r * e α ^ 2 := fun α =>
    mul_nonneg (Real.rpow_nonneg (oscEigenvalue_pos α).le _) (sq_nonneg _)
  refine ⟨Summable.of_nonneg_of_le hnn hpt hsumb, ?_⟩
  calc ∑' α, oscEigenvalue d α ^ r * e α ^ 2 ≤ ∑' α, κ / 2 * (T1 α + T2 α) :=
        (Summable.of_nonneg_of_le hnn hpt hsumb).tsum_le_tsum hpt hsumb
    _ = κ / 2 * (∑' α, T1 α + ∑' α, T2 α) := by
        rw [tsum_mul_left, hT1.tsum_add hT2sum]
    _ ≤ κ / 2 * (∑' β, u β + ∑' β, u β) := by
        rw [hT2eq]; gcongr
    _ = κ * ∑' β, u β := by ring

/-! ### Schwartz operators `x_j`, `∂_j` -/

/-- Multiplication by the coordinate `x_j` on Schwartz functions. -/
def mova1_X (j : Fin d) : SchwartzMap (Euc d) ℝ →L[ℝ] SchwartzMap (Euc d) ℝ :=
  SchwartzMap.smulLeftCLM ℝ (fun x : Euc d => x j)

theorem mova1_hasTempGrowth_coord (j : Fin d) : (fun x : Euc d => x j).HasTemperateGrowth :=
  (EuclideanSpace.proj (𝕜 := ℝ) j).hasTemperateGrowth

@[simp] theorem mova1_X_apply (j : Fin d) (f : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    mova1_X j f x = x j * f x := by
  simp [mova1_X, SchwartzMap.smulLeftCLM_apply_apply (mova1_hasTempGrowth_coord j)]

/-- The partial derivative `∂_j` on Schwartz functions. -/
def mova1_D (j : Fin d) : SchwartzMap (Euc d) ℝ →L[ℝ] SchwartzMap (Euc d) ℝ :=
  (SchwartzMap.evalCLM ℝ (Euc d) ℝ (EuclideanSpace.single j (1 : ℝ))).comp
    (SchwartzMap.fderivCLM ℝ (Euc d) ℝ)

@[simp] theorem mova1_D_apply (j : Fin d) (f : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    mova1_D j f x = fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) := rfl

/-! ### `mo_xmul`, `mo_partial` -/

theorem mova1_ladder_memosc (j : Fin d) (r : ℝ) (f : SchwartzMap (Euc d) ℝ) (g : Euc d → ℝ)
    (hg : MemLp g 2 (volume : Measure (Euc d))) (σ : ℝ) (hσ : σ ^ 2 = 1)
    (hc : ∀ α, hermiteCoeff g α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff f (mova1_up j α) +
        σ * Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff f (mova1_dn j α)) :
    MemOsc r g ∧ oscNorm r g ≤ Real.sqrt (2 ^ |r + 1|) * oscNorm (r + 1) f := by
  have hs := (memOsc_schwartz (r + 1) f).2
  have hA : ∀ α : MultiIndex d, Real.sqrt (((α j : ℝ) + 1) / 2) ^ 2 ≤ oscEigenvalue d α / 4 := by
    intro α
    rw [Real.sq_sqrt (by positivity)]
    have := mova1_eigen_ge j α
    linarith
  have hB : ∀ α : MultiIndex d, (σ * Real.sqrt ((α j : ℝ) / 2)) ^ 2 ≤ oscEigenvalue d α / 4 := by
    intro α
    rw [mul_pow, hσ, one_mul, Real.sq_sqrt (by positivity)]
    have := mova1_eigen_ge j α
    have : (0 : ℝ) ≤ α j := Nat.cast_nonneg _
    linarith
  have hB0 : ∀ α : MultiIndex d, α j = 0 → σ * Real.sqrt ((α j : ℝ) / 2) = 0 := by
    intro α h; simp [h]
  obtain ⟨hsum, hle⟩ := mova1_ladder_bound j r (hermiteCoeff f) (hermiteCoeff g)
    (fun α => Real.sqrt (((α j : ℝ) + 1) / 2)) (fun α => σ * Real.sqrt ((α j : ℝ) / 2)) hA hB hB0
    (fun α => hc α) hs
  refine ⟨⟨hg, hsum⟩, ?_⟩
  unfold oscNorm
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hle

/-- **`mo_xmul`.**  For every real `r`: `‖x_j f‖_{Σ^r} ≤ C ‖f‖_{Σ^{r+1}}` for Schwartz `f`, with `x_j f ∈ Σ^r`;
`C = 2^{|r+1|/2}` is uniform in `j`. -/
theorem mo_xmul (r : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin d) (f : SchwartzMap (Euc d) ℝ),
    MemOsc r (fun x => x j * f x) ∧ oscNorm r (fun x => x j * f x) ≤ C * oscNorm (r + 1) f := by
  refine ⟨Real.sqrt (2 ^ |r + 1|), Real.sqrt_nonneg _, fun j f => ?_⟩
  have e : (fun x : Euc d => x j * f x) = ⇑(mova1_X j f) := funext fun x => (mova1_X_apply j f x).symm
  refine mova1_ladder_memosc j r f _ (by rw [e]; exact (mova1_X j f).memLp 2) 1 (by norm_num)
    (fun α => ?_)
  rw [mo_coeff_xmul]; ring

/-- **`mo_partial`.**  For every real `r`: `‖∂_j f‖_{Σ^r} ≤ C ‖f‖_{Σ^{r+1}}` for Schwartz `f`, with `∂_j f ∈ Σ^r`;
`C = 2^{|r+1|/2}` is uniform in `j`. -/
theorem mo_partial (r : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin d) (f : SchwartzMap (Euc d) ℝ),
    MemOsc r (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) ∧
      oscNorm r (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) ≤ C * oscNorm (r + 1) f := by
  refine ⟨Real.sqrt (2 ^ |r + 1|), Real.sqrt_nonneg _, fun j f => ?_⟩
  have e : (fun x : Euc d => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) = ⇑(mova1_D j f) :=
    funext fun x => (mova1_D_apply j f x).symm
  refine mova1_ladder_memosc j r f _ (by rw [e]; exact (mova1_D j f).memLp 2) (-1) (by norm_num)
    (fun α => ?_)
  rw [mo_coeff_partial]; ring

/-! ### Monotonicity and log-convexity -/

theorem mo_mono {r r' : ℝ} (h : r ≤ r') {f : Euc d → ℝ} (hf : MemOsc r' f) :
    MemOsc r f ∧ oscNorm r f ≤ oscNorm r' f := by
  have hle : ∀ α : MultiIndex d, oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 ≤
      oscEigenvalue d α ^ r' * hermiteCoeff f α ^ 2 := fun α =>
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) h)
      (sq_nonneg _)
  have hnn : ∀ α : MultiIndex d, 0 ≤ oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 := fun α =>
    mul_nonneg (Real.rpow_nonneg (oscEigenvalue_pos α).le _) (sq_nonneg _)
  have hs := Summable.of_nonneg_of_le hnn hle hf.2
  exact ⟨⟨hf.1, hs⟩, Real.sqrt_le_sqrt (hs.tsum_le_tsum hle hf.2)⟩

theorem mo_logconvex {r r' θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) {f : Euc d → ℝ} (hf : MemOsc r f)
    (hf' : MemOsc r' f) :
    MemOsc (θ * r + (1 - θ) * r') f ∧
      oscNorm (θ * r + (1 - θ) * r') f ≤ oscNorm r f ^ θ * oscNorm r' f ^ (1 - θ) := by
  set P : MultiIndex d → ℝ := fun α => oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 with hP
  set Q : MultiIndex d → ℝ := fun α => oscEigenvalue d α ^ r' * hermiteCoeff f α ^ 2 with hQ
  have hP0 : ∀ α, 0 ≤ P α := fun α =>
    mul_nonneg (Real.rpow_nonneg (oscEigenvalue_pos α).le _) (sq_nonneg _)
  have hQ0 : ∀ α, 0 ≤ Q α := fun α =>
    mul_nonneg (Real.rpow_nonneg (oscEigenvalue_pos α).le _) (sq_nonneg _)
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · subst h0
    simp only [zero_mul, zero_add, sub_zero, one_mul, Real.rpow_zero, one_mul]
    refine ⟨hf', ?_⟩
    simp [oscNorm]
  rcases eq_or_lt_of_le hθ1 with h1 | h1
  · subst h1
    simp only [one_mul, sub_self, zero_mul, add_zero, Real.rpow_zero, mul_one, Real.rpow_one]
    exact ⟨hf, le_rfl⟩
  have hpq := Real.holderConjugate_one_div h0 (sub_pos.2 h1) (by ring)
  have hs1 : 0 < 1 - θ := sub_pos.2 h1
  set F : MultiIndex d → ℝ := fun α => P α ^ θ with hF
  set G : MultiIndex d → ℝ := fun α => Q α ^ (1 - θ) with hG
  have hF0 : ∀ α, 0 ≤ F α := fun α => Real.rpow_nonneg (hP0 α) _
  have hG0 : ∀ α, 0 ≤ G α := fun α => Real.rpow_nonneg (hQ0 α) _
  have hFp : ∀ α, F α ^ (1 / θ) = P α := by
    intro α
    simp only [hF]
    rw [← Real.rpow_mul (hP0 α), mul_one_div_cancel h0.ne', Real.rpow_one]
  have hGq : ∀ α, G α ^ (1 / (1 - θ)) = Q α := by
    intro α
    simp only [hG]
    rw [← Real.rpow_mul (hQ0 α), mul_one_div_cancel hs1.ne', Real.rpow_one]
  have hFs : Summable fun α => F α ^ (1 / θ) := by simpa only [hFp] using hf.2
  have hGs : Summable fun α => G α ^ (1 / (1 - θ)) := by simpa only [hGq] using hf'.2
  have hprod : ∀ α, F α * G α = oscEigenvalue d α ^ (θ * r + (1 - θ) * r') * hermiteCoeff f α ^ 2 := by
    intro α
    have hl := oscEigenvalue_pos (d := d) α
    have hc0 : 0 ≤ hermiteCoeff f α ^ 2 := sq_nonneg _
    simp only [hF, hG, hP, hQ]
    rw [Real.mul_rpow (Real.rpow_nonneg hl.le _) hc0, Real.mul_rpow (Real.rpow_nonneg hl.le _) hc0,
      ← Real.rpow_mul hl.le, ← Real.rpow_mul hl.le, Real.rpow_add hl]
    have : (hermiteCoeff f α ^ 2) ^ θ * (hermiteCoeff f α ^ 2) ^ (1 - θ) = hermiteCoeff f α ^ 2 := by
      rw [← Real.rpow_add' hc0 (by linarith)]; simp
    calc oscEigenvalue d α ^ (r * θ) * (hermiteCoeff f α ^ 2) ^ θ *
          (oscEigenvalue d α ^ (r' * (1 - θ)) * (hermiteCoeff f α ^ 2) ^ (1 - θ))
        = oscEigenvalue d α ^ (r * θ) * oscEigenvalue d α ^ (r' * (1 - θ)) *
          ((hermiteCoeff f α ^ 2) ^ θ * (hermiteCoeff f α ^ 2) ^ (1 - θ)) := by ring
      _ = _ := by rw [this]; ring_nf
  have hsum := Real.summable_mul_of_Lp_Lq_of_nonneg hpq hF0 hG0 hFs hGs
  have hint := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hF0 hG0 hFs hGs
  have hsum' : Summable fun α : MultiIndex d =>
      oscEigenvalue d α ^ (θ * r + (1 - θ) * r') * hermiteCoeff f α ^ 2 :=
    hsum.congr fun α => hprod α
  refine ⟨⟨hf.1, hsum'⟩, ?_⟩
  have e1 : ∑' α : MultiIndex d, oscEigenvalue d α ^ (θ * r + (1 - θ) * r') * hermiteCoeff f α ^ 2 =
      ∑' α, F α * G α := tsum_congr fun α => (hprod α).symm
  have e2 : (∑' α, F α ^ (1 / θ)) = ∑' α, P α := tsum_congr hFp
  have e3 : (∑' α, G α ^ (1 / (1 - θ))) = ∑' α, Q α := tsum_congr hGq
  rw [e2, e3, one_div_one_div, one_div_one_div] at hint
  have hS0 : 0 ≤ ∑' α, P α := tsum_nonneg hP0
  have hT0 : 0 ≤ ∑' α, Q α := tsum_nonneg hQ0
  unfold oscNorm
  rw [e1]
  calc Real.sqrt (∑' α, F α * G α)
      ≤ Real.sqrt ((∑' α, P α) ^ θ * (∑' α, Q α) ^ (1 - θ)) := Real.sqrt_le_sqrt hint
    _ = Real.sqrt (∑' α, P α) ^ θ * Real.sqrt (∑' α, Q α) ^ (1 - θ) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
          Real.mul_rpow (Real.rpow_nonneg hS0 _) (Real.rpow_nonneg hT0 _),
          ← Real.rpow_mul hS0, ← Real.rpow_mul hT0, ← Real.rpow_mul hS0, ← Real.rpow_mul hT0]
        ring_nf

end HRS.MS.MovOsc
