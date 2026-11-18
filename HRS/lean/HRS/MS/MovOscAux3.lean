import HRS.MS.MovOscAux2

/-!
# MOV-A1, part 3: monomial operators `x^a ∂^γ` and the integer equivalence `mo_int_equiv`

Namespace `HRS.MS.MovOsc` (helpers `mova1_`, main statements `mo_`).

Definitions (documented because they enter the statement of `mo_int_equiv`):
* `mo_xpow a x = ∏ᵢ xᵢ^{aᵢ}`;
* `mo_pd γ f = ∂^γ f`, the iterated partial derivative of a Schwartz function, realised as
  `(∂_0)^{γ_0} ((∂_1)^{γ_1} (⋯ f))` (the partial derivatives commute: `mova1_D_comm`; the key identity
  `∂_i ∂^γ f = ∂^{γ+e_i} f` is `mova1_D_pd`);
* `mo_idx d n = {(a, γ) : |a| + |γ| ≤ n}` as a `Finset`.

Contents: commutation of the `∂_i`, the Leibniz rule `∂_i (x^a g) = x^a ∂_i g + a_i x^{a-e_i} g`,
`Bnd k T` ("`T` loses `k` orders on the `Σ^s` scale"), closure of `Bnd` under composition and the ladder
operators, and the upper integer bound `‖x^a ∂^γ f‖_2 ≤ C ‖f‖_{Σ^n}` for `|a| + |γ| ≤ n`.

Lower bound (`‖f‖_{Σ^n} ≤ C ∑ ‖x^a ∂^γ f‖_2`): `mova1_rec_step` shows
`‖f‖_{Σ^{s+1}} ≤ √(d+1) ‖f‖_{Σ^s} + 2^{|s|/2} ∑_j ‖(x_j + ∂_j) f‖_{Σ^s}`
(since `c_α((x_j + ∂_j) f) = 2 √((α_j+1)/2) c_{α+e_j}(f)` and `λ_β = d + 1 + 2 ∑_j β_j`); iterating gives
`‖f‖_{Σ^n} ≤ C W_n(f)` with `W_n` the sum of `L²` norms of all words in `x_j + ∂_j` (`mova1_W`), and
`mova1_W_le` rewrites every word as a normal-ordered combination (`mova1_IsLow`, closed under left
multiplication by `x_j` and `∂_j` by the Leibniz rule).  `mo_int_equiv` combines both bounds.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovOsc

open HRS HRS.Whole

variable {d : ℕ}

local notation "𝒮" => SchwartzMap (Euc d) ℝ

/-! ### Commutation of the partial derivatives -/

theorem mova1_D_comm_apply (i k : Fin d) (g : 𝒮) (x : Euc d) :
    mova1_D i (mova1_D k g) x =
      fderiv ℝ (fderiv ℝ (⇑g)) x (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single k (1 : ℝ)) := by
  rw [mova1_D_apply]
  have e : (⇑(mova1_D k g) : Euc d → ℝ) =
      fun y => (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k (1 : ℝ) : Euc d))
        (fderiv ℝ (⇑g) y) := by
    funext y; rw [mova1_D_apply]; rfl
  rw [e]
  have h1 : DifferentiableAt ℝ (fun y => fderiv ℝ (⇑g) y) x :=
    (SchwartzMap.fderivCLM ℝ (Euc d) ℝ g).differentiableAt
  have h2 := (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k (1 : ℝ) : Euc d)).hasFDerivAt.comp
    x h1.hasFDerivAt
  have h3 : fderiv ℝ (fun y => (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k (1 : ℝ) : Euc d))
        (fderiv ℝ (⇑g) y)) x =
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single k (1 : ℝ) : Euc d)).comp
        (fderiv ℝ (fderiv ℝ (⇑g)) x) := h2.fderiv
  rw [h3]
  rfl

theorem mova1_D_comm (i k : Fin d) (g : 𝒮) : mova1_D i (mova1_D k g) = mova1_D k (mova1_D i g) := by
  ext x
  rw [mova1_D_comm_apply, mova1_D_comm_apply]
  have hs : IsSymmSndFDerivAt ℝ (⇑g) x := (g.contDiffAt 2).isSymmSndFDerivAt (by simp)
  exact hs _ _

theorem mova1_D_fun_comm (i k : Fin d) : Function.Commute (mova1_D i) (mova1_D k) :=
  fun g => mova1_D_comm i k g

/-! ### `∂^γ` -/

/-- `∂^γ f = (∂_0)^{γ_0} ((∂_1)^{γ_1} ⋯ f)`. -/
def mo_pd (γ : MultiIndex d) (f : 𝒮) : 𝒮 :=
  (List.finRange d).foldr (fun i g => (mova1_D i)^[γ i] g) f

theorem mova1_foldr_congr (l : List (Fin d)) (γ γ' : MultiIndex d) (h : ∀ k ∈ l, γ k = γ' k)
    (f : 𝒮) :
    l.foldr (fun k g => (mova1_D k)^[γ k] g) f = l.foldr (fun k g => (mova1_D k)^[γ' k] g) f := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    simp only [List.foldr_cons]
    rw [h k List.mem_cons_self, ih (fun k' hk' => h k' (List.mem_cons_of_mem _ hk'))]

theorem mova1_foldr_D (l : List (Fin d)) (hl : l.Nodup) (i : Fin d) (hi : i ∈ l) (γ : MultiIndex d)
    (f : 𝒮) :
    mova1_D i (l.foldr (fun k g => (mova1_D k)^[γ k] g) f) =
      l.foldr (fun k g => (mova1_D k)^[mova1_up i γ k] g) f := by
  induction l with
  | nil => simp at hi
  | cons k l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    by_cases hik : i = k
    · subst hik
      have hnot : i ∉ l := hl.1
      have hcongr : l.foldr (fun k' g => (mova1_D k')^[mova1_up i γ k'] g) f =
          l.foldr (fun k' g => (mova1_D k')^[γ k'] g) f := by
        refine (mova1_foldr_congr l _ _ (fun k' hk' => ?_) f).symm
        have : k' ≠ i := fun h => hnot (h ▸ hk')
        simp [mova1_up, Function.update_of_ne this]
      rw [hcongr, mova1_up_apply, ← Function.iterate_succ_apply' (mova1_D i)]
    · have hil : i ∈ l := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h hik
        · exact h
      rw [(mova1_D_fun_comm i k).iterate_right (γ k), ih hl.2 hil]
      have : mova1_up i γ k = γ k := by simp [mova1_up, Function.update_of_ne (Ne.symm hik)]
      rw [this]

/-- `∂_i ∂^γ f = ∂^{γ+e_i} f`. -/
theorem mova1_D_pd (i : Fin d) (γ : MultiIndex d) (f : 𝒮) :
    mova1_D i (mo_pd γ f) = mo_pd (mova1_up i γ) f :=
  mova1_foldr_D (List.finRange d) (List.nodup_finRange d) i (List.mem_finRange i) γ f

theorem mova1_pd_zero (f : 𝒮) : mo_pd (0 : MultiIndex d) f = f := by
  unfold mo_pd
  induction (List.finRange d) with
  | nil => rfl
  | cons k l ih => simp

/-! ### Monomials `x^a` -/

/-- `x^a = ∏ᵢ xᵢ^{aᵢ}`. -/
def mo_xpow (a : MultiIndex d) (x : Euc d) : ℝ := ∏ i, x i ^ a i

theorem mova1_tg_xpow (a : MultiIndex d) : (mo_xpow a).HasTemperateGrowth := by
  have e : mo_xpow a = ∏ i, (fun x : Euc d => x i ^ a i) := by
    funext x; simp [mo_xpow, Finset.prod_apply]
  rw [e]
  refine Finset.prod_induction _ (fun F : Euc d → ℝ => F.HasTemperateGrowth)
    (fun f g hf hg => hf.mul hg) ?_ (fun i _ => (mova1_hasTempGrowth_coord i).pow _)
  exact Function.HasTemperateGrowth.const (1 : ℝ)

/-- Multiplication by the monomial `x^a` on Schwartz functions. -/
def mova1_xm (a : MultiIndex d) : 𝒮 →L[ℝ] 𝒮 := SchwartzMap.smulLeftCLM ℝ (mo_xpow a)

@[simp] theorem mova1_xm_apply (a : MultiIndex d) (g : 𝒮) (x : Euc d) :
    mova1_xm a g x = mo_xpow a x * g x := by
  simp [mova1_xm, SchwartzMap.smulLeftCLM_apply_apply (mova1_tg_xpow a)]

theorem mova1_xpow_zero (x : Euc d) : mo_xpow (0 : MultiIndex d) x = 1 := by simp [mo_xpow]

theorem mova1_xm_zero (g : 𝒮) : mova1_xm (0 : MultiIndex d) g = g := by
  ext x; simp [mova1_xpow_zero]

theorem mova1_xpow_up (j : Fin d) (a : MultiIndex d) (x : Euc d) :
    mo_xpow (mova1_up j a) x = x j * mo_xpow a x := by
  unfold mo_xpow mova1_up
  rw [mova1_prod_update (fun k n => x k ^ n) a j (a j + 1), mova1_prod_self (fun k n => x k ^ n) a j]
  ring

theorem mova1_xpow_dn (j : Fin d) (a : MultiIndex d) (x : Euc d) :
    mo_xpow (mova1_dn j a) x = (∏ k ∈ Finset.univ.erase j, x k ^ a k) * x j ^ (a j - 1) := by
  unfold mo_xpow mova1_dn
  exact mova1_prod_update (fun k n => x k ^ n) a j (a j - 1)

theorem mova1_X_xm (j : Fin d) (a : MultiIndex d) (g : 𝒮) :
    mova1_X j (mova1_xm a g) = mova1_xm (mova1_up j a) g := by
  ext x
  simp [mova1_xpow_up]
  ring

theorem mova1_hasLineDerivAt_xpow (a : MultiIndex d) (i : Fin d) (x : Euc d) :
    HasLineDerivAt ℝ (mo_xpow a) ((a i : ℝ) * mo_xpow (mova1_dn i a) x) x
      (EuclideanSpace.single i (1 : ℝ)) := by
  have hfun : mo_xpow a = fun y : Euc d => (∏ k ∈ Finset.univ.erase i, y k ^ a k) * y i ^ a i := by
    funext y; exact mova1_prod_self (fun k n => y k ^ n) a i
  have h := hasLineDerivAt_coord_mul i (fun y : Euc d => ∏ k ∈ Finset.univ.erase i, y k ^ a k)
    (fun x t => prod_erase_indep i (fun k y => y ^ a k) x t) (fun y => y ^ a i)
    (fun y => (a i : ℝ) * y ^ (a i - 1)) (fun y => hasDerivAt_pow (a i) y) x
  rw [hfun, mova1_xpow_dn]
  have e : (a i : ℝ) * ((∏ k ∈ Finset.univ.erase i, x k ^ a k) * x i ^ (a i - 1)) =
      (∏ k ∈ Finset.univ.erase i, x k ^ a k) * ((a i : ℝ) * x i ^ (a i - 1)) := by ring
  rw [e]
  exact h

/-- Leibniz rule `∂_i (x^a g) = x^a ∂_i g + a_i x^{a-e_i} g`. -/
theorem mova1_D_xm (i : Fin d) (a : MultiIndex d) (g : 𝒮) :
    mova1_D i (mova1_xm a g) = mova1_xm a (mova1_D i g) + (a i : ℝ) • mova1_xm (mova1_dn i a) g := by
  ext x
  have hM := mova1_hasLineDerivAt_xpow a i x
  have hg : HasLineDerivAt ℝ (⇑g) (fderiv ℝ (⇑g) x (EuclideanSpace.single i (1 : ℝ))) x
      (EuclideanSpace.single i (1 : ℝ)) := by
    have h := ((g.differentiableAt (x := x)).lineDifferentiableAt (v := EuclideanSpace.single i (1 : ℝ))).hasLineDerivAt
    rwa [(g.differentiableAt (x := x)).lineDeriv_eq_fderiv] at h
  have hprod : HasLineDerivAt ℝ (fun y => mo_xpow a y * g y)
      (mo_xpow a x * fderiv ℝ (⇑g) x (EuclideanSpace.single i (1 : ℝ)) +
        g x * ((a i : ℝ) * mo_xpow (mova1_dn i a) x)) x (EuclideanSpace.single i (1 : ℝ)) := by
    have h := HasDerivAt.mul hM hg
    unfold HasLineDerivAt
    refine h.congr_deriv ?_
    simp only [zero_smul, add_zero]
    ring
  have e : (⇑(mova1_xm a g) : Euc d → ℝ) = fun y => mo_xpow a y * g y := by
    funext y; simp
  have h1 := hprod.lineDeriv
  rw [← e] at h1
  have h2 : lineDeriv ℝ (⇑(mova1_xm a g)) x (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ (⇑(mova1_xm a g)) x (EuclideanSpace.single i (1 : ℝ)) :=
    (mova1_xm a g).differentiableAt.lineDeriv_eq_fderiv
  rw [mova1_D_apply, ← h2, h1]
  simp
  ring

theorem mova1_dn_degree_le (j : Fin d) (a : MultiIndex d) :
    (mova1_dn j a).degree ≤ a.degree := by
  by_cases h : 1 ≤ a j
  · have := mova1_dn_degree j a h; omega
  · have h0 : a j = 0 := by omega
    have : mova1_dn j a = a := by
      funext i
      by_cases hi : i = j
      · subst hi; simp [mova1_dn, h0]
      · simp [mova1_dn, Function.update_of_ne hi]
    rw [this]

/-! ### The `L²` norm, the index set, and `mo_S` -/

/-- The `L²(ℝ^d)` norm `‖g‖₂ = (∫ g²)^{1/2}` (for `g ∈ L²`; junk-free for the functions used below). -/
def mo_l2 (g : Euc d → ℝ) : ℝ := Real.sqrt (∫ x, g x ^ 2)

/-- The multi-indices `{(a, γ) : |a| + |γ| ≤ n}`. -/
def mo_idx (d n : ℕ) : Finset (MultiIndex d × MultiIndex d) :=
  ((Fintype.piFinset fun _ : Fin d => Finset.range (n + 1)) ×ˢ
    (Fintype.piFinset fun _ : Fin d => Finset.range (n + 1))).filter
    (fun p => MultiIndex.degree p.1 + MultiIndex.degree p.2 ≤ n)

theorem mova1_le_degree (a : MultiIndex d) (i : Fin d) : a i ≤ MultiIndex.degree a :=
  Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem mem_mo_idx {n : ℕ} {p : MultiIndex d × MultiIndex d} :
    p ∈ mo_idx d n ↔ MultiIndex.degree p.1 + MultiIndex.degree p.2 ≤ n := by
  unfold mo_idx
  rw [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, Fintype.mem_piFinset]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨⟨fun i => ?_, fun i => ?_⟩, h⟩
    · have := mova1_le_degree p.1 i
      rw [Finset.mem_range]; omega
    · have := mova1_le_degree p.2 i
      rw [Finset.mem_range]; omega

theorem mo_idx_mono {m n : ℕ} (h : m ≤ n) : mo_idx d m ⊆ mo_idx d n := by
  intro p hp
  rw [mem_mo_idx] at hp ⊢
  omega

/-- `S_n(f) = ∑_{|a|+|γ| ≤ n} ‖x^a ∂^γ f‖₂`. -/
def mo_S (n : ℕ) (f : 𝒮) : ℝ :=
  ∑ p ∈ mo_idx d n, mo_l2 (fun x => mo_xpow p.1 x * mo_pd p.2 f x)

theorem mo_l2_nonneg (g : Euc d → ℝ) : 0 ≤ mo_l2 g := Real.sqrt_nonneg _

theorem mo_S_nonneg (n : ℕ) (f : 𝒮) : 0 ≤ mo_S n f :=
  Finset.sum_nonneg fun _ _ => mo_l2_nonneg _

theorem mo_S_mono {m n : ℕ} (h : m ≤ n) (f : 𝒮) : mo_S m f ≤ mo_S n f :=
  Finset.sum_le_sum_of_subset_of_nonneg (mo_idx_mono h) fun _ _ _ => mo_l2_nonneg _

/-- The `L²` norm of a Schwartz function, as the norm of its `Lp` class. -/
def mova1_n2 (g : 𝒮) : ℝ := ‖g.toLp 2 volume‖

theorem mova1_n2_eq (g : 𝒮) : mova1_n2 g = mo_l2 g := by
  unfold mova1_n2 mo_l2
  rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
  rw [Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq_abs]

theorem mova1_n2_add (g h : 𝒮) : mova1_n2 (g + h) ≤ mova1_n2 g + mova1_n2 h := by
  unfold mova1_n2
  have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure (Euc d))).map_add g h
  simp only [SchwartzMap.toLpCLM_apply] at this
  rw [this]
  exact norm_add_le _ _

theorem mova1_n2_smul (c : ℝ) (g : 𝒮) : mova1_n2 (c • g) = |c| * mova1_n2 g := by
  unfold mova1_n2
  have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure (Euc d))).map_smul c g
  simp only [SchwartzMap.toLpCLM_apply] at this
  rw [this, norm_smul, Real.norm_eq_abs]

theorem mova1_n2_nonneg (g : 𝒮) : 0 ≤ mova1_n2 g := norm_nonneg _

/-! ### Normal-ordered combinations -/

/-- A term `(c, a, γ)` stands for `c x^a ∂^γ`. -/
abbrev mova1_Term (d : ℕ) := ℝ × MultiIndex d × MultiIndex d

def mova1_eval (t : mova1_Term d) (f : 𝒮) : 𝒮 := t.1 • mova1_xm t.2.1 (mo_pd t.2.2 f)

def mova1_Lsum (L : List (mova1_Term d)) (f : 𝒮) : 𝒮 := (L.map fun t => mova1_eval t f).sum

/-- `T` is a finite combination of `x^a ∂^γ` with `|a| + |γ| ≤ m`. -/
def mova1_IsLow (m : ℕ) (T : 𝒮 → 𝒮) : Prop :=
  ∃ L : List (mova1_Term d), (∀ t ∈ L, MultiIndex.degree t.2.1 + MultiIndex.degree t.2.2 ≤ m) ∧
    ∀ f, T f = mova1_Lsum L f

@[simp] theorem mova1_Lsum_nil (f : 𝒮) : mova1_Lsum ([] : List (mova1_Term d)) f = 0 := by
  simp [mova1_Lsum]

@[simp] theorem mova1_Lsum_cons (t : mova1_Term d) (L : List (mova1_Term d)) (f : 𝒮) :
    mova1_Lsum (t :: L) f = mova1_eval t f + mova1_Lsum L f := by
  simp [mova1_Lsum]

theorem mova1_Lsum_append (L L' : List (mova1_Term d)) (f : 𝒮) :
    mova1_Lsum (L ++ L') f = mova1_Lsum L f + mova1_Lsum L' f := by
  simp [mova1_Lsum]

theorem mova1_low_id : mova1_IsLow 0 (fun f : 𝒮 => f) := by
  refine ⟨[((1 : ℝ), (0 : MultiIndex d), (0 : MultiIndex d))], ?_, fun f => ?_⟩
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    simp [MultiIndex.degree]
  · simp [mova1_eval, mova1_xm_zero, mova1_pd_zero]

theorem mova1_low_mono {m m' : ℕ} {T : 𝒮 → 𝒮} (h : mova1_IsLow m T) (hm : m ≤ m') :
    mova1_IsLow m' T := by
  obtain ⟨L, hL, hT⟩ := h
  exact ⟨L, fun t ht => (hL t ht).trans hm, hT⟩

theorem mova1_low_add {m : ℕ} {T T' : 𝒮 → 𝒮} (h : mova1_IsLow m T) (h' : mova1_IsLow m T') :
    mova1_IsLow m (fun f => T f + T' f) := by
  obtain ⟨L, hL, hT⟩ := h
  obtain ⟨L', hL', hT'⟩ := h'
  refine ⟨L ++ L', fun t ht => ?_, fun f => ?_⟩
  · rcases List.mem_append.1 ht with h | h
    · exact hL t h
    · exact hL' t h
  · dsimp only
    rw [mova1_Lsum_append, hT, hT']

theorem mova1_X_Lsum (j : Fin d) (L : List (mova1_Term d)) (f : 𝒮) :
    mova1_X j (mova1_Lsum L f) =
      mova1_Lsum (L.map fun t => (t.1, mova1_up j t.2.1, t.2.2)) f := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [mova1_Lsum_cons, List.map_cons, map_add, ih]
    congr 1
    simp [mova1_eval, mova1_X_xm]

theorem mova1_low_X {m : ℕ} {T : 𝒮 → 𝒮} (h : mova1_IsLow m T) (j : Fin d) :
    mova1_IsLow (m + 1) (fun f => mova1_X j (T f)) := by
  obtain ⟨L, hL, hT⟩ := h
  refine ⟨L.map fun t => (t.1, mova1_up j t.2.1, t.2.2), ?_, fun f => ?_⟩
  · intro t ht
    obtain ⟨t0, ht0, rfl⟩ := List.mem_map.1 ht
    have := hL t0 ht0
    simp only [mova1_up_degree]
    omega
  · dsimp only
    rw [hT, mova1_X_Lsum]

/-- The Leibniz expansion of `∂_j` on a list of terms. -/
def mova1_Dlist (j : Fin d) (L : List (mova1_Term d)) : List (mova1_Term d) :=
  L.flatMap fun t => [(t.1, t.2.1, mova1_up j t.2.2), (t.1 * (t.2.1 j : ℝ), mova1_dn j t.2.1, t.2.2)]

theorem mova1_D_Lsum (j : Fin d) (L : List (mova1_Term d)) (f : 𝒮) :
    mova1_D j (mova1_Lsum L f) = mova1_Lsum (mova1_Dlist j L) f := by
  induction L with
  | nil => simp [mova1_Dlist]
  | cons t L ih =>
    have e : mova1_Dlist j (t :: L) =
        [(t.1, t.2.1, mova1_up j t.2.2), (t.1 * (t.2.1 j : ℝ), mova1_dn j t.2.1, t.2.2)] ++
          mova1_Dlist j L := by
      simp [mova1_Dlist]
    rw [e, mova1_Lsum_append, mova1_Lsum_cons, map_add, ih]
    congr 1
    simp only [mova1_eval, map_smul, mova1_D_xm, mova1_D_pd, mova1_Lsum_cons, mova1_Lsum_nil,
      smul_add, add_zero, smul_smul]

theorem mova1_low_D {m : ℕ} {T : 𝒮 → 𝒮} (h : mova1_IsLow m T) (j : Fin d) :
    mova1_IsLow (m + 1) (fun f => mova1_D j (T f)) := by
  obtain ⟨L, hL, hT⟩ := h
  refine ⟨mova1_Dlist j L, ?_, fun f => ?_⟩
  · intro t ht
    unfold mova1_Dlist at ht
    obtain ⟨t0, ht0, ht1⟩ := List.mem_flatMap.1 ht
    have := hL t0 ht0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht1
    rcases ht1 with rfl | rfl
    · simp only [mova1_up_degree]; omega
    · have := mova1_dn_degree_le j t0.2.1
      simp only; omega
  · dsimp only
    rw [hT, mova1_D_Lsum]

theorem mova1_low_G {m : ℕ} {T : 𝒮 → 𝒮} (h : mova1_IsLow m T) (j : Fin d) :
    mova1_IsLow (m + 1) (fun f => mova1_X j (T f) + mova1_D j (T f)) :=
  mova1_low_add (mova1_low_X h j) (mova1_low_D h j)

theorem mova1_n2_term_le {m : ℕ} (a γ : MultiIndex d) (h : MultiIndex.degree a + MultiIndex.degree γ ≤ m)
    (f : 𝒮) : mova1_n2 (mova1_xm a (mo_pd γ f)) ≤ mo_S m f := by
  rw [mova1_n2_eq]
  unfold mo_S
  have e : (⇑(mova1_xm a (mo_pd γ f)) : Euc d → ℝ) = fun x => mo_xpow a x * mo_pd γ f x :=
    funext fun x => mova1_xm_apply a _ x
  rw [e]
  have hmem : (a, γ) ∈ mo_idx d m := mem_mo_idx.2 h
  have := Finset.single_le_sum (f := fun p : MultiIndex d × MultiIndex d =>
    mo_l2 (fun x => mo_xpow p.1 x * mo_pd p.2 f x)) (fun p _ => mo_l2_nonneg _) hmem
  simpa using this

theorem mova1_low_bound {m : ℕ} {T : 𝒮 → 𝒮} (h : mova1_IsLow m T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f, mova1_n2 (T f) ≤ K * mo_S m f := by
  obtain ⟨L, hL, hT⟩ := h
  have key : ∀ L : List (mova1_Term d),
      (∀ t ∈ L, MultiIndex.degree t.2.1 + MultiIndex.degree t.2.2 ≤ m) →
      ∀ f, mova1_n2 (mova1_Lsum L f) ≤ (L.map fun t => |t.1|).sum * mo_S m f := by
    intro L
    induction L with
    | nil =>
      intro _ f
      have : mova1_n2 (0 : 𝒮) = 0 := by
        have := mova1_n2_smul 0 (0 : 𝒮)
        simpa using this
      simp [this]
    | cons t L ih =>
      intro hL f
      rw [mova1_Lsum_cons]
      refine (mova1_n2_add _ _).trans ?_
      have h1 : mova1_n2 (mova1_eval t f) ≤ |t.1| * mo_S m f := by
        unfold mova1_eval
        rw [mova1_n2_smul]
        exact mul_le_mul_of_nonneg_left (mova1_n2_term_le _ _ (hL t List.mem_cons_self) f) (abs_nonneg _)
      have h2 := ih (fun t' ht' => hL t' (List.mem_cons_of_mem _ ht')) f
      simp only [List.map_cons, List.sum_cons]
      nlinarith
  refine ⟨(L.map fun t => |t.1|).sum, ?_, fun f => ?_⟩
  · exact List.sum_nonneg (fun x hx => by
      obtain ⟨t, _, rfl⟩ := List.mem_map.1 hx
      exact abs_nonneg _)
  · rw [hT]; exact key L hL f

/-! ### Order loss: `Bnd k T` -/

/-- `T` loses `k` orders on the `Σ^s` scale (for every real `s`, with a constant depending on `s`). -/
def mova1_Bnd (k : ℕ) (T : 𝒮 → 𝒮) : Prop :=
  ∀ s : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝒮, oscNorm s (T f) ≤ C * oscNorm (s + k) f

theorem mova1_Bnd_id : mova1_Bnd 0 (fun f : 𝒮 => f) := fun s => ⟨1, zero_le_one, fun f => by simp⟩

theorem mova1_Bnd_congr {k k' : ℕ} {T T' : 𝒮 → 𝒮} (hk : k = k') (hT : ∀ f, T f = T' f)
    (h : mova1_Bnd k T) : mova1_Bnd k' T' := by
  subst hk
  intro s
  obtain ⟨C, hC, h⟩ := h s
  exact ⟨C, hC, fun f => by rw [← hT f]; exact h f⟩

theorem mova1_Bnd_comp {k k' : ℕ} {T T' : 𝒮 → 𝒮} (h : mova1_Bnd k T) (h' : mova1_Bnd k' T') :
    mova1_Bnd (k + k') (fun f => T (T' f)) := by
  intro s
  obtain ⟨C, hC, hCb⟩ := h s
  obtain ⟨C', hC', hCb'⟩ := h' (s + k)
  refine ⟨C * C', mul_nonneg hC hC', fun f => ?_⟩
  calc oscNorm s (T (T' f)) ≤ C * oscNorm (s + k) (T' f) := hCb _
    _ ≤ C * (C' * oscNorm (s + k + k') f) := mul_le_mul_of_nonneg_left (hCb' f) hC
    _ = C * C' * oscNorm (s + ((k + k' : ℕ) : ℝ)) f := by push_cast; ring_nf

theorem mova1_Bnd_X (j : Fin d) : mova1_Bnd 1 (fun f : 𝒮 => mova1_X j f) := by
  intro s
  obtain ⟨C, hC, h⟩ := mo_xmul (d := d) s
  refine ⟨C, hC, fun f => ?_⟩
  have e : (⇑(mova1_X j f) : Euc d → ℝ) = fun x => x j * f x :=
    funext fun x => mova1_X_apply j f x
  rw [e]
  simpa using (h j f).2

theorem mova1_Bnd_D (j : Fin d) : mova1_Bnd 1 (fun f : 𝒮 => mova1_D j f) := by
  intro s
  obtain ⟨C, hC, h⟩ := mo_partial (d := d) s
  refine ⟨C, hC, fun f => ?_⟩
  have e : (⇑(mova1_D j f) : Euc d → ℝ) =
      fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) :=
    funext fun x => mova1_D_apply j f x
  rw [e]
  simpa using (h j f).2

theorem mova1_degree_eq_zero {a : MultiIndex d} (h : MultiIndex.degree a = 0) : a = 0 := by
  funext i
  have := mova1_le_degree a i
  simp only [Pi.zero_apply]; omega

theorem mova1_exists_pos {a : MultiIndex d} {n : ℕ} (h : MultiIndex.degree a = n + 1) :
    ∃ j, 1 ≤ a j := by
  by_contra hcon
  push Not at hcon
  have : MultiIndex.degree a = 0 := by
    unfold MultiIndex.degree
    exact Finset.sum_eq_zero fun i _ => by have := hcon i; omega
  omega

theorem mova1_Bnd_pd : ∀ (n : ℕ) (γ : MultiIndex d), MultiIndex.degree γ = n →
    mova1_Bnd n (fun f : 𝒮 => mo_pd γ f) := by
  intro n
  induction n with
  | zero =>
    intro γ hγ
    rw [mova1_degree_eq_zero hγ]
    exact mova1_Bnd_congr rfl (fun f => (mova1_pd_zero f).symm) mova1_Bnd_id
  | succ n ih =>
    intro γ hγ
    obtain ⟨j, hj⟩ := mova1_exists_pos hγ
    have hdeg := mova1_dn_degree j γ hj
    have h1 := mova1_Bnd_comp (mova1_Bnd_D j) (ih (mova1_dn j γ) (by omega))
    refine mova1_Bnd_congr (by omega) (fun f => ?_) h1
    rw [mova1_D_pd, mova1_up_dn j γ hj]

theorem mova1_Bnd_xm : ∀ (n : ℕ) (a : MultiIndex d), MultiIndex.degree a = n →
    mova1_Bnd n (fun f : 𝒮 => mova1_xm a f) := by
  intro n
  induction n with
  | zero =>
    intro a ha
    rw [mova1_degree_eq_zero ha]
    exact mova1_Bnd_congr rfl (fun f => (mova1_xm_zero f).symm) mova1_Bnd_id
  | succ n ih =>
    intro a ha
    obtain ⟨j, hj⟩ := mova1_exists_pos ha
    have hdeg := mova1_dn_degree j a hj
    have h1 := mova1_Bnd_comp (mova1_Bnd_X j) (ih (mova1_dn j a) (by omega))
    refine mova1_Bnd_congr (by omega) (fun f => ?_) h1
    rw [mova1_X_xm, mova1_up_dn j a hj]

theorem mova1_Bnd_term (a γ : MultiIndex d) :
    mova1_Bnd (MultiIndex.degree a + MultiIndex.degree γ) (fun f : 𝒮 => mova1_xm a (mo_pd γ f)) :=
  mova1_Bnd_comp (mova1_Bnd_xm _ a rfl) (mova1_Bnd_pd _ γ rfl)

/-- Upper integer bound: `S_n(f) ≤ C ‖f‖_{Σ^n}`. -/
theorem mova1_upper (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝒮, mo_S n f ≤ C * oscNorm n f := by
  have h1 : ∀ p ∈ mo_idx d n, ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝒮,
      mo_l2 (fun x => mo_xpow p.1 x * mo_pd p.2 f x) ≤ C * oscNorm n f := by
    intro p hp
    have hk := mem_mo_idx.1 hp
    obtain ⟨C, hC, hB⟩ := mova1_Bnd_term p.1 p.2 0
    refine ⟨C, hC, fun f => ?_⟩
    have e : (⇑(mova1_xm p.1 (mo_pd p.2 f)) : Euc d → ℝ) = fun x => mo_xpow p.1 x * mo_pd p.2 f x :=
      funext fun x => mova1_xm_apply p.1 _ x
    have h0 := oscNorm_zero (fun x => mo_xpow p.1 x * mo_pd p.2 f x)
      (by rw [← e]; exact (mova1_xm p.1 (mo_pd p.2 f)).memLp 2)
    have h2 : oscNorm 0 (fun x => mo_xpow p.1 x * mo_pd p.2 f x) ≤
        C * oscNorm (0 + ((MultiIndex.degree p.1 + MultiIndex.degree p.2 : ℕ) : ℝ)) f := by
      have := hB f
      rwa [← e]
    have h3 : oscNorm (0 + ((MultiIndex.degree p.1 + MultiIndex.degree p.2 : ℕ) : ℝ)) f ≤ oscNorm n f := by
      refine (mo_mono ?_ (memOsc_schwartz (n : ℝ) f)).2
      have : ((MultiIndex.degree p.1 + MultiIndex.degree p.2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hk
      linarith
    unfold mo_l2
    rw [← h0]
    exact h2.trans (mul_le_mul_of_nonneg_left h3 hC)
  choose! Cp hCp0 hCp using h1
  refine ⟨∑ p ∈ mo_idx d n, Cp p, Finset.sum_nonneg fun p hp => (hCp0 p hp), fun f => ?_⟩
  unfold mo_S
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun p hp => hCp p hp f

/-! ### The recursion step: `‖f‖_{Σ^{s+1}} ≲ ‖f‖_{Σ^s} + ∑_j ‖(x_j + ∂_j) f‖_{Σ^s}` -/

theorem mova1_hermiteCoeff_add (g₁ g₂ : 𝒮) (α : MultiIndex d) :
    hermiteCoeff (⇑(g₁ + g₂)) α = hermiteCoeff (⇑g₁) α + hermiteCoeff (⇑g₂) α := by
  unfold hermiteCoeff
  have I1 := int_schwartz_mul g₁ _ (hermiteFunD_poly α).1 (hermiteFunD_poly α).2
  have I2 := int_schwartz_mul g₂ _ (hermiteFunD_poly α).1 (hermiteFunD_poly α).2
  rw [← integral_add I1 I2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [add_apply]
  ring

/-- `c_α((x_j + ∂_j) f) = 2 √((α_j+1)/2) c_{α+e_j}(f)`. -/
theorem mova1_coeff_G (j : Fin d) (f : 𝒮) (α : MultiIndex d) :
    hermiteCoeff (⇑(mova1_X j f + mova1_D j f)) α =
      2 * Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff (⇑f) (mova1_up j α) := by
  rw [mova1_hermiteCoeff_add]
  have e1 : (⇑(mova1_X j f) : Euc d → ℝ) = fun x => x j * f x :=
    funext fun x => mova1_X_apply j f x
  have e2 : (⇑(mova1_D j f) : Euc d → ℝ) =
      fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) :=
    funext fun x => mova1_D_apply j f x
  rw [e1, e2, mo_coeff_xmul, mo_coeff_partial]
  ring

theorem mova1_sq_G (j : Fin d) (f : 𝒮) (β : MultiIndex d) :
    (if 1 ≤ β j then hermiteCoeff (⇑(mova1_X j f + mova1_D j f)) (mova1_dn j β) ^ 2 else 0) =
      2 * (β j : ℝ) * hermiteCoeff (⇑f) β ^ 2 := by
  by_cases h : 1 ≤ β j
  · simp only [h, ↓reduceIte]
    rw [mova1_coeff_G, mova1_up_dn j β h, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity), mova1_dn_apply]
    have : ((β j - 1 : ℕ) : ℝ) + 1 = (β j : ℝ) := by
      have : ((β j - 1 : ℕ) : ℝ) = (β j : ℝ) - 1 := by
        rw [Nat.cast_sub h]; simp
      rw [this]; ring
    rw [this]; ring
  · have h0 : β j = 0 := by omega
    simp [h0]

theorem mova1_eigen_split (β : MultiIndex d) :
    oscEigenvalue d β = ((d : ℝ) + 1) + 2 * ∑ j : Fin d, (β j : ℝ) := by
  unfold oscEigenvalue MultiIndex.degree
  push_cast
  ring

theorem mova1_rec_step (s : ℝ) (f : 𝒮) :
    oscNorm (s + 1) f ≤ Real.sqrt ((d : ℝ) + 1) * oscNorm s f +
      Real.sqrt (2 ^ |s|) * ∑ j : Fin d, oscNorm s (⇑(mova1_X j f + mova1_D j f)) := by
  set c : MultiIndex d → ℝ := hermiteCoeff (⇑f) with hc
  set g : Fin d → 𝒮 := fun j => mova1_X j f + mova1_D j f with hg
  set κ : ℝ := 2 ^ |s| with hκ
  have hκ0 : 0 < κ := by positivity
  have hl0 : ∀ β : MultiIndex d, 0 < oscEigenvalue d β := fun β => oscEigenvalue_pos β
  have hs1 := (memOsc_schwartz (s + 1) f).2
  have hs0 : Summable fun β : MultiIndex d => oscEigenvalue d β ^ s * c β ^ 2 :=
    (memOsc_schwartz s f).2
  have hsg : ∀ j, Summable fun α : MultiIndex d => oscEigenvalue d α ^ s * hermiteCoeff (⇑(g j)) α ^ 2 :=
    fun j => (memOsc_schwartz s (g j)).2
  -- the shifted pieces
  set H : Fin d → MultiIndex d → ℝ := fun j β =>
    oscEigenvalue d β ^ s * (if 1 ≤ β j then hermiteCoeff (⇑(g j)) (mova1_dn j β) ^ 2 else 0) with hH
  have hHsupp : ∀ j, ∀ β ∉ Set.range (mova1_up (d := d) j), H j β = 0 := by
    intro j β hβ
    by_cases h : 1 ≤ β j
    · exact absurd (mova1_up_ne_dn_range j β h) hβ
    · simp [hH, h]
  have hHup : ∀ j α, H j (mova1_up j α) =
      oscEigenvalue d (mova1_up j α) ^ s * hermiteCoeff (⇑(g j)) α ^ 2 := by
    intro j α
    simp [hH, mova1_up_apply, mova1_dn_up]
  have hcmp : ∀ j α, oscEigenvalue d (mova1_up j α) ^ s ≤ κ * oscEigenvalue d α ^ s := by
    intro j α
    have h2 := mova1_eigen_two_le j α
    exact mova1_rpow_cmp s (hl0 _) (hl0 _) (by rw [mova1_eigen_up]; linarith)
      (by rw [mova1_eigen_up]; linarith)
  have hHsum : ∀ j, Summable (H j) := by
    intro j
    refine ((mova1_up_injective (d := d) j).summable_iff (hHsupp j)).1 ?_
    have hle : ∀ α, (H j ∘ mova1_up j) α ≤ κ * (oscEigenvalue d α ^ s * hermiteCoeff (⇑(g j)) α ^ 2) := by
      intro α
      simp only [Function.comp_apply, hHup]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (hcmp j α) (sq_nonneg _)
    refine Summable.of_nonneg_of_le (fun α => ?_) hle ((hsg j).mul_left κ)
    simp only [Function.comp_apply, hHup]
    exact mul_nonneg (Real.rpow_nonneg (hl0 _).le _) (sq_nonneg _)
  have hHtsum : ∀ j, ∑' β, H j β ≤ κ * ∑' α, oscEigenvalue d α ^ s * hermiteCoeff (⇑(g j)) α ^ 2 := by
    intro j
    have h := (mova1_up_injective (d := d) j).tsum_eq (f := H j) (fun β hβ => by
      by_contra h; exact hβ (hHsupp j β h))
    rw [← h, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun α => ?_) ((hHsum j).comp_injective (mova1_up_injective j))
      ((hsg j).mul_left κ)
    simp only [hHup]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcmp j α) (sq_nonneg _)
  -- pointwise identity
  have hpt : ∀ β, oscEigenvalue d β ^ (s + 1) * c β ^ 2 =
      ((d : ℝ) + 1) * (oscEigenvalue d β ^ s * c β ^ 2) + ∑ j, H j β := by
    intro β
    rw [Real.rpow_add_one (hl0 β).ne']
    have hlam := mova1_eigen_split (d := d) β
    have : ∑ j, H j β = oscEigenvalue d β ^ s * (2 * (∑ j : Fin d, (β j : ℝ)) * c β ^ 2) := by
      simp only [hH, ← Finset.mul_sum]
      congr 1
      rw [Finset.sum_congr rfl fun j _ => mova1_sq_G j f β, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [this]
    linear_combination (oscEigenvalue d β ^ s * c β ^ 2) * hlam
  have hsum2 : Summable fun β => ∑ j, H j β := summable_sum fun j _ => hHsum j
  have htot : ∑' β, oscEigenvalue d β ^ (s + 1) * c β ^ 2 =
      ((d : ℝ) + 1) * ∑' β, oscEigenvalue d β ^ s * c β ^ 2 + ∑ j, ∑' β, H j β := by
    rw [tsum_congr hpt, (hs0.mul_left _).tsum_add hsum2, tsum_mul_left,
      Summable.tsum_finsetSum fun j _ => hHsum j]
  -- squares
  have hsq : ∀ (m : ℝ) (u : Euc d → ℝ), 0 ≤ ∑' α : MultiIndex d, oscEigenvalue d α ^ m * hermiteCoeff u α ^ 2 :=
    fun m u => tsum_nonneg fun α => mul_nonneg (Real.rpow_nonneg (hl0 α).le _) (sq_nonneg _)
  have hosq : ∀ (m : ℝ) (u : Euc d → ℝ), oscNorm m u ^ 2 =
      ∑' α : MultiIndex d, oscEigenvalue d α ^ m * hermiteCoeff u α ^ 2 := fun m u =>
    Real.sq_sqrt (hsq m u)
  have hmain : oscNorm (s + 1) f ^ 2 ≤ ((d : ℝ) + 1) * oscNorm s f ^ 2 +
      κ * ∑ j : Fin d, oscNorm s (⇑(g j)) ^ 2 := by
    rw [hosq, hosq, htot]
    have : ∑ j : Fin d, oscNorm s (⇑(g j)) ^ 2 =
        ∑ j : Fin d, ∑' α, oscEigenvalue d α ^ s * hermiteCoeff (⇑(g j)) α ^ 2 :=
      Finset.sum_congr rfl fun j _ => hosq s _
    rw [this, Finset.mul_sum]
    gcongr with j _
    exact hHtsum j
  have hy0 : ∀ j, 0 ≤ oscNorm s (⇑(g j)) := fun j => Real.sqrt_nonneg _
  have hsqsum : ∑ j : Fin d, oscNorm s (⇑(g j)) ^ 2 ≤ (∑ j : Fin d, oscNorm s (⇑(g j))) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => hy0 j
  have hR0 : 0 ≤ Real.sqrt ((d : ℝ) + 1) * oscNorm s f +
      Real.sqrt κ * ∑ j : Fin d, oscNorm s (⇑(g j)) :=
    add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => hy0 j))
  have hRsq : ((d : ℝ) + 1) * oscNorm s f ^ 2 + κ * ∑ j : Fin d, oscNorm s (⇑(g j)) ^ 2 ≤
      (Real.sqrt ((d : ℝ) + 1) * oscNorm s f + Real.sqrt κ * ∑ j : Fin d, oscNorm s (⇑(g j))) ^ 2 := by
    have h1 : Real.sqrt ((d : ℝ) + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have h2 : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ0.le
    have h3 : 0 ≤ Real.sqrt ((d : ℝ) + 1) * oscNorm s f := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h4 : 0 ≤ Real.sqrt κ * ∑ j : Fin d, oscNorm s (⇑(g j)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun j _ => hy0 j)
    have h5 : κ * ∑ j : Fin d, oscNorm s (⇑(g j)) ^ 2 ≤
        (Real.sqrt κ * ∑ j : Fin d, oscNorm s (⇑(g j))) ^ 2 := by
      rw [mul_pow, h2]
      exact mul_le_mul_of_nonneg_left hsqsum hκ0.le
    have h6 : ((d : ℝ) + 1) * oscNorm s f ^ 2 = (Real.sqrt ((d : ℝ) + 1) * oscNorm s f) ^ 2 := by
      rw [mul_pow, h1]
    nlinarith
  have := hmain.trans hRsq
  have h7 := Real.sqrt_le_sqrt this
  rwa [Real.sqrt_sq (show 0 ≤ oscNorm (s + 1) (⇑f) from Real.sqrt_nonneg _), Real.sqrt_sq hR0] at h7

/-! ### The lower integer bound -/

/-- The word norm: `W 0 f = ‖f‖₂`, `W (n+1) f = W n f + ∑_j W n ((x_j + ∂_j) f)`. -/
def mova1_W : ℕ → 𝒮 → ℝ
  | 0, f => mova1_n2 f
  | n + 1, f => mova1_W n f + ∑ j : Fin d, mova1_W n (mova1_X j f + mova1_D j f)

theorem mova1_W_nonneg : ∀ (n : ℕ) (f : 𝒮), 0 ≤ mova1_W n f := by
  intro n
  induction n with
  | zero => intro f; exact mova1_n2_nonneg f
  | succ n ih =>
    intro f
    exact add_nonneg (ih f) (Finset.sum_nonneg fun j _ => ih _)

theorem mova1_lower_W (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝒮, oscNorm n f ≤ C * mova1_W n f := by
  induction n with
  | zero =>
    refine ⟨1, zero_le_one, fun f => ?_⟩
    have h := oscNorm_zero (⇑f) (f.memLp 2)
    have : mova1_W 0 f = mo_l2 f := mova1_n2_eq f
    rw [this]
    simpa [mo_l2] using h.le
  | succ n ih =>
    obtain ⟨C, hC, hCb⟩ := ih
    set M : ℝ := Real.sqrt ((d : ℝ) + 1) + Real.sqrt (2 ^ |(n : ℝ)|) with hM
    have hM0 : 0 ≤ M := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine ⟨M * C, mul_nonneg hM0 hC, fun f => ?_⟩
    have h1 := mova1_rec_step (n : ℝ) f
    have h2 : oscNorm ((n + 1 : ℕ) : ℝ) f = oscNorm ((n : ℝ) + 1) f := by push_cast; rfl
    rw [h2]
    refine h1.trans ?_
    have hW0 := mova1_W_nonneg n f
    have hs : ∑ j : Fin d, oscNorm (n : ℝ) (⇑(mova1_X j f + mova1_D j f)) ≤
        ∑ j : Fin d, C * mova1_W n (mova1_X j f + mova1_D j f) :=
      Finset.sum_le_sum fun j _ => hCb _
    have hs' : ∑ j : Fin d, C * mova1_W n (mova1_X j f + mova1_D j f) =
        C * ∑ j : Fin d, mova1_W n (mova1_X j f + mova1_D j f) := by rw [Finset.mul_sum]
    have hsum0 : 0 ≤ ∑ j : Fin d, mova1_W n (mova1_X j f + mova1_D j f) :=
      Finset.sum_nonneg fun j _ => mova1_W_nonneg n _
    show _ ≤ M * C * (mova1_W n f + ∑ j : Fin d, mova1_W n (mova1_X j f + mova1_D j f))
    have a1 : Real.sqrt ((d : ℝ) + 1) * oscNorm (n : ℝ) f ≤ M * (C * mova1_W n f) := by
      calc Real.sqrt ((d : ℝ) + 1) * oscNorm (n : ℝ) f
          ≤ Real.sqrt ((d : ℝ) + 1) * (C * mova1_W n f) :=
            mul_le_mul_of_nonneg_left (hCb f) (Real.sqrt_nonneg _)
        _ ≤ M * (C * mova1_W n f) :=
            mul_le_mul_of_nonneg_right (by rw [hM]; linarith [Real.sqrt_nonneg (2 ^ |(n : ℝ)|)])
              (mul_nonneg hC hW0)
    have a2 : Real.sqrt (2 ^ |(n : ℝ)|) * ∑ j : Fin d, oscNorm (n : ℝ) (⇑(mova1_X j f + mova1_D j f)) ≤
        M * (C * ∑ j : Fin d, mova1_W n (mova1_X j f + mova1_D j f)) := by
      calc _ ≤ Real.sqrt (2 ^ |(n : ℝ)|) * (C * ∑ j : Fin d, mova1_W n (mova1_X j f + mova1_D j f)) :=
            mul_le_mul_of_nonneg_left (hs.trans hs'.le) (Real.sqrt_nonneg _)
        _ ≤ M * (C * ∑ j : Fin d, mova1_W n (mova1_X j f + mova1_D j f)) :=
            mul_le_mul_of_nonneg_right (by rw [hM]; linarith [Real.sqrt_nonneg ((d : ℝ) + 1)])
              (mul_nonneg hC hsum0)
    nlinarith

theorem mova1_S_mono_add (n m k : ℕ) (f : 𝒮) (h : n + m ≤ k) : mo_S (n + m) f ≤ mo_S k f :=
  mo_S_mono h f

theorem mova1_W_le : ∀ (n m : ℕ) (T : 𝒮 → 𝒮), mova1_IsLow m T →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f, mova1_W n (T f) ≤ K * mo_S (n + m) f := by
  intro n
  induction n with
  | zero =>
    intro m T hT
    obtain ⟨K, hK, hb⟩ := mova1_low_bound hT
    exact ⟨K, hK, fun f => by simpa [mova1_W] using hb f⟩
  | succ n ih =>
    intro m T hT
    obtain ⟨K0, hK0, hb0⟩ := ih m T hT
    have hj : ∀ j : Fin d, ∃ K : ℝ, 0 ≤ K ∧ ∀ f, mova1_W n (mova1_X j (T f) + mova1_D j (T f)) ≤
        K * mo_S (n + (m + 1)) f := fun j => ih (m + 1) _ (mova1_low_G hT j)
    choose Kj hKj0 hKj using hj
    refine ⟨K0 + ∑ j, Kj j, add_nonneg hK0 (Finset.sum_nonneg fun j _ => hKj0 j), fun f => ?_⟩
    have e : n + 1 + m = n + (m + 1) := by omega
    rw [e]
    have hS : mo_S (n + m) f ≤ mo_S (n + (m + 1)) f := mo_S_mono (by omega) f
    have hS0 := mo_S_nonneg (n + (m + 1)) f
    show mova1_W n (T f) + ∑ j : Fin d, mova1_W n (mova1_X j (T f) + mova1_D j (T f)) ≤ _
    calc mova1_W n (T f) + ∑ j : Fin d, mova1_W n (mova1_X j (T f) + mova1_D j (T f))
        ≤ K0 * mo_S (n + (m + 1)) f + ∑ j : Fin d, Kj j * mo_S (n + (m + 1)) f := by
          refine add_le_add ((hb0 f).trans (mul_le_mul_of_nonneg_left hS hK0)) ?_
          exact Finset.sum_le_sum fun j _ => hKj j f
      _ = (K0 + ∑ j, Kj j) * mo_S (n + (m + 1)) f := by rw [add_mul, Finset.sum_mul]

/-- Lower integer bound: `‖f‖_{Σ^n} ≤ C S_n(f)`. -/
theorem mova1_lower (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ f : 𝒮, oscNorm n f ≤ C * mo_S n f := by
  obtain ⟨C, hC, hCb⟩ := mova1_lower_W (d := d) n
  obtain ⟨K, hK, hKb⟩ := mova1_W_le n 0 (fun f : 𝒮 => f) mova1_low_id
  refine ⟨C * K, mul_nonneg hC hK, fun f => ?_⟩
  calc oscNorm n f ≤ C * mova1_W n f := hCb f
    _ ≤ C * (K * mo_S (n + 0) f) := mul_le_mul_of_nonneg_left (hKb f) hC
    _ = C * K * mo_S n f := by rw [Nat.add_zero]; ring

/-- **`mo_int_equiv`.**  For Schwartz `f` and every `n : ℕ`, the `Σ^n` norm is equivalent to the sum of the
`L²` norms `‖x^a ∂^γ f‖₂` over `|a| + |γ| ≤ n` (`mo_idx d n`, `mo_xpow`, `mo_pd`, `mo_l2`), with a constant
depending only on `d` and `n`. -/
theorem mo_int_equiv (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Euc d) ℝ,
    (∑ p ∈ mo_idx d n, mo_l2 (fun x => mo_xpow p.1 x * mo_pd p.2 f x)) ≤ C * oscNorm n f ∧
    oscNorm n f ≤ C * ∑ p ∈ mo_idx d n, mo_l2 (fun x => mo_xpow p.1 x * mo_pd p.2 f x) := by
  obtain ⟨Cu, hCu, hu⟩ := mova1_upper (d := d) n
  obtain ⟨Cl, hCl, hl⟩ := mova1_lower (d := d) n
  refine ⟨Cu + Cl + 1, by positivity, fun f => ⟨?_, ?_⟩⟩
  · have h0 : 0 ≤ oscNorm (n : ℝ) f := Real.sqrt_nonneg _
    calc _ ≤ Cu * oscNorm n f := hu f
      _ ≤ (Cu + Cl + 1) * oscNorm n f := mul_le_mul_of_nonneg_right (by linarith) h0
  · have h0 := mo_S_nonneg n f
    calc oscNorm n f ≤ Cl * mo_S n f := hl f
      _ ≤ (Cu + Cl + 1) * mo_S n f := mul_le_mul_of_nonneg_right (by linarith) h0

end HRS.MS.MovOsc
