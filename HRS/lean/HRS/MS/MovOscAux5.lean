import HRS.MS.MovOscAux4

/-!
# MOV-A2: duality for the oscillator scale `Σ^r` and extensions of the ladder bounds

Namespace `HRS.MS.MovOsc` (helpers `mova2_`, main statements `mo_`).  Infrastructure for S6.1; not manuscript rows.

All statements carry `MemOsc` hypotheses: `oscNorm` is junk (`0`) off `MemOsc`, and `MemOsc` at a
negative index still demands `f ∈ L²`.

* `mo_dual_le` : `MemOsc (-r) f → MemOsc r g → |∫ f g| ≤ ‖f‖_{Σ^{-r}} ‖g‖_{Σ^r}`.
* `mo_dual_sup` : for `f ∈ Σ^{-r}`, `‖f‖_{Σ^{-r}}` is the least upper bound of `|∫ f g|` over finite
  Hermite sums `g = ∑_{α∈S} a_α h_α` with `‖g‖_{Σ^r} ≤ 1` (`mo_hsum`, `mo_dualSet`); conversely
  `mo_memOsc_neg_of_dual_bdd` / `mo_memOsc_neg_iff`: an `L²` function whose pairings with such `g` are
  bounded lies in `Σ^{-r}`.
* `mo_hsum_tail`, `mo_pSum_oscNorm_le` : the Hermite partial sums `mo_pSum f n` (finite Hermite sums over
  `degree ≤ n`) converge to `f ∈ Σ^r` in `Σ^r` and have `‖·‖_{Σ^r} ≤ ‖f‖_{Σ^r}`.
* `mo_xmul_ext`, `mo_xmul_ext_memLp`, `mo_xmul_ext_pos`: the bound `mo_xmul` for non-Schwartz `f ∈ Σ^{r+1}`
  (the hypothesis `x_j f ∈ L²` is automatic for `r ≥ 0`: closure by partial sums and Fatou).
* `mo_partial_ext`: the bound `mo_partial` for differentiable `f ∈ Σ^{r+1}` with `∂_j f ∈ L²`.

Adjustments w.r.t. the sketch in `docs/MOV_PLAN.md` (harmless): the Plancherel `H^{-s}` duality and the
extension of `mo_int_equiv`/`mo_sobolev_emb` to non-Schwartz `f` are not included (the latter needs the Hermite
functions packaged as Schwartz maps or Fourier analysis of `L²` weak derivatives); `∂_j f ∈ L²` is a
hypothesis in `mo_partial_ext`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovOsc

open HRS HRS.Whole

variable {d : ℕ}

/-! ### Parseval polarisation and the duality inequality -/

theorem mova2_parseval_inner {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 (volume : Measure (Euc d))) :
    HasSum (fun α : MultiIndex d => hermiteCoeff f α * hermiteCoeff g α) (∫ x, f x * g x) := by
  obtain ⟨b, hb⟩ := exists_hermiteHilbertBasisD (d := d)
  have h := b.hasSum_inner_mul_inner (hf.toLp f) (hg.toLp g)
  have e1 : ∀ α, inner ℝ (hf.toLp f) (b α) = hermiteCoeff f α := fun α => by
    rw [real_inner_comm, hb α, OscSpace.inner_hermiteLpD_toLp f hf α]
  have e2 : ∀ α, inner ℝ (b α) (hg.toLp g) = hermiteCoeff g α := fun α => by
    rw [hb α, OscSpace.inner_hermiteLpD_toLp g hg α]
  have e3 : inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]; simp [mul_comm]
  simpa only [e1, e2, e3] using h

theorem mova2_cs {ι : Type*} (a b : ι → ℝ) (ha : Summable fun i => a i ^ 2)
    (hb : Summable fun i => b i ^ 2) {s : ℝ} (hs : HasSum (fun i => a i * b i) s) :
    |s| ≤ Real.sqrt (∑' i, a i ^ 2) * Real.sqrt (∑' i, b i ^ 2) := by
  set x : lp (fun _ : ι => ℝ) 2 := ⟨a, memℓp_two_iff.2 ha⟩ with hx
  set y : lp (fun _ : ι => ℝ) 2 := ⟨b, memℓp_two_iff.2 hb⟩ with hy
  have h1 : inner ℝ x y = s := by
    rw [lp.inner_eq_tsum, ← hs.tsum_eq]
    exact tsum_congr fun i => by simp [hx, hy, mul_comm]
  have h2 := abs_real_inner_le_norm x y
  rw [h1, lp_two_norm_eq, lp_two_norm_eq] at h2
  exact h2

/-- **`mo_dual_le`.**  `|⟨f,g⟩| ≤ ‖f‖_{Σ^{-r}} ‖g‖_{Σ^r}` for `f ∈ Σ^{-r}`, `g ∈ Σ^r` (all real `r`). -/
theorem mo_dual_le (r : ℝ) {f g : Euc d → ℝ} (hf : MemOsc (-r) f) (hg : MemOsc r g) :
    |∫ x, f x * g x| ≤ oscNorm (-r) f * oscNorm r g := by
  have hp := mova2_parseval_inner hf.1 hg.1
  have hab : ∀ α : MultiIndex d, (oscEigenvalue d α ^ (-(r / 2)) * hermiteCoeff f α) *
      (oscEigenvalue d α ^ (r / 2) * hermiteCoeff g α) = hermiteCoeff f α * hermiteCoeff g α := by
    intro α
    have := rpow_neg_half_mul r _ (oscEv_pos (d := d) α)
    calc _ = (oscEigenvalue d α ^ (-(r / 2)) * oscEigenvalue d α ^ (r / 2)) *
          (hermiteCoeff f α * hermiteCoeff g α) := by ring
      _ = _ := by rw [this, one_mul]
  have haa : ∀ α : MultiIndex d, (oscEigenvalue d α ^ (-(r / 2)) * hermiteCoeff f α) ^ 2 =
      oscEigenvalue d α ^ (-r) * hermiteCoeff f α ^ 2 := by
    intro α
    rw [mul_pow, ← rpow_half_sq (-r) _ (oscEv_pos α), neg_div]
  have hbb : ∀ α : MultiIndex d, (oscEigenvalue d α ^ (r / 2) * hermiteCoeff g α) ^ 2 =
      oscEigenvalue d α ^ r * hermiteCoeff g α ^ 2 := by
    intro α
    rw [mul_pow, rpow_half_sq r _ (oscEv_pos α)]
  have := mova2_cs (fun α : MultiIndex d => oscEigenvalue d α ^ (-(r / 2)) * hermiteCoeff f α)
    (fun α : MultiIndex d => oscEigenvalue d α ^ (r / 2) * hermiteCoeff g α)
    (hf.2.congr fun α => (haa α).symm) (hg.2.congr fun α => (hbb α).symm)
    (hp.congr_fun fun α => hab α)
  simp only [haa, hbb] at this
  exact this

/-! ### Finite Hermite sums -/

/-- The finite Hermite sum `∑_{α∈S} a_α h_α`. -/
def mo_hsum (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) : Euc d → ℝ :=
  fun x => ∑ α ∈ S, a α * hermiteFunD α x

theorem mova2_hsum_memLp (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    MemLp (mo_hsum S a) 2 (volume : Measure (Euc d)) := by
  unfold mo_hsum
  exact memLp_finsetSum _ fun α _ => (memLp_hermiteFunD α).const_mul (a α)

theorem mova2_coeff_hsum (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) (β : MultiIndex d) :
    hermiteCoeff (mo_hsum S a) β = if β ∈ S then a β else 0 := by
  unfold hermiteCoeff mo_hsum
  have e : ∀ x : Euc d, (∑ α ∈ S, a α * hermiteFunD α x) * hermiteFunD β x =
      ∑ α ∈ S, a α * (hermiteFunD α x * hermiteFunD β x) := fun x => by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun α _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun α _ => (integrable_hermiteFunD_mul α β).const_mul (a α)]
  simp_rw [integral_const_mul, hermiteFunD_orthonormal]
  simp [Finset.sum_ite_eq']

theorem mova2_coeff_sq_summable (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) (r : ℝ) :
    Summable fun α : MultiIndex d => oscEigenvalue d α ^ r * hermiteCoeff (mo_hsum S a) α ^ 2 := by
  refine summable_of_ne_finset_zero (s := S) fun α hα => ?_
  rw [mova2_coeff_hsum, if_neg hα]; simp

theorem mo_hsum_memOsc (r : ℝ) (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    MemOsc r (mo_hsum S a) := ⟨mova2_hsum_memLp S a, mova2_coeff_sq_summable S a r⟩

theorem mo_hsum_oscNorm_sq (r : ℝ) (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    oscNorm r (mo_hsum S a) ^ 2 = ∑ α ∈ S, oscEigenvalue d α ^ r * a α ^ 2 := by
  unfold oscNorm
  rw [Real.sq_sqrt (tsum_nonneg fun α => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _))]
  rw [tsum_eq_sum (s := S)]
  · exact Finset.sum_congr rfl fun α hα => by rw [mova2_coeff_hsum, if_pos hα]
  · intro α hα; rw [mova2_coeff_hsum, if_neg hα]; simp

theorem mova2_pair_hsum {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) :
    ∫ x, f x * mo_hsum S a x = ∑ α ∈ S, a α * hermiteCoeff f α := by
  unfold mo_hsum hermiteCoeff
  have e : ∀ x : Euc d, f x * (∑ α ∈ S, a α * hermiteFunD α x) =
      ∑ α ∈ S, a α * (f x * hermiteFunD α x) := fun x => by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun α _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun α _ => ((memLp_hermiteFunD α).integrable_mul hf |>.congr
    (Filter.Eventually.of_forall fun x => by simp [mul_comm])).const_mul (a α)]
  simp_rw [integral_const_mul]

/-! ### The supremum characterisation -/

/-- The set `{|⟨f,g⟩| : g finite Hermite sum, ‖g‖_{Σ^r} ≤ 1}`. -/
def mo_dualSet (r : ℝ) (f : Euc d → ℝ) : Set ℝ :=
  {t | ∃ (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ),
    oscNorm r (mo_hsum S a) ≤ 1 ∧ t = |∫ x, f x * mo_hsum S a x|}

theorem mova2_zero_mem (r : ℝ) (f : Euc d → ℝ) : (0 : ℝ) ∈ mo_dualSet r f := by
  refine ⟨∅, fun _ => 0, ?_, ?_⟩
  · have := mo_hsum_oscNorm_sq r (∅ : Finset (MultiIndex d)) (fun _ => 0)
    simp at this
    rw [this]; norm_num
  · simp [mo_hsum]

/-- **`mo_dual_sup` (upper bound).**  Every element of the dual set is at most `‖f‖_{Σ^{-r}}`. -/
theorem mo_dualSet_le (r : ℝ) {f : Euc d → ℝ} (hf : MemOsc (-r) f) {t : ℝ}
    (ht : t ∈ mo_dualSet r f) : t ≤ oscNorm (-r) f := by
  obtain ⟨S, a, h1, rfl⟩ := ht
  have := mo_dual_le r hf (mo_hsum_memOsc r S a)
  have h0 : 0 ≤ oscNorm (-r) f := Real.sqrt_nonneg _
  calc _ ≤ _ := this
    _ ≤ oscNorm (-r) f * 1 := mul_le_mul_of_nonneg_left h1 h0
    _ = _ := mul_one _

/-- **`mo_memOsc_neg_of_dual_bdd`.**  An `L²` function whose pairings with finite Hermite sums of
`Σ^r`-norm `≤ 1` are bounded by `M` lies in `Σ^{-r}`, with `‖f‖_{Σ^{-r}} ≤ M`. -/
theorem mo_memOsc_neg_of_dual_bdd (r : ℝ) {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    {M : ℝ} (hM : ∀ t ∈ mo_dualSet r f, t ≤ M) : MemOsc (-r) f ∧ oscNorm (-r) f ≤ M := by
  have hM0 : 0 ≤ M := hM 0 (mova2_zero_mem r f)
  set u : MultiIndex d → ℝ := fun α => oscEigenvalue d α ^ (-r) * hermiteCoeff f α ^ 2 with hu
  have hu0 : ∀ α, 0 ≤ u α := fun α =>
    mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  have key : ∀ S : Finset (MultiIndex d), ∑ α ∈ S, u α ≤ M ^ 2 := by
    intro S
    set T := ∑ α ∈ S, u α with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun α _ => hu0 α
    rcases hT0.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · set a : MultiIndex d → ℝ := fun α => (Real.sqrt T)⁻¹ * (oscEigenvalue d α ^ (-r) * hermiteCoeff f α)
      have hsq : oscNorm r (mo_hsum S a) = 1 := by
        have h2 := mo_hsum_oscNorm_sq r S a
        have h3 : ∑ α ∈ S, oscEigenvalue d α ^ r * a α ^ 2 = 1 := by
          have : ∀ α ∈ S, oscEigenvalue d α ^ r * a α ^ 2 = T⁻¹ * u α := by
            intro α _
            have hl := oscEv_pos (d := d) α
            have hs : (Real.sqrt T)⁻¹ ^ 2 = T⁻¹ := by
              rw [inv_pow, Real.sq_sqrt hpos.le]
            have hr : oscEigenvalue d α ^ r * (oscEigenvalue d α ^ (-r)) ^ 2 =
                oscEigenvalue d α ^ (-r) := by
              rw [sq, ← mul_assoc, ← Real.rpow_add hl]; simp
            simp only [a, hu, mul_pow, hs]
            calc _ = T⁻¹ * (oscEigenvalue d α ^ r * (oscEigenvalue d α ^ (-r)) ^ 2 *
                  hermiteCoeff f α ^ 2) := by ring
              _ = _ := by rw [hr]
          rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
          exact inv_mul_cancel₀ hpos.ne'
        have h4 : oscNorm r (mo_hsum S a) ^ 2 = 1 := by rw [h2, h3]
        have h5 : 0 ≤ oscNorm r (mo_hsum S a) := Real.sqrt_nonneg _
        nlinarith
      have hpair : ∫ x, f x * mo_hsum S a x = Real.sqrt T := by
        rw [mova2_pair_hsum hf]
        have : ∀ α ∈ S, a α * hermiteCoeff f α = (Real.sqrt T)⁻¹ * u α := by
          intro α _; simp only [a, hu]; ring
        rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← hT]
        have : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hpos.le
        have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.2 hpos).ne'
        field_simp
        rw [sq]; exact this.symm
      have hle : Real.sqrt T ≤ M := by
        have := hM _ ⟨S, a, hsq.le, rfl⟩
        rwa [hpair, abs_of_nonneg (Real.sqrt_nonneg _)] at this
      calc T = (Real.sqrt T) ^ 2 := (Real.sq_sqrt hpos.le).symm
        _ ≤ M ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hle 2
  have hs : Summable u := summable_of_sum_le hu0 key
  refine ⟨⟨hf, hs⟩, ?_⟩
  unfold oscNorm
  exact Real.sqrt_le_iff.2 ⟨hM0, Real.tsum_le_of_sum_le hu0 key⟩

/-- **`mo_dual_sup`.**  For `f ∈ Σ^{-r}`, `‖f‖_{Σ^{-r}}` is the supremum of `|⟨f,g⟩|` over finite Hermite
sums `g` with `‖g‖_{Σ^r} ≤ 1`. -/
theorem mo_dual_sup (r : ℝ) {f : Euc d → ℝ} (hf : MemOsc (-r) f) :
    IsLUB (mo_dualSet r f) (oscNorm (-r) f) :=
  ⟨fun _ ht => mo_dualSet_le r hf ht,
    fun _ hM => (mo_memOsc_neg_of_dual_bdd r hf.1 (fun _ ht => hM ht)).2⟩

theorem mo_dual_sup_eq (r : ℝ) {f : Euc d → ℝ} (hf : MemOsc (-r) f) :
    oscNorm (-r) f = sSup (mo_dualSet r f) :=
  ((mo_dual_sup r hf).csSup_eq ⟨0, mova2_zero_mem r f⟩).symm

/-- **`mo_memOsc_neg_iff`.**  For `f ∈ L²`: `f ∈ Σ^{-r}` iff the pairings with finite Hermite sums of
`Σ^r`-norm `≤ 1` are bounded. -/
theorem mo_memOsc_neg_iff (r : ℝ) {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) :
    MemOsc (-r) f ↔ BddAbove (mo_dualSet r f) :=
  ⟨fun h => ⟨_, fun _ ht => mo_dualSet_le r h ht⟩, fun ⟨M, hM⟩ =>
    (mo_memOsc_neg_of_dual_bdd r hf fun _ ht => hM ht).1⟩

/-! ### Density of the Hermite partial sums -/

/-- The finite set of multi-indices of degree `≤ n`. -/
def mova2_S (d n : ℕ) : Finset (MultiIndex d) := (multiIndex_sublevel_finite d n).toFinset

theorem mova2_mem_S {n : ℕ} {α : MultiIndex d} : α ∈ mova2_S d n ↔ α.degree ≤ n := by
  simp [mova2_S]

theorem mova2_S_mono : Monotone (mova2_S d) := fun m n h α hα => by
  rw [mova2_mem_S] at hα ⊢; omega

theorem mova2_S_exh (α : MultiIndex d) : ∃ n, α ∈ mova2_S d n := ⟨α.degree, mova2_mem_S.2 le_rfl⟩

/-- The Hermite partial sum `∑_{|α| ≤ n} ⟨f,h_α⟩ h_α`. -/
def mo_pSum (f : Euc d → ℝ) (n : ℕ) : Euc d → ℝ := mo_hsum (mova2_S d n) (hermiteCoeff f)

theorem mova2_tendsto_tail {u : MultiIndex d → ℝ} (hu : Summable u) :
    Tendsto (fun n : ℕ => ∑' α : MultiIndex d, if α.degree ≤ n then 0 else u α) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => ∑ α ∈ mova2_S d n, u α) atTop (𝓝 (∑' α, u α)) :=
    hu.hasSum.comp (tendsto_atTop_finset_of_monotone mova2_S_mono mova2_S_exh)
  have h2 : ∀ n, ∑' α : MultiIndex d, (if α.degree ≤ n then 0 else u α) =
      ∑' α, u α - ∑ α ∈ mova2_S d n, u α := by
    intro n
    have hin : Summable fun α : MultiIndex d => if α.degree ≤ n then u α else 0 :=
      summable_of_ne_finset_zero (s := mova2_S d n) fun α hα => by
        rw [mova2_mem_S] at hα; simp [hα]
    have e1 : ∑' α : MultiIndex d, (if α.degree ≤ n then u α else 0) = ∑ α ∈ mova2_S d n, u α := by
      rw [tsum_eq_sum (s := mova2_S d n) (fun α hα => by rw [mova2_mem_S] at hα; simp [hα])]
      exact Finset.sum_congr rfl fun α hα => by rw [mova2_mem_S] at hα; simp [hα]
    have e2 : ∀ α : MultiIndex d, (if α.degree ≤ n then 0 else u α) =
        u α - (if α.degree ≤ n then u α else 0) := fun α => by split_ifs <;> simp
    simp_rw [e2]
    rw [(hu.hasSum.sub hin.hasSum).tsum_eq, e1]
  simp_rw [h2]
  have := (tendsto_const_nhds (x := ∑' α, u α)).sub h1
  simpa using this

theorem mova2_int_mul {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) (α : MultiIndex d) :
    Integrable (fun x => f x * hermiteFunD α x) (volume : Measure (Euc d)) :=
  hf.integrable_mul (memLp_hermiteFunD α)

theorem mova2_coeff_sub {f g : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hg : MemLp g 2 (volume : Measure (Euc d))) (α : MultiIndex d) :
    hermiteCoeff (fun x => f x - g x) α = hermiteCoeff f α - hermiteCoeff g α := by
  unfold hermiteCoeff
  simp_rw [sub_mul]
  exact integral_sub (mova2_int_mul hf α) (mova2_int_mul hg α)

theorem mova2_coeff_pSum (f : Euc d → ℝ) (n : ℕ) (α : MultiIndex d) :
    hermiteCoeff (mo_pSum f n) α = if α.degree ≤ n then hermiteCoeff f α else 0 := by
  unfold mo_pSum; rw [mova2_coeff_hsum]; simp only [mova2_mem_S]

theorem mova2_sub_pSum (r : ℝ) {f : Euc d → ℝ} (hf : MemOsc r f) (n : ℕ) :
    MemOsc r (fun x => f x - mo_pSum f n x) ∧
      oscNorm r (fun x => f x - mo_pSum f n x) ^ 2 = ∑' α : MultiIndex d,
        if α.degree ≤ n then 0 else oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 := by
  have hL : MemLp (fun x => f x - mo_pSum f n x) 2 (volume : Measure (Euc d)) :=
    hf.1.sub (mova2_hsum_memLp _ _)
  have hc : ∀ α, hermiteCoeff (fun x => f x - mo_pSum f n x) α =
      if α.degree ≤ n then 0 else hermiteCoeff f α := by
    intro α
    have hp : MemLp (mo_pSum f n) 2 (volume : Measure (Euc d)) := mova2_hsum_memLp _ _
    rw [mova2_coeff_sub hf.1 hp]
    have := mova2_coeff_pSum f n α
    rw [this]; split_ifs <;> simp
  have hw : ∀ α, oscEigenvalue d α ^ r * hermiteCoeff (fun x => f x - mo_pSum f n x) α ^ 2 =
      if α.degree ≤ n then 0 else oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 := by
    intro α; rw [hc α]; split_ifs <;> simp
  have hnn : ∀ α : MultiIndex d, 0 ≤ if α.degree ≤ n then 0 else
      oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 := fun α => by
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  refine ⟨⟨hL, ?_⟩, ?_⟩
  · simp_rw [hw]
    refine Summable.of_nonneg_of_le hnn (fun α => ?_) hf.2
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
    · exact le_rfl
  · unfold oscNorm
    rw [Real.sq_sqrt (tsum_nonneg fun α => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _))]
    exact tsum_congr hw

/-- **`mo_hsum_tail`.**  The Hermite partial sums of `f ∈ Σ^r` converge to `f` in `Σ^r`. -/
theorem mo_hsum_tail (r : ℝ) {f : Euc d → ℝ} (hf : MemOsc r f) :
    Tendsto (fun n : ℕ => oscNorm r (fun x => f x - mo_pSum f n x)) atTop (𝓝 0) := by
  have e : ∀ n : ℕ, oscNorm r (fun x => f x - mo_pSum f n x) = Real.sqrt (∑' α : MultiIndex d,
      if α.degree ≤ n then 0 else oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2) := fun n => by
    have hn : 0 ≤ oscNorm r (fun x => f x - mo_pSum f n x) := Real.sqrt_nonneg _
    rw [← (mova2_sub_pSum r hf n).2, Real.sqrt_sq hn]
  simp_rw [e]
  simpa using (mova2_tendsto_tail hf.2).sqrt

theorem mo_pSum_oscNorm_le (r : ℝ) {f : Euc d → ℝ} (hf : MemOsc r f) (n : ℕ) :
    MemOsc r (mo_pSum f n) ∧ oscNorm r (mo_pSum f n) ≤ oscNorm r f := by
  refine ⟨mo_hsum_memOsc r _ _, ?_⟩
  have h2 := mo_hsum_oscNorm_sq r (mova2_S d n) (hermiteCoeff f)
  have h3 : oscNorm r f ^ 2 = ∑' α : MultiIndex d, oscEigenvalue d α ^ r * hermiteCoeff f α ^ 2 :=
    Real.sq_sqrt (tsum_nonneg fun α => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _))
  have h4 : oscNorm r (mo_pSum f n) ^ 2 ≤ oscNorm r f ^ 2 := by
    rw [h3]
    unfold mo_pSum
    rw [h2]
    exact hf.2.sum_le_tsum _ fun α _ => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) two_ne_zero).1 h4

/-! ### Extension of `mo_xmul`, `mo_partial` beyond Schwartz functions -/

theorem mova2_ladder_ext (j : Fin d) (r : ℝ) {f g : Euc d → ℝ} (hf : MemOsc (r + 1) f)
    (hg : MemLp g 2 (volume : Measure (Euc d))) (σ : ℝ) (hσ : σ ^ 2 = 1)
    (hc : ∀ α, hermiteCoeff g α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff f (mova1_up j α) +
        σ * Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff f (mova1_dn j α)) :
    MemOsc r g ∧ oscNorm r g ≤ Real.sqrt (2 ^ |r + 1|) * oscNorm (r + 1) f := by
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
    (fun α => hc α) hf.2
  refine ⟨⟨hg, hsum⟩, ?_⟩
  unfold oscNorm
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.sqrt_le_sqrt hle

theorem mova2_coeff_xmul {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d))) (j : Fin d)
    (α : MultiIndex d) :
    hermiteCoeff (fun x => x j * f x) α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff f (mova1_up j α) +
        Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff f (mova1_dn j α) := by
  unfold hermiteCoeff
  have e : ∀ x : Euc d, (x j * f x) * hermiteFunD α x =
      Real.sqrt (((α j : ℝ) + 1) / 2) * (f x * hermiteFunD (mova1_up j α) x) +
        Real.sqrt ((α j : ℝ) / 2) * (f x * hermiteFunD (mova1_dn j α) x) := by
    intro x
    have := mova1_x_hD α j x
    linear_combination f x * this
  simp_rw [e]
  rw [integral_add ((mova2_int_mul hf _).const_mul _) ((mova2_int_mul hf _).const_mul _),
    integral_const_mul, integral_const_mul]

/-- **`mo_xmul_ext`.**  `mo_xmul` for non-Schwartz `f ∈ Σ^{r+1}` with `x_j f ∈ L²` (for `r ≥ 0` the
last hypothesis is automatic, `mo_xmul_ext_memLp`; for `r < 0` it is needed since `MemOsc` demands `L²`). -/
theorem mo_xmul_ext (r : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin d) (f : Euc d → ℝ), MemOsc (r + 1) f →
    MemLp (fun x => x j * f x) 2 (volume : Measure (Euc d)) →
    MemOsc r (fun x => x j * f x) ∧ oscNorm r (fun x => x j * f x) ≤ C * oscNorm (r + 1) f :=
  ⟨Real.sqrt (2 ^ |r + 1|), Real.sqrt_nonneg _, fun j f hf hg =>
    mova2_ladder_ext j r hf hg 1 (by norm_num) fun α => by rw [mova2_coeff_xmul hf.1]; ring⟩

theorem mova2_xmul_hsum_memLp (S : Finset (MultiIndex d)) (a : MultiIndex d → ℝ) (j : Fin d) :
    MemLp (fun x : Euc d => x j * mo_hsum S a x) 2 (volume : Measure (Euc d)) := by
  have e : (fun x : Euc d => x j * mo_hsum S a x) = fun x => ∑ α ∈ S,
      (a α * Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteFunD (mova1_up j α) x +
        a α * Real.sqrt ((α j : ℝ) / 2) * hermiteFunD (mova1_dn j α) x) := by
    funext x
    unfold mo_hsum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    have := mova1_x_hD α j x
    linear_combination a α * this
  rw [e]
  exact memLp_finsetSum _ fun α _ =>
    ((memLp_hermiteFunD _).const_mul _).add ((memLp_hermiteFunD _).const_mul _)

theorem mova2_eLpNorm_two {h : Euc d → ℝ} (hh : MemLp h 2 (volume : Measure (Euc d))) :
    eLpNorm h 2 (volume : Measure (Euc d)) = ENNReal.ofReal (oscNorm 0 h) := by
  rw [oscNorm_zero h hh, hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 1
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [Real.sqrt_eq_rpow]; norm_num

/-- **`mo_xmul_ext_memLp`.**  If `f ∈ Σ^1` then `x_j f ∈ L²` (closure: Hermite partial sums, Fatou). -/
theorem mo_xmul_ext_memLp {f : Euc d → ℝ} (hf : MemOsc 1 f) (j : Fin d) :
    MemLp (fun x => x j * f x) 2 (volume : Measure (Euc d)) := by
  obtain ⟨C, hC0, hC⟩ := mo_xmul_ext (d := d) 0
  have hf0 : MemOsc 0 f := (mo_mono (by norm_num) hf).1
  -- uniform bound for the partial sums
  have hbd : ∀ n : ℕ, eLpNorm (fun x => x j * mo_pSum f n x) 2 (volume : Measure (Euc d)) ≤
      ENNReal.ofReal (C * oscNorm 1 f) := by
    intro n
    have hg := mo_pSum_oscNorm_le 1 hf n
    have hL : MemLp (fun x => x j * mo_pSum f n x) 2 (volume : Measure (Euc d)) :=
      mova2_xmul_hsum_memLp (mova2_S d n) (hermiteCoeff f) j
    have h1 := hC j (mo_pSum f n) (by simpa using hg.1) hL
    rw [mova2_eLpNorm_two hL]
    refine ENNReal.ofReal_le_ofReal (h1.2.trans ?_)
    simpa using mul_le_mul_of_nonneg_left hg.2 hC0
  -- convergence in measure of the partial sums, then an a.e. convergent subsequence
  have hconv : Tendsto (fun n : ℕ => eLpNorm (mo_pSum f n - f) 2 (volume : Measure (Euc d))) atTop
      (𝓝 0) := by
    have e : ∀ n : ℕ, eLpNorm (mo_pSum f n - f) 2 (volume : Measure (Euc d)) =
        ENNReal.ofReal (oscNorm 0 (fun x => f x - mo_pSum f n x)) := fun n => by
      rw [eLpNorm_sub_comm]
      exact mova2_eLpNorm_two (hf0.1.sub (mova2_hsum_memLp _ _))
    simp_rw [e]
    simpa using ENNReal.tendsto_ofReal (mo_hsum_tail 0 hf0)
  have hmeas : TendstoInMeasure (volume : Measure (Euc d)) (fun n => mo_pSum f n) atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hconv
  obtain ⟨ns, hns, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hcont : Continuous fun x : Euc d => x j := (EuclideanSpace.proj (𝕜 := ℝ) j).continuous
  have hmeasF : AEStronglyMeasurable (fun x => x j * f x) (volume : Measure (Euc d)) :=
    hcont.aestronglyMeasurable.mul hf.1.aestronglyMeasurable
  have hlim : ∀ᵐ x ∂(volume : Measure (Euc d)),
      Tendsto (fun k => x j * mo_pSum f (ns k) x) atTop (𝓝 (x j * f x)) := by
    filter_upwards [hae] with x hx using hx.const_mul (x j)
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (f := fun k x => x j * mo_pSum f (ns k) x)
    (fun k => (hcont.aestronglyMeasurable.mul (mova2_hsum_memLp _ _).aestronglyMeasurable))
    (fun x => x j * f x) hmeasF hlim
  have hlt : eLpNorm (fun x => x j * f x) 2 (volume : Measure (Euc d)) ≤
      ENNReal.ofReal (C * oscNorm 1 f) := by
    refine hfatou.trans ?_
    calc _ ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal (C * oscNorm 1 f)) atTop :=
          Filter.liminf_le_liminf (Filter.Eventually.of_forall fun k => hbd (ns k))
      _ = _ := Filter.liminf_const _
  exact lt_of_le_of_lt hlt ENNReal.ofReal_lt_top

theorem mo_xmul_ext_pos {r : ℝ} (hr : 0 ≤ r) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin d) (f : Euc d → ℝ),
    MemOsc (r + 1) f →
    MemOsc r (fun x => x j * f x) ∧ oscNorm r (fun x => x j * f x) ≤ C * oscNorm (r + 1) f := by
  obtain ⟨C, hC0, hC⟩ := mo_xmul_ext (d := d) r
  exact ⟨C, hC0, fun j f hf => hC j f hf (mo_xmul_ext_memLp
    ((mo_mono (by linarith) hf).1) j)⟩

theorem mova2_coeff_partial {f : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hdiff : Differentiable ℝ f) (j : Fin d)
    (hg : MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) 2
      (volume : Measure (Euc d))) (α : MultiIndex d) :
    hermiteCoeff (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) α =
      Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff f (mova1_up j α) -
        Real.sqrt ((α j : ℝ) / 2) * hermiteCoeff f (mova1_dn j α) := by
  obtain ⟨hA, -⟩ := hermiteFunD_line_data α j
  have hl : ∀ x : Euc d, fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ)) =
      lineDeriv ℝ f x (EuclideanSpace.single j (1 : ℝ)) :=
    fun x => ((hdiff x).lineDeriv_eq_fderiv).symm
  have hf' : ∀ x : Euc d, HasLineDerivAt ℝ f
      (lineDeriv ℝ f x (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single j (1 : ℝ)) :=
    fun x => ((hdiff x).lineDifferentiableAt).hasLineDerivAt
  have hg' : ∀ x : Euc d, (∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) *
      deriv (hermiteFun (α j)) (x j) =
      Real.sqrt ((α j : ℝ) / 2) * hermiteFunD (mova1_dn j α) x -
        Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteFunD (mova1_up j α) x := fun x => mova1_dQ_hD α j x
  have I1 : Integrable (fun x : Euc d => lineDeriv ℝ f x (EuclideanSpace.single j (1 : ℝ)) *
      hermiteFunD α x) (volume : Measure (Euc d)) := by
    simp_rw [← hl]; exact mova2_int_mul hg α
  have I2' : Integrable (fun x : Euc d => Real.sqrt ((α j : ℝ) / 2) * (f x * hermiteFunD (mova1_dn j α) x) -
      Real.sqrt (((α j : ℝ) + 1) / 2) * (f x * hermiteFunD (mova1_up j α) x))
      (volume : Measure (Euc d)) :=
    ((mova2_int_mul hf _).const_mul _).sub ((mova2_int_mul hf _).const_mul _)
  have I2 : Integrable (fun x : Euc d => f x * ((∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) *
      deriv (hermiteFun (α j)) (x j))) (volume : Measure (Euc d)) := by
    refine I2'.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hg']; ring
  have key := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℝ) (f := f)
    (f' := fun x => lineDeriv ℝ f x (EuclideanSpace.single j (1 : ℝ))) (g := hermiteFunD α)
    (g' := fun x => (∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) *
      deriv (hermiteFun (α j)) (x j)) (v := (EuclideanSpace.single j (1 : ℝ) : Euc d))
    (μ := volume) (by simpa using I1) (by simpa using I2) (by simpa using mova2_int_mul hf α)
    (fun x _ => hf' x) (fun x _ => hA x)
  simp only [ContinuousLinearMap.mul_apply'] at key
  unfold hermiteCoeff
  simp_rw [hl]
  rw [show ∫ x : Euc d, lineDeriv ℝ f x (EuclideanSpace.single j (1 : ℝ)) * hermiteFunD α x =
      -∫ x : Euc d, f x * ((∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) *
        deriv (hermiteFun (α j)) (x j)) from by linarith]
  have e : ∀ x : Euc d, f x * ((∏ i ∈ Finset.univ.erase j, hermiteFun (α i) (x i)) *
      deriv (hermiteFun (α j)) (x j)) =
      Real.sqrt ((α j : ℝ) / 2) * (f x * hermiteFunD (mova1_dn j α) x) -
        Real.sqrt (((α j : ℝ) + 1) / 2) * (f x * hermiteFunD (mova1_up j α) x) := by
    intro x; rw [hg' x]; ring
  simp_rw [e]
  rw [integral_sub ((mova2_int_mul hf _).const_mul _) ((mova2_int_mul hf _).const_mul _),
    integral_const_mul, integral_const_mul]
  ring

/-- **`mo_partial_ext`.**  `mo_partial` for a differentiable `f ∈ Σ^{r+1}` whose partial derivative `∂_j f`
is in `L²` (unlike `x_j f`, this is not deduced automatically from `f ∈ Σ^1`: it is a hypothesis). -/
theorem mo_partial_ext (r : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Fin d) (f : Euc d → ℝ), MemOsc (r + 1) f →
    Differentiable ℝ f →
    MemLp (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) 2 (volume : Measure (Euc d)) →
    MemOsc r (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) ∧
      oscNorm r (fun x => fderiv ℝ f x (EuclideanSpace.single j (1 : ℝ))) ≤ C * oscNorm (r + 1) f :=
  ⟨Real.sqrt (2 ^ |r + 1|), Real.sqrt_nonneg _, fun j f hf hd hg =>
    mova2_ladder_ext j r hf hg (-1) (by norm_num) fun α => by
      rw [mova2_coeff_partial hf.1 hd j hg]; ring⟩

end HRS.MS.MovOsc
