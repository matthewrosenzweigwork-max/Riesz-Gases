import HRS.MS.SA16PRiesz3

/-!
# SA16P, part 4: the density `g = G / h` lies in `L^q` with `‖g‖_q ≤ ‖ℓ‖`

Test `ℓ` against the truncations `s_N h`, `s_N = 1_{T_N} g|g|^{q-2}/h`, `T_N = {|g| ≤ N, h ≥ 1/(N+1)}`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Function
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16P

lemma sa16p_phi {q : ℝ} (hq : 1 < q) (t : ℝ) :
    |t * |t| ^ (q - 2)| = |t| ^ (q - 1) ∧ t * (t * |t| ^ (q - 2)) = |t| ^ q := by
  by_cases ht : t = 0
  · subst ht
    simp [Real.zero_rpow (by linarith : q - 1 ≠ 0), Real.zero_rpow (by linarith : q ≠ 0)]
  · have hpos : 0 < |t| := abs_pos.2 ht
    constructor
    · rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _),
        ← Real.rpow_one_add' (abs_nonneg t) (by linarith)]
      congr 1; ring
    · have h2 : t * t = |t| ^ (2 : ℝ) := by
        rw [Real.rpow_two, sq_abs]; ring
      rw [← mul_assoc, h2, ← Real.rpow_add hpos]
      congr 1; ring

/-- the key bound `I ≤ ‖ℓ‖ I^{1/p}  ⇒  I ≤ ‖ℓ‖^q` -/
lemma sa16p_norm_arith {p q : ℝ} (hpq : p.HolderConjugate q) {I L : ℝ} (hI : 0 ≤ I) (hL : 0 ≤ L)
    (h : I ≤ L * I ^ (1 / p)) : I ≤ L ^ q := by
  rcases (lt_or_eq_of_le hI).symm with h0 | hpos
  · rw [← h0]; exact Real.rpow_nonneg hL _
  · have hp : 1 < p := hpq.lt
    have hq : 1 < q := hpq.symm.lt
    have hinv : 1 / p + 1 / q = 1 := by simpa using hpq.inv_add_inv_eq_one
    have h1 : I ^ (1 - 1 / p) ≤ L := by
      have : I ^ (1 - 1 / p) = I / I ^ (1 / p) := by
        rw [Real.rpow_sub hpos, Real.rpow_one]
      rw [this, div_le_iff₀ (Real.rpow_pos_of_pos hpos _)]
      linarith
    have h2 : 1 - 1 / p = 1 / q := by linarith
    rw [h2] at h1
    have h3 : (I ^ (1 / q)) ^ q ≤ L ^ q := Real.rpow_le_rpow (Real.rpow_nonneg hI _) h1 (by linarith)
    rwa [← Real.rpow_mul hI, one_div, inv_mul_cancel₀ (by linarith), Real.rpow_one] at h3

section Norm
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)] {h : α → ℝ} (hh : MemLp h (ENNReal.ofReal p) μ)
  (ℓ : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] ℝ)

/-- the density `g = G / h` -/
def sa16p_g (hp : 1 < p) (x : α) : ℝ := sa16p_G hh ℓ hp x / h x

/-- the truncation sets `T_N = {|g| ≤ N, h ≥ 1/(N+1)}` -/
def sa16p_T (hp : 1 < p) (N : ℕ) : Set α :=
  {x | |sa16p_g hh ℓ hp x| ≤ N ∧ 1 / ((N : ℝ) + 1) ≤ h x}

/-- the test function `s_N` -/
def sa16p_s (q : ℝ) (hp : 1 < p) (N : ℕ) (x : α) : ℝ :=
  (sa16p_T hh ℓ hp N).indicator
    (fun x => (sa16p_g hh ℓ hp x * |sa16p_g hh ℓ hp x| ^ (q - 2)) / h x) x

lemma sa16p_g_measurable (hhm : Measurable h) (hp : 1 < p) : Measurable (sa16p_g hh ℓ hp) :=
  (sa16p_G_measurable hh ℓ hp).div hhm

lemma sa16p_T_measurable (hhm : Measurable h) (hp : 1 < p) (N : ℕ) :
    MeasurableSet (sa16p_T hh ℓ hp N) := by
  unfold sa16p_T
  exact (measurableSet_le (sa16p_g_measurable hh ℓ hhm hp).abs measurable_const).inter
    (measurableSet_le measurable_const hhm)

lemma sa16p_G_eq (hpos : ∀ x, 0 < h x) (hp : 1 < p) (x : α) :
    sa16p_G hh ℓ hp x = sa16p_g hh ℓ hp x * h x := by
  simp [sa16p_g, (hpos x).ne']

lemma sa16p_s_bound {q : ℝ} (hq : 1 < q) (hpos : ∀ x, 0 < h x) (hp : 1 < p) (N : ℕ) (x : α) :
    |sa16p_s hh ℓ q hp N x| ≤ (N : ℝ) ^ (q - 1) * ((N : ℝ) + 1) := by
  unfold sa16p_s
  by_cases hx : x ∈ sa16p_T hh ℓ hp N
  · rw [Set.indicator_of_mem hx]
    obtain ⟨h1, h2⟩ := hx
    rw [abs_div, (sa16p_phi hq _).1, abs_of_pos (hpos x)]
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have e1 : |sa16p_g hh ℓ hp x| ^ (q - 1) ≤ (N : ℝ) ^ (q - 1) :=
      Real.rpow_le_rpow (abs_nonneg _) h1 (by linarith)
    have e2 : 1 / h x ≤ (N : ℝ) + 1 := by
      rw [div_le_iff₀ (hpos x)]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).1 h2
      linarith [this, mul_comm (h x) ((N : ℝ) + 1)]
    calc |sa16p_g hh ℓ hp x| ^ (q - 1) / h x = |sa16p_g hh ℓ hp x| ^ (q - 1) * (1 / h x) := by ring
      _ ≤ (N : ℝ) ^ (q - 1) * ((N : ℝ) + 1) :=
        mul_le_mul e1 e2 (one_div_nonneg.2 (hpos x).le) (Real.rpow_nonneg hN0 _)
  · rw [Set.indicator_of_notMem hx, abs_zero]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (by positivity)

lemma sa16p_trunc {q : ℝ} (hpq : p.HolderConjugate q) (hhm : Measurable h) (hpos : ∀ x, 0 < h x)
    (hp : 1 < p) (N : ℕ) :
    Integrable ((sa16p_T hh ℓ hp N).indicator (fun x => |sa16p_g hh ℓ hp x| ^ q)) μ ∧
    ∫ x, (sa16p_T hh ℓ hp N).indicator (fun x => |sa16p_g hh ℓ hp x| ^ q) x ∂μ ≤ ‖ℓ‖ ^ q := by
  have hq : 1 < q := hpq.symm.lt
  have hp0 : 0 < p := by linarith
  have hGi := sa16p_G_integrable hh ℓ hp
  set T := sa16p_T hh ℓ hp N with hT
  have hTm : MeasurableSet T := sa16p_T_measurable hh ℓ hhm hp N
  have hgm := sa16p_g_measurable hh ℓ hhm hp
  have hsm : Measurable (sa16p_s hh ℓ q hp N) := by
    unfold sa16p_s
    exact (((hgm.mul ((hgm.abs).pow_const _)).div hhm)).indicator hTm
  have hsb := sa16p_s_bound hh ℓ hq hpos hp N
  have hmem := sa16p_mulh_memLp hh hsm.aestronglyMeasurable hsb
  have e1 := sa16p_ell_bdd hh ℓ hp hsm hsb hmem
  have hpt1 : ∀ x, sa16p_s hh ℓ q hp N x * sa16p_G hh ℓ hp x =
      T.indicator (fun x => |sa16p_g hh ℓ hp x| ^ q) x := by
    intro x
    by_cases hx : x ∈ T
    · unfold sa16p_s
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, sa16p_G_eq hh ℓ hpos hp x]
      have := (sa16p_phi hq (sa16p_g hh ℓ hp x)).2
      have hh0 := (hpos x).ne'
      calc _ = (sa16p_g hh ℓ hp x * |sa16p_g hh ℓ hp x| ^ (q - 2)) * sa16p_g hh ℓ hp x := by
            field_simp
        _ = _ := by rw [mul_comm]; exact this
    · unfold sa16p_s
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  have hpt2 : ∀ x, ‖sa16p_s hh ℓ q hp N x * h x‖ ^ p =
      T.indicator (fun x => |sa16p_g hh ℓ hp x| ^ q) x := by
    intro x
    by_cases hx : x ∈ T
    · unfold sa16p_s
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have hh0 := (hpos x).ne'
      rw [Real.norm_eq_abs, div_mul_cancel₀ _ hh0, (sa16p_phi hq _).1,
        ← Real.rpow_mul (abs_nonneg _), hpq.symm.sub_one_mul_conj]
    · unfold sa16p_s
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, norm_zero,
        Real.zero_rpow hp0.ne']
  have hint : Integrable (T.indicator (fun x => |sa16p_g hh ℓ hp x| ^ q)) μ := by
    have := hGi.bdd_mul (c := (N : ℝ) ^ (q - 1) * ((N : ℝ) + 1)) hsm.aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact sa16p_s_bound hh ℓ hq hpos hp N x)
    refine this.congr (Eventually.of_forall fun x => hpt1 x)
  refine ⟨hint, ?_⟩
  set I := ∫ x, T.indicator (fun x => |sa16p_g hh ℓ hp x| ^ q) x ∂μ with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => by
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx]; exact Real.rpow_nonneg (abs_nonneg _) _
    · simp [Set.indicator_of_notMem hx]
  have e2 : ℓ (hmem.toLp _) = I := by
    rw [e1]; exact integral_congr_ae (Eventually.of_forall hpt1)
  have e3 : ‖hmem.toLp (fun x => sa16p_s hh ℓ q hp N x * h x)‖ = I ^ (1 / p) := by
    have hp1 : ENNReal.ofReal p ≠ 0 := by simpa using hp0
    rw [Lp.norm_toLp, hmem.eLpNorm_eq_integral_rpow_norm hp1 ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _),
      ENNReal.toReal_ofReal hp0.le, one_div]
    congr 2
    funext x
    exact hpt2 x
  have e4 : I ≤ ‖ℓ‖ * I ^ (1 / p) := by
    have := ℓ.le_opNorm (hmem.toLp (fun x => sa16p_s hh ℓ q hp N x * h x))
    rw [e2, e3, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  exact sa16p_norm_arith hpq hI0 (norm_nonneg _) e4

end Norm

end HRS.Whole.AppendixA.Phase2SA16P
