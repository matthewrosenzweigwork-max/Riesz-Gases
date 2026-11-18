import HRS.MC.S7FCH1B1

/-!
# S7FCH1B2: L² estimates for the Gaussian side of a finite-rank field (H1b, part 2)

For a fixed smooth test function `f` and a random `η : Ω → NegSobolev d r` with
`HasFiniteGaussianCoeffs P η` and `ModeCovBound P η K'` (`0 ≤ K'`), this file proves:

* `S7FCH1_part η T f ω = ∑_{k∈T} f̂(k) η̂_k(ω)` is the finite partial sum of the pairing `eval (η ω) f`;
  it converges pointwise to `eval (η ω) f` along any exhausting sequence of finite sets (`S7FCH1_part_tendsto`);
* `∫ (part T' f - part T f)² ≤ K' · tailW f T` for `T ⊆ T'` (`S7FCH1_part_l2`, from `ModeCovBound`);
* `∫⁻ ‖eval η f - part T f‖ₑ² ≤ ofReal (K' · tailW f T)` (`S7FCH1_fatou`, Fatou along the sequence);
* the convergence of the expectations of products of two such partial sums (`S7FCH1_prod_lim`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH1

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-- The finite partial sum `∑_{k∈T} f̂(k) η̂_k(ω)` of the pairing `eval (η ω) f`. -/
def S7FCH1_part {Ω : Type} {r : ℝ} (η : Ω → NegSobolev d r) (T : Finset (NonzeroLattice d))
    (f : Torus d → ℝ) (ω : Ω) : ℝ :=
  ∑ k ∈ T, Torus.funRealCoeff f k * NegSobolev.fourierCoeff (η ω) k

open Classical in
/-- The tail `∑_{k∉T} f̂(k)²` of the test function (used with `ModeCovBound`). -/
def S7FCH1_tailW (f : Torus d → ℝ) (T : Finset (NonzeroLattice d)) : ℝ :=
  ∑' k, if k ∈ T then 0 else Torus.funRealCoeff f k ^ 2

/-- The pairing has absolutely summable terms for every realisation and every smooth `f`. -/
theorem S7FCH1_summable_pair {r : ℝ} (F : NegSobolev d r) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    Summable (fun k : NonzeroLattice d => Torus.funRealCoeff f k * NegSobolev.fourierCoeff F k) := by
  have hw := S7FCH1_wsum hf r
  have hc := (NegSobolev.coord_sq F).1
  refine Summable.of_norm_bounded ((hc.add hw).mul_left (1 / 2)) (fun k => ?_)
  have e : NegSobolev.fourierCoeff F k = Lattice.jp k.1 ^ r * NegSobolev.coord F k := rfl
  have hj : (Lattice.jp k.1 ^ r * Torus.funRealCoeff f k) ^ 2 =
      Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff f k ^ 2 := by
    rw [mul_pow, Torus.jp_rpow_sq]
  rw [e, Real.norm_eq_abs]
  have h1 : Torus.funRealCoeff f k * (Lattice.jp k.1 ^ r * NegSobolev.coord F k) =
      NegSobolev.coord F k * (Lattice.jp k.1 ^ r * Torus.funRealCoeff f k) := by ring
  rw [h1, abs_mul]
  have h2 : |Lattice.jp k.1 ^ r * Torus.funRealCoeff f k| ^ 2 =
      Lattice.jp k.1 ^ (2 * r) * Torus.funRealCoeff f k ^ 2 := by
    rw [sq_abs, hj]
  nlinarith [sq_nonneg (|NegSobolev.coord F k| - |Lattice.jp k.1 ^ r * Torus.funRealCoeff f k|),
    sq_abs (NegSobolev.coord F k)]

/-- The pairing `eval (η ω) f` is the sum of the absolutely summable series. -/
theorem S7FCH1_hasSum_pair {r : ℝ} (F : NegSobolev d r) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    HasSum (fun k : NonzeroLattice d => Torus.funRealCoeff f k * NegSobolev.fourierCoeff F k)
      (NegSobolev.eval F f) := by
  have e : NegSobolev.eval F f =
      ∑' k : NonzeroLattice d, Torus.funRealCoeff f k * NegSobolev.fourierCoeff F k := by
    unfold NegSobolev.eval
    exact tsum_congr fun k => by ring
  rw [e]
  exact (S7FCH1_summable_pair F hf).hasSum

/-- Along an exhausting sequence of finite sets the partial sums converge to the pairing. -/
theorem S7FCH1_part_tendsto {Ω : Type} {r : ℝ} (η : Ω → NegSobolev d r) (ω : Ω) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) (N : ℕ → Finset (NonzeroLattice d)) (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => S7FCH1_part η (N n) f ω) atTop (𝓝 (NegSobolev.eval (η ω) f)) :=
  (S7FCH1_hasSum_pair (η ω) hf).comp hN

/-- Splitting a sum of a function that vanishes on `T` (`∑_{T'} 1_{k∉T} F(k) = ∑_{T'} F - ∑_T F`). -/
theorem S7FCH1_sum_ite_diff {α : Type*} [DecidableEq α] (T T' : Finset α) (h : T ⊆ T') (F : α → ℝ) :
    ∑ k ∈ T', (if k ∈ T then 0 else F k) = ∑ k ∈ T', F k - ∑ k ∈ T, F k := by
  have h1 : ∑ k ∈ T' \ T, (if k ∈ T then 0 else F k) + ∑ k ∈ T, (if k ∈ T then 0 else F k) =
      ∑ k ∈ T', (if k ∈ T then 0 else F k) := Finset.sum_sdiff h
  have h2 : ∑ k ∈ T' \ T, F k + ∑ k ∈ T, F k = ∑ k ∈ T', F k := Finset.sum_sdiff h
  have h3 : ∑ k ∈ T' \ T, (if k ∈ T then 0 else F k) = ∑ k ∈ T' \ T, F k :=
    Finset.sum_congr rfl fun k hk => by simp [(Finset.mem_sdiff.1 hk).2]
  have h4 : ∑ k ∈ T, (if k ∈ T then 0 else F k) = 0 :=
    Finset.sum_eq_zero fun k hk => by simp [hk]
  linarith

open Classical in
/-- The difference of two partial sums is the tail sum over `T' \ T`. -/
theorem S7FCH1_part_diff {Ω : Type} {r : ℝ} (η : Ω → NegSobolev d r) (T T' : Finset (NonzeroLattice d))
    (h : T ⊆ T') (f : Torus d → ℝ) (ω : Ω) :
    S7FCH1_part η T' f ω - S7FCH1_part η T f ω =
      ∑ k ∈ T', (if k ∈ T then 0 else Torus.funRealCoeff f k) * NegSobolev.fourierCoeff (η ω) k := by
  have e : ∑ k ∈ T', (if k ∈ T then 0 else Torus.funRealCoeff f k) * NegSobolev.fourierCoeff (η ω) k =
      ∑ k ∈ T', (if k ∈ T then 0 else Torus.funRealCoeff f k * NegSobolev.fourierCoeff (η ω) k) :=
    Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  rw [e]
  unfold S7FCH1_part
  exact (S7FCH1_sum_ite_diff T T' h (fun k => Torus.funRealCoeff f k * NegSobolev.fourierCoeff (η ω) k)).symm

open Classical in
theorem S7FCH1_tailW_nonneg (f : Torus d → ℝ) (T : Finset (NonzeroLattice d)) :
    0 ≤ S7FCH1_tailW f T :=
  tsum_nonneg fun k => by split_ifs <;> positivity

open Classical in
/-- The tail of the test function tends to zero along an exhausting sequence. -/
theorem S7FCH1_tailW_tendsto {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (N : ℕ → Finset (NonzeroLattice d))
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => S7FCH1_tailW f (N n)) atTop (𝓝 0) :=
  (S7FCH1_tail_tendsto (fun k => Torus.funRealCoeff f k ^ 2) (S7FCH1_sq_summable hf)).comp hN

open Classical in
/-- The `L²` bound on the difference of two partial sums (from `ModeCovBound`). -/
theorem S7FCH1_part_l2 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {r : ℝ} (η : Ω → NegSobolev d r) (K' : ℝ) (hK : ModeCovBound P η K') (hK0 : 0 ≤ K')
    (T T' : Finset (NonzeroLattice d)) (h : T ⊆ T') (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    ∫ ω, (S7FCH1_part η T' f ω - S7FCH1_part η T f ω) ^ 2 ∂P ≤ K' * S7FCH1_tailW f T := by
  have e : ∀ ω, (S7FCH1_part η T' f ω - S7FCH1_part η T f ω) ^ 2 =
      (∑ k ∈ T', (if k ∈ T then 0 else Torus.funRealCoeff f k) * NegSobolev.fourierCoeff (η ω) k) ^ 2 :=
    fun ω => by rw [S7FCH1_part_diff η T T' h f ω]
  have hint : ∫ ω, (S7FCH1_part η T' f ω - S7FCH1_part η T f ω) ^ 2 ∂P =
      ∫ ω, (∑ k ∈ T', (if k ∈ T then 0 else Torus.funRealCoeff f k) * NegSobolev.fourierCoeff (η ω) k) ^ 2 ∂P :=
    integral_congr_ae (Eventually.of_forall e)
  rw [hint]
  have hb := hK T' (fun k => if k ∈ T then 0 else Torus.funRealCoeff f k)
  have hsum : Summable (fun k : NonzeroLattice d => if k ∈ T then (0 : ℝ) else Torus.funRealCoeff f k ^ 2) :=
    Summable.of_nonneg_of_le (fun k => by split_ifs <;> positivity)
      (fun k => by split_ifs <;> simp [sq_nonneg]) (S7FCH1_sq_summable hf)
  have hsumle : ∑ k ∈ T', (if k ∈ T then (0 : ℝ) else Torus.funRealCoeff f k) ^ 2 ≤ S7FCH1_tailW f T := by
    unfold S7FCH1_tailW
    calc ∑ k ∈ T', (if k ∈ T then (0 : ℝ) else Torus.funRealCoeff f k) ^ 2
        = ∑ k ∈ T', (if k ∈ T then (0 : ℝ) else Torus.funRealCoeff f k ^ 2) :=
          Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
      _ ≤ ∑' k, (if k ∈ T then (0 : ℝ) else Torus.funRealCoeff f k ^ 2) :=
          Summable.sum_le_tsum _ (fun k _ => by split_ifs <;> positivity) hsum
  calc _ ≤ K' * ∑ k ∈ T', (if k ∈ T then (0 : ℝ) else Torus.funRealCoeff f k) ^ 2 := hb
    _ ≤ K' * S7FCH1_tailW f T := mul_le_mul_of_nonneg_left hsumle hK0

/-- The integral of the square of a real function in terms of its `enorm`. -/
theorem S7FCH1_lintegral_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : Ω → ℝ)
    (hx : Integrable (fun ω => x ω ^ 2) P) :
    ∫⁻ ω, ‖x ω‖ₑ ^ 2 ∂P = ENNReal.ofReal (∫ ω, x ω ^ 2 ∂P) := by
  rw [ofReal_integral_eq_lintegral_ofReal hx (Eventually.of_forall fun ω => sq_nonneg _)]
  refine lintegral_congr fun ω => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

/-- An `enorm`-square bound in `ℝ≥0∞` gives `L²` membership and the real bound. -/
theorem S7FCH1_memLp_of_lintegral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {x : Ω → ℝ}
    (hx : AEStronglyMeasurable x P) {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ ω, ‖x ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal c) :
    MemLp x 2 P ∧ ∫ ω, x ω ^ 2 ∂P ≤ c := by
  have hsq : ∀ ω, ‖x ω ^ 2‖ₑ = ‖x ω‖ₑ ^ 2 := fun ω => by
    rw [Real.enorm_eq_ofReal (sq_nonneg _), Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
      sq_abs]
  have hfin : ∫⁻ ω, ‖x ω ^ 2‖ₑ ∂P < ∞ := by
    simp only [hsq]
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω => x ω ^ 2) P := ⟨hx.pow 2, hfin⟩
  refine ⟨(memLp_two_iff_integrable_sq hx).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _) (hx.pow 2)]
  refine ENNReal.toReal_le_of_le_ofReal hc ?_
  have e : ∫⁻ ω, ENNReal.ofReal (x ω ^ 2) ∂P = ∫⁻ ω, ‖x ω‖ₑ ^ 2 ∂P :=
    lintegral_congr fun ω => by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [e]
  exact h

/-- Coordinates of a Gaussian field are Gaussian. -/
theorem S7FCH1_coord_gauss {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    {η : Ω → NegSobolev d r} (hG : HasFiniteGaussianCoeffs P η) (k : NonzeroLattice d) :
    HasGaussianLaw (fun ω => NegSobolev.fourierCoeff (η ω) k) P := by
  have h := (hG {k}).1.eval (⟨k, Finset.mem_singleton_self k⟩ : ({k} : Finset (NonzeroLattice d)))
  exact h

/-- The pairing of a Gaussian field is measurable. -/
theorem S7FCH1_part_aesm {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    {η : Ω → NegSobolev d r} (hG : HasFiniteGaussianCoeffs P η) (T : Finset (NonzeroLattice d))
    (f : Torus d → ℝ) :
    AEStronglyMeasurable (fun ω => S7FCH1_part η T f ω) P := by
  unfold S7FCH1_part
  have h := Finset.aestronglyMeasurable_sum T fun k _ =>
    ((S7FCH1_coord_gauss hG k).aemeasurable.aestronglyMeasurable).const_mul (Torus.funRealCoeff f k)
  simpa only [Finset.sum_fn] using h

/-- The partial sums are in `L²`. -/
theorem S7FCH1_part_memLp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    {η : Ω → NegSobolev d r} (hG : HasFiniteGaussianCoeffs P η) (T : Finset (NonzeroLattice d))
    (f : Torus d → ℝ) :
    MemLp (fun ω => S7FCH1_part η T f ω) 2 P := by
  unfold S7FCH1_part
  have h := memLp_finsetSum' T fun k _ => ((S7FCH1_coord_gauss hG k).memLp_two).const_mul (Torus.funRealCoeff f k)
  simpa only [Finset.sum_fn] using h

/-- The pairing `eval (η ω) f` is measurable (an a.e. limit of partial sums). -/
theorem S7FCH1_eval_aesm {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    {η : Ω → NegSobolev d r} (hG : HasFiniteGaussianCoeffs P η) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    (N : ℕ → Finset (NonzeroLattice d)) (hN : Tendsto N atTop atTop) :
    AEStronglyMeasurable (fun ω => NegSobolev.eval (η ω) f) P :=
  aestronglyMeasurable_of_tendsto_ae (u := atTop) (f := fun n ω => S7FCH1_part η (N n) f ω)
    (fun n => S7FCH1_part_aesm hG (N n) f)
    (ae_of_all _ fun ω => S7FCH1_part_tendsto η ω hf N hN)

/-- Fatou bound: `∫⁻ ‖eval η f - part T f‖ₑ² ≤ ofReal (K' · tailW f T)`. -/
theorem S7FCH1_fatou {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (K' : ℝ) (hK : ModeCovBound P η K')
    (hK0 : 0 ≤ K') (N : ℕ → Finset (NonzeroLattice d)) (hN : Tendsto N atTop atTop)
    (T : Finset (NonzeroLattice d)) (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    ∫⁻ ω, ‖NegSobolev.eval (η ω) f - S7FCH1_part η T f ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (K' * S7FCH1_tailW f T) := by
  have hdiff : ∀ n, AEStronglyMeasurable (fun ω => S7FCH1_part η (N n) f ω - S7FCH1_part η T f ω) P :=
    fun n => (S7FCH1_part_aesm hG (N n) f).sub (S7FCH1_part_aesm hG T f)
  have hmeas : ∀ n, AEMeasurable (fun ω => ‖S7FCH1_part η (N n) f ω - S7FCH1_part η T f ω‖ₑ ^ 2) P :=
    fun n => ((hdiff n).aemeasurable.enorm).pow_const 2
  have hlim : ∀ ω, Tendsto (fun n => ‖S7FCH1_part η (N n) f ω - S7FCH1_part η T f ω‖ₑ ^ 2) atTop
      (𝓝 (‖NegSobolev.eval (η ω) f - S7FCH1_part η T f ω‖ₑ ^ 2)) := by
    intro ω
    have h1 : Tendsto (fun n => S7FCH1_part η (N n) f ω - S7FCH1_part η T f ω) atTop
        (𝓝 (NegSobolev.eval (η ω) f - S7FCH1_part η T f ω)) :=
      (S7FCH1_part_tendsto η ω hf N hN).sub_const _
    exact ((ENNReal.continuous_pow 2).tendsto _).comp h1.enorm
  have hev : ∀ᶠ n in atTop, T ≤ N n := hN.eventually (eventually_ge_atTop T)
  have hbound : ∀ᶠ n in atTop, ∫⁻ ω, ‖S7FCH1_part η (N n) f ω - S7FCH1_part η T f ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (K' * S7FCH1_tailW f T) := by
    filter_upwards [hev] with n hn
    have hTn : T ⊆ N n := hn
    have hmem := (S7FCH1_part_memLp hG (N n) f).sub (S7FCH1_part_memLp hG T f)
    have hint : Integrable (fun ω => (S7FCH1_part η (N n) f ω - S7FCH1_part η T f ω) ^ 2) P :=
      hmem.integrable_sq
    rw [S7FCH1_lintegral_sq P _ hint]
    exact ENNReal.ofReal_le_ofReal (S7FCH1_part_l2 P η K' hK hK0 T (N n) hTn f hf)
  calc ∫⁻ ω, ‖NegSobolev.eval (η ω) f - S7FCH1_part η T f ω‖ₑ ^ 2 ∂P
      = ∫⁻ ω, liminf (fun n => ‖S7FCH1_part η (N n) f ω - S7FCH1_part η T f ω‖ₑ ^ 2) atTop ∂P :=
        lintegral_congr fun ω => ((hlim ω).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ ω, ‖S7FCH1_part η (N n) f ω - S7FCH1_part η T f ω‖ₑ ^ 2 ∂P) atTop :=
        lintegral_liminf_le' hmeas
    _ ≤ ENNReal.ofReal (K' * S7FCH1_tailW f T) :=
        liminf_le_of_frequently_le' (hbound.frequently)

/-- Cauchy-Schwarz in `L²`: `∫ |x y| ≤ √(∫ x²) √(∫ y²)`. -/
theorem S7FCH1_cs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {x y : Ω → ℝ}
    (hx : MemLp x 2 P) (hy : MemLp y 2 P) :
    ∫ ω, |x ω * y ω| ∂P ≤ Real.sqrt (∫ ω, x ω ^ 2 ∂P) * Real.sqrt (∫ ω, y ω ^ 2 ∂P) := by
  have hp : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hx' : MemLp (fun ω => |x ω|) (ENNReal.ofReal 2) P := by
    rw [hp]
    have := hx.norm
    simpa [Real.norm_eq_abs] using this
  have hy' : MemLp (fun ω => |y ω|) (ENNReal.ofReal 2) P := by
    rw [hp]
    have := hy.norm
    simpa [Real.norm_eq_abs] using this
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ fun ω => abs_nonneg (x ω)) (ae_of_all _ fun ω => abs_nonneg (y ω)) hx' hy'
  have e1 : ∀ z : Ω → ℝ, ∫ ω, |z ω| ^ (2 : ℝ) ∂P = ∫ ω, z ω ^ 2 ∂P := fun z =>
    integral_congr_ae (ae_of_all _ fun ω => by simp only [Real.rpow_two, sq_abs])
  rw [e1 x, e1 y, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  calc ∫ ω, |x ω * y ω| ∂P = ∫ ω, |x ω| * |y ω| ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => by simp only [abs_mul])
    _ ≤ _ := by simpa using h

/-- Expectations of products of `L²`-convergent sequences converge. -/
theorem S7FCH1_prod_lim {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (a b : ℕ → Ω → ℝ) (a0 b0 : Ω → ℝ) (ha : ∀ n, MemLp (a n) 2 P) (hb : ∀ n, MemLp (b n) 2 P)
    (ha0 : MemLp a0 2 P) (hb0 : MemLp b0 2 P)
    (hA : Tendsto (fun n => ∫ ω, (a n ω - a0 ω) ^ 2 ∂P) atTop (𝓝 0))
    (hB : Tendsto (fun n => ∫ ω, (b n ω - b0 ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, a n ω * b n ω ∂P) atTop (𝓝 (∫ ω, a0 ω * b0 ω ∂P)) := by
  have hdA : ∀ n, MemLp (fun ω => a n ω - a0 ω) 2 P := fun n => (ha n).sub ha0
  have hdB : ∀ n, MemLp (fun ω => b n ω - b0 ω) 2 P := fun n => (hb n).sub hb0
  -- integrability of the products
  have iprod : ∀ (x y : Ω → ℝ), MemLp x 2 P → MemLp y 2 P → Integrable (fun ω => x ω * y ω) P :=
    fun x y hx hy => hx.integrable_mul hy
  -- decomposition of the difference of products
  have hsplit : ∀ n, ∫ ω, a n ω * b n ω ∂P - ∫ ω, a0 ω * b0 ω ∂P =
      ∫ ω, (a n ω - a0 ω) * b n ω ∂P + ∫ ω, a0 ω * (b n ω - b0 ω) ∂P := by
    intro n
    rw [← integral_add (iprod _ _ (hdA n) (hb n)) (iprod _ _ ha0 (hdB n)),
      ← integral_sub (iprod _ _ (ha n) (hb n)) (iprod _ _ ha0 hb0)]
    exact integral_congr_ae (ae_of_all _ fun ω => by ring)
  -- bound on the second moments of `b n`
  have hbsq : ∀ n, ∫ ω, b n ω ^ 2 ∂P ≤ 2 * ∫ ω, b0 ω ^ 2 ∂P + 2 * ∫ ω, (b n ω - b0 ω) ^ 2 ∂P := by
    intro n
    have i1 : Integrable (fun ω => b0 ω ^ 2) P := hb0.integrable_sq
    have i2 : Integrable (fun ω => (b n ω - b0 ω) ^ 2) P := (hdB n).integrable_sq
    calc ∫ ω, b n ω ^ 2 ∂P ≤ ∫ ω, (2 * b0 ω ^ 2 + 2 * (b n ω - b0 ω) ^ 2) ∂P :=
          integral_mono (hb n).integrable_sq ((i1.const_mul 2).add (i2.const_mul 2))
            fun ω => by nlinarith [sq_nonneg (2 * b0 ω - b n ω)]
      _ = 2 * ∫ ω, b0 ω ^ 2 ∂P + 2 * ∫ ω, (b n ω - b0 ω) ^ 2 ∂P := by
          rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul]
  set C : ℝ := Real.sqrt (2 * ∫ ω, b0 ω ^ 2 ∂P + 2) with hC_def
  -- first term
  have h1 : Tendsto (fun n => ∫ ω, (a n ω - a0 ω) * b n ω ∂P) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => Real.sqrt (∫ ω, (a n ω - a0 ω) ^ 2 ∂P) * C) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp hA).mul_const C
      simpa [Real.sqrt_zero] using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hB.eventually (gt_mem_nhds one_pos)] with n hn
    rw [Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs).trans ?_
    have hcs := S7FCH1_cs P (hdA n) (hb n)
    have hsq : Real.sqrt (∫ ω, b n ω ^ 2 ∂P) ≤ C := by
      apply Real.sqrt_le_sqrt
      linarith [hbsq n]
    calc ∫ ω, |(a n ω - a0 ω) * b n ω| ∂P ≤ Real.sqrt (∫ ω, (a n ω - a0 ω) ^ 2 ∂P) *
          Real.sqrt (∫ ω, b n ω ^ 2 ∂P) := hcs
      _ ≤ Real.sqrt (∫ ω, (a n ω - a0 ω) ^ 2 ∂P) * C :=
          mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ = _ := rfl
  -- second term
  have h2 : Tendsto (fun n => ∫ ω, a0 ω * (b n ω - b0 ω) ∂P) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => Real.sqrt (∫ ω, a0 ω ^ 2 ∂P) *
        Real.sqrt (∫ ω, (b n ω - b0 ω) ^ 2 ∂P)) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp hB).const_mul (Real.sqrt (∫ ω, a0 ω ^ 2 ∂P))
      simpa [Real.sqrt_zero] using this
    refine squeeze_zero_norm' (Eventually.of_forall fun n => ?_) hlim
    rw [Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs).trans ?_
    exact S7FCH1_cs P ha0 (hdB n)
  -- conclusion
  rw [← tendsto_sub_nhds_zero_iff]
  have hsum := h1.add h2
  rw [zero_add] at hsum
  refine hsum.congr fun n => ?_
  exact (hsplit n).symm

end HRS.MC.Sec7.S7FCH1

end
