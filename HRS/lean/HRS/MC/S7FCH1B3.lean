import HRS.MC.S7FCH1B2
import HRS.MC.QRPWick

/-!
# S7FCH1B3: the Gaussian side of a finite-rank field (`s7_FC_H1b_gauss`, assembly)

Proof of `HRS.MC.Sec7.FCPlan.s7_FC_H1b_gauss` (statement copied verbatim from `HRS/MC/S7FCPlan.lean`; the tie is
`HRS/MC/S7FCH1Tie.lean`).  Route:

* `wickSection` over a finite set `T` equals `Y_T - ∫ Y_T` with `Y_T = ½ ∑_{k,l∈T} ĥ°_{kl} η̂_k η̂_l`, and
  `Y_T = ½ ∑_{ij} c_ij part_i(T) part_j(T)` (finite-rank expansion, `S7FCH1_Y_eq_part`).
* Pointwise, along an exhausting sequence, `Y_{N n} → K.quad (η)`; the expectations converge by the `L²` convergence
  of the partial sums (`S7FCH1B2`, `S7FCH1_prod_lim`).
* For `S ⊆ T`, `wickSection T - wickSection S` is a centred Wick sum over `T` with matrix `½ ĥ° 1[¬(S×S)]`, whose `L²`
  norm is bounded by `qrs_wick_var_fin_proof` by `½ K'² · tailHS ĥ° S`.  Fatou along the sequence gives the bound for
  the limit, and `tailHS → 0` along finite sets gives `IsHalfWick`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCH1

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan

variable {d : ℕ}

/-! ### Mode bounds -/

/-- A mode bound with constant `K'` is also one with the nonnegative constant `max K' 0`. -/
theorem S7FCH1_mcb_max {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ} (η : Ω → NegSobolev d r)
    (K' : ℝ) (hK : ModeCovBound P η K') : ModeCovBound P η (max K' 0) :=
  fun S a => (hK S a).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Finset.sum_nonneg fun k _ => sq_nonneg (a k)))

/-- The mode bound restricted to a finite set `T`, for families indexed by the subtype `↥T`. -/
theorem S7FCH1_hK_index {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ} (η : Ω → NegSobolev d r)
    (K : ℝ) (hK : ModeCovBound P η K) (T : Finset (NonzeroLattice d)) (a : ↥T → ℝ) :
    ∫ ω, (∑ i : ↥T, a i * NegSobolev.fourierCoeff (η ω) i.1) ^ 2 ∂P ≤ K * ∑ i : ↥T, a i ^ 2 := by
  obtain ⟨a', ha'⟩ : ∃ a' : NonzeroLattice d → ℝ, ∀ i : ↥T, a' i.1 = a i :=
    ⟨fun k => if h : k ∈ T then a ⟨k, h⟩ else 0, fun i => dif_pos i.2⟩
  have hL1 : ∀ ω, ∑ i : ↥T, a i * NegSobolev.fourierCoeff (η ω) i.1 =
      ∑ i : ↥T, a' i.1 * NegSobolev.fourierCoeff (η ω) i.1 := fun ω =>
    Finset.sum_congr rfl fun i _ => by rw [ha' i]
  have hL2 : ∀ ω, ∑ i : ↥T, a' i.1 * NegSobolev.fourierCoeff (η ω) i.1 =
      ∑ k ∈ T, a' k * NegSobolev.fourierCoeff (η ω) k := fun ω =>
    Finset.sum_coe_sort T (fun k => a' k * NegSobolev.fourierCoeff (η ω) k)
  have hS1 : ∑ i : ↥T, a i ^ 2 = ∑ i : ↥T, a' i.1 ^ 2 :=
    Finset.sum_congr rfl fun i _ => by rw [ha' i]
  have hS2 : ∑ i : ↥T, a' i.1 ^ 2 = ∑ k ∈ T, a' k ^ 2 :=
    Finset.sum_coe_sort T (fun k => a' k ^ 2)
  have hmc := hK T a'
  calc ∫ ω, (∑ i : ↥T, a i * NegSobolev.fourierCoeff (η ω) i.1) ^ 2 ∂P
      = ∫ ω, (∑ k ∈ T, a' k * NegSobolev.fourierCoeff (η ω) k) ^ 2 ∂P :=
        integral_congr_ae (ae_of_all _ fun ω => by simp only [hL1 ω, hL2 ω])
    _ ≤ K * ∑ k ∈ T, a' k ^ 2 := hmc
    _ = K * ∑ i : ↥T, a i ^ 2 := by rw [hS1, hS2]

/-! ### The `L²` Wick bound on a finite index set -/

/-- Sums over a finite set and over its subtype agree (for a double sum). -/
theorem S7FCH1_coe_sum2 {ι : Type} {M : Type} [AddCommMonoid M] (T : Finset ι) (F : ι → ι → M) :
    ∑ k ∈ T, ∑ l ∈ T, F k l = ∑ i : ↥T, ∑ j : ↥T, F i.1 j.1 :=
  (Finset.sum_coe_sort T (fun k => ∑ l ∈ T, F k l)).symm.trans
    (Finset.sum_congr rfl fun i _ => (Finset.sum_coe_sort T (fun l => F i.1 l)).symm)

/-- The `(k,l)` summand of a centred Wick sum. -/
def S7FCH1_Wf {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {r : ℝ} (η : Ω → NegSobolev d r)
    (A : NonzeroLattice d → NonzeroLattice d → ℝ) (ω : Ω) (k l : NonzeroLattice d) : ℝ :=
  A k l * (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
    ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P)

/-- Centred Wick sums over a finite set `T` have the `L²` bound of `qrs_wick_var_fin_proof`. -/
theorem S7FCH1_wick_T {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (K : ℝ) (hK : ModeCovBound P η K)
    (T : Finset (NonzeroLattice d)) (A : NonzeroLattice d → NonzeroLattice d → ℝ) :
    MemLp (fun ω => ∑ k ∈ T, ∑ l ∈ T, A k l * (NegSobolev.fourierCoeff (η ω) k *
      NegSobolev.fourierCoeff (η ω) l - ∫ ω', NegSobolev.fourierCoeff (η ω') k *
        NegSobolev.fourierCoeff (η ω') l ∂P)) 2 P ∧
    ∫ ω, (∑ k ∈ T, ∑ l ∈ T, A k l * (NegSobolev.fourierCoeff (η ω) k *
      NegSobolev.fourierCoeff (η ω) l - ∫ ω', NegSobolev.fourierCoeff (η ω') k *
        NegSobolev.fourierCoeff (η ω') l ∂P)) ^ 2 ∂P ≤
      2 * K ^ 2 * ∑ k ∈ T, ∑ l ∈ T, A k l ^ 2 := by
  obtain ⟨h1, h2⟩ := HRS.MC.QRSpec.Wick.qrs_wick_var_fin_proof P
    (fun (i : ↥T) (ω : Ω) => NegSobolev.fourierCoeff (η ω) i.1) (hG T).1 (fun i => (hG T).2 i.1) K
    (S7FCH1_hK_index P η K hK T) (fun i j => A i.1 j.1)
  have hsub : ∀ ω, ∑ i : ↥T, ∑ j : ↥T, S7FCH1_Wf P η A ω i.1 j.1 =
      ∑ k ∈ T, ∑ l ∈ T, S7FCH1_Wf P η A ω k l := fun ω => (S7FCH1_coe_sum2 T (S7FCH1_Wf P η A ω)).symm
  have hR : ∑ k ∈ T, ∑ l ∈ T, A k l ^ 2 = ∑ i : ↥T, ∑ j : ↥T, A i.1 j.1 ^ 2 :=
    S7FCH1_coe_sum2 T (fun k l => A k l ^ 2)
  refine ⟨MemLp.ae_eq (ae_of_all _ fun ω => hsub ω) h1, ?_⟩
  refine (le_of_eq (integral_congr_ae (ae_of_all _ fun ω => congrArg (fun x : ℝ => x ^ 2) (hsub ω).symm))).trans
    (h2.trans (le_of_eq ?_))
  rw [hR]

/-! ### Finite-sum and tail algebra (decidability is only used through `split_ifs`) -/

/-- The truncated Wick matrix `½ ĥ°_{kl} 1[¬(k ∈ S ∧ l ∈ S)]`. -/
def S7FCH1_mat {ι : Type} [DecidableEq ι] (w : ι → ι → ℝ) (S : Finset ι) (k l : ι) : ℝ :=
  (1 / 2) * (if k ∈ S ∧ l ∈ S then 0 else w k l)

/-- The summand `½ w_{kl} G_{kl}` of a Wick section. -/
def S7FCH1_F {ι : Type} (w G : ι → ι → ℝ) (k l : ι) : ℝ := (1 / 2) * (w k l * G k l)

/-- Splitting a double sum over `T × T` against `S × S` (for `S ⊆ T`). -/
theorem S7FCH1_split {ι : Type} [DecidableEq ι] (w G : ι → ι → ℝ) (S T : Finset ι) (h : S ⊆ T) :
    ∑ k ∈ T, ∑ l ∈ T, S7FCH1_mat w S k l * G k l =
      ∑ k ∈ T, ∑ l ∈ T, S7FCH1_F w G k l - ∑ k ∈ S, ∑ l ∈ S, S7FCH1_F w G k l := by
  have hpt : ∀ k l, S7FCH1_mat w S k l * G k l =
      (if k ∈ S ∧ l ∈ S then 0 else S7FCH1_F w G k l) := by
    intro k l
    unfold S7FCH1_mat S7FCH1_F
    split_ifs <;> ring
  have hsub : ∀ k l, (if k ∈ S ∧ l ∈ S then (0 : ℝ) else S7FCH1_F w G k l) =
      S7FCH1_F w G k l - (if k ∈ S ∧ l ∈ S then S7FCH1_F w G k l else 0) := by
    intro k l
    split_ifs <;> ring
  have hb : ∑ k ∈ T, ∑ l ∈ T, (if k ∈ S ∧ l ∈ S then S7FCH1_F w G k l else 0) =
      ∑ k ∈ S, ∑ l ∈ S, S7FCH1_F w G k l := by
    have hk : ∀ k ∈ T, k ∉ S →
        ∑ l ∈ T, (if k ∈ S ∧ l ∈ S then S7FCH1_F w G k l else 0) = 0 :=
      fun k _ hkS => by simp [hkS]
    refine (Finset.sum_subset h hk).symm.trans ?_
    refine Finset.sum_congr rfl fun k hkS => ?_
    have hz : ∀ l ∈ T, l ∉ S → (if k ∈ S ∧ l ∈ S then S7FCH1_F w G k l else 0) = 0 :=
      fun l _ hlS => by simp [hlS]
    refine (Finset.sum_subset h hz).symm.trans ?_
    exact Finset.sum_congr rfl fun l hlS => by simp [hkS, hlS]
  simp only [hpt, hsub, Finset.sum_sub_distrib]
  rw [hb]

/-- The matrix `S7FCH1_mat` has squared Hilbert-Schmidt mass at most `¼ tailHS`. -/
theorem S7FCH1_mat_sq_le {ι : Type} [DecidableEq ι] (w : ι → ι → ℝ)
    (hs : Summable (fun p : ι × ι => w p.1 p.2 ^ 2)) (S T : Finset ι) :
    ∑ k ∈ T, ∑ l ∈ T, (S7FCH1_mat w S k l) ^ 2 ≤ (1 / 4) * tailHS w S := by
  unfold tailHS
  rw [← tsum_mul_left]
  refine le_trans ?_ (Summable.sum_le_tsum (T ×ˢ T) (fun p _ => ?_) ?_)
  · rw [Finset.sum_product]
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
    simp only [S7FCH1_mat]
    try dsimp only
    split_ifs <;> exact le_of_eq (by ring)
  · try dsimp only
    split_ifs <;> positivity
  · exact Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
      (fun p => by split_ifs <;> nlinarith [sq_nonneg (w p.1 p.2)]) (hs.mul_left (1 / 4))

/-- The tail `tailHS` of a summable square family tends to zero along finite sets. -/
theorem S7FCH1_tailHS_tendsto {ι : Type} [DecidableEq ι] (A : ι → ι → ℝ)
    (hA : Summable (fun p : ι × ι => A p.1 p.2 ^ 2)) :
    Tendsto (fun F : Finset ι => tailHS A F) atTop (𝓝 0) := by
  have hP : Tendsto (fun F : Finset ι => F ×ˢ F) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun R => ⟨R.image Prod.fst ∪ R.image Prod.snd, fun F hF => ?_⟩
    intro p hp
    rw [Finset.mem_product]
    exact ⟨hF (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp)),
      hF (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hp))⟩
  have hR := (S7FCH1_tail_tendsto (fun p : ι × ι => A p.1 p.2 ^ 2) hA).comp hP
  have hlo : ∀ F : Finset ι, 0 ≤ tailHS A F := fun F => by
    unfold tailHS
    exact tsum_nonneg fun p => by split_ifs <;> positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR (Eventually.of_forall hlo)
    (Eventually.of_forall fun F => ?_)
  show tailHS A F ≤ ∑' a : ι × ι, (if a ∈ F ×ˢ F then (0 : ℝ) else A a.1 a.2 ^ 2)
  unfold tailHS
  refine Summable.tsum_le_tsum (fun p => ?_) ?_ ?_
  · split_ifs with h1 h2 <;> simp_all [Finset.mem_product]
  · exact Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
      (fun p => by split_ifs <;> first | positivity | exact le_rfl) hA
  · exact Summable.of_nonneg_of_le (fun p => by split_ifs <;> positivity)
      (fun p => by split_ifs <;> first | positivity | exact le_rfl) hA

/-! ### The Wick section and the quadratic form `Y_T` -/

/-- Integrability of products of two coordinates of a finite-rank Gaussian field. -/
theorem S7FCH1_int_pair {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    {η : Ω → NegSobolev d r} (hG : HasFiniteGaussianCoeffs P η) (k l : NonzeroLattice d) :
    Integrable (fun ω => NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l) P :=
  (S7FCH1_coord_gauss hG k).memLp_two.integrable_mul (S7FCH1_coord_gauss hG l).memLp_two

/-- The Wick quadratic form `Y_T(ω) = ½ ∑_{k,l∈T} ĥ°_{kl} η̂_k(ω) η̂_l(ω)`. -/
def S7FCH1_Y {Ω : Type} {r : ℝ} (η : Ω → NegSobolev d r) (μ : Measure (Torus d)) (K : FRKernel d)
    (T : Finset (NonzeroLattice d)) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ k ∈ T, ∑ l ∈ T, wickCoeff μ K.toFun k l *
    (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l)

/-- The Wick section is the centred Wick quadratic form. -/
theorem S7FCH1_wS_eq_Y {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (K : FRKernel d) (T : Finset (NonzeroLattice d)) (ω : Ω) :
    wickSection P η μ K.toFun T ω = S7FCH1_Y η μ K T ω - ∫ ω', S7FCH1_Y η μ K T ω' ∂P := by
  have hint : ∫ ω', S7FCH1_Y η μ K T ω' ∂P = (1 / 2) * ∑ k ∈ T, ∑ l ∈ T, wickCoeff μ K.toFun k l *
      ∫ ω', (NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l) ∂P := by
    unfold S7FCH1_Y
    rw [integral_const_mul, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (S7FCH1_int_pair hG k l).const_mul (wickCoeff μ K.toFun k l)]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (S7FCH1_int_pair hG k l).const_mul (wickCoeff μ K.toFun k l)]
    exact Finset.sum_congr rfl fun l _ => integral_const_mul _ _
  rw [hint]
  unfold wickSection S7FCH1_Y
  simp only [mul_sub, Finset.sum_sub_distrib]

/-- Difference of two Wick sections is a centred Wick sum with the truncated matrix. -/
theorem S7FCH1_wS_diff {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {r : ℝ}
    (η : Ω → NegSobolev d r) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (K : FRKernel d)
    (S T : Finset (NonzeroLattice d)) (h : S ⊆ T) (ω : Ω) :
    wickSection P η μ K.toFun T ω - wickSection P η μ K.toFun S ω =
      ∑ k ∈ T, ∑ l ∈ T, S7FCH1_mat (wickCoeff μ K.toFun) S k l *
        (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
          ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P) := by
  refine Eq.trans ?_ (S7FCH1_split (wickCoeff μ K.toFun)
    (fun k l => NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
      ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P) S T h).symm
  simp only [wickSection, S7FCH1_F, Finset.mul_sum]

/-- The difference of two Wick sections is in `L²`. -/
theorem S7FCH1_wS_memLp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (K : FRKernel d) (K' : ℝ) (hK : ModeCovBound P η K') (S T : Finset (NonzeroLattice d)) (h : S ⊆ T) :
    MemLp (fun ω => wickSection P η μ K.toFun T ω - wickSection P η μ K.toFun S ω) 2 P := by
  have hm := S7FCH1_wick_T η hG K' hK T (S7FCH1_mat (wickCoeff μ K.toFun) S)
  have hae : (fun ω => ∑ k ∈ T, ∑ l ∈ T, S7FCH1_mat (wickCoeff μ K.toFun) S k l *
        (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
          ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P)) =ᵐ[P]
      (fun ω => wickSection P η μ K.toFun T ω - wickSection P η μ K.toFun S ω) :=
    ae_of_all _ fun ω => (S7FCH1_wS_diff η μ K S T h ω).symm
  exact MemLp.ae_eq hae hm.1

/-- The `L²` bound for the difference of two Wick sections (Wick variance bound on `T`). -/
theorem S7FCH1_wS_L2 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (K : FRKernel d) (K' : ℝ) (hK : ModeCovBound P η K') (S T : Finset (NonzeroLattice d)) (h : S ⊆ T) :
    ∫⁻ ω, ‖wickSection P η μ K.toFun T ω - wickSection P η μ K.toFun S ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((1 / 2) * K' ^ 2 * tailHS (wickCoeff μ K.toFun) S) := by
  have hm := S7FCH1_wick_T η hG K' hK T (S7FCH1_mat (wickCoeff μ K.toFun) S)
  have hmem := S7FCH1_wS_memLp η hG μ K K' hK S T h
  have hint : Integrable (fun ω => (wickSection P η μ K.toFun T ω - wickSection P η μ K.toFun S ω) ^ 2) P :=
    hmem.integrable_sq
  rw [S7FCH1_lintegral_sq P _ hint]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : ∫ ω, (wickSection P η μ K.toFun T ω - wickSection P η μ K.toFun S ω) ^ 2 ∂P =
      ∫ ω, (∑ k ∈ T, ∑ l ∈ T, S7FCH1_mat (wickCoeff μ K.toFun) S k l *
        (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
          ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P)) ^ 2 ∂P :=
    integral_congr_ae (ae_of_all _ fun ω => by simp only [S7FCH1_wS_diff (P := P) η μ K S T h ω])
  rw [e]
  refine hm.2.trans ?_
  have hmat := S7FCH1_mat_sq_le (wickCoeff μ K.toFun) (S7FCH1_hs μ K) S T
  have hK2 : (0 : ℝ) ≤ 2 * K' ^ 2 := by positivity
  linarith [mul_le_mul_of_nonneg_left hmat hK2]

/-! ### Finite-rank expansion of `Y_T` -/

/-- Swapping the finite sums of a four-fold array (`Fintype` indices for the kernel, `T` for the modes). -/
theorem S7FCH1_swap4 {α β : Type} [Fintype α] (T : Finset β) (G : α → α → β → β → ℝ) :
    ∑ k ∈ T, ∑ l ∈ T, ∑ i, ∑ j, G i j k l = ∑ i, ∑ j, ∑ k ∈ T, ∑ l ∈ T, G i j k l := by
  have h1 : ∀ i, ∑ k ∈ T, ∑ l ∈ T, ∑ j, G i j k l = ∑ j, ∑ k ∈ T, ∑ l ∈ T, G i j k l := fun i => by
    calc ∑ k ∈ T, ∑ l ∈ T, ∑ j, G i j k l
        = ∑ k ∈ T, ∑ j, ∑ l ∈ T, G i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ j, ∑ k ∈ T, ∑ l ∈ T, G i j k l := Finset.sum_comm
  calc ∑ k ∈ T, ∑ l ∈ T, ∑ i, ∑ j, G i j k l
      = ∑ k ∈ T, ∑ i, ∑ l ∈ T, ∑ j, G i j k l := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ i, ∑ k ∈ T, ∑ l ∈ T, ∑ j, G i j k l := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ k ∈ T, ∑ l ∈ T, G i j k l := Finset.sum_congr rfl fun i _ => h1 i

/-- The partial sums `part_i(T) = ∑_{k∈T} f̂_i(k) η̂_k` expand the Wick quadratic form. -/
theorem S7FCH1_Y_eq_part {Ω : Type} {r : ℝ} (η : Ω → NegSobolev d r) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (K : FRKernel d) (T : Finset (NonzeroLattice d)) (ω : Ω) :
    S7FCH1_Y η μ K T ω = (1 / 2) * ∑ i, ∑ j, K.c i j *
      (S7FCH1_part η T (K.f i) ω * S7FCH1_part η T (K.f j) ω) := by
  have e1 : ∀ k l : NonzeroLattice d, wickCoeff μ K.toFun k l *
      (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l) =
      ∑ i, ∑ j, K.c i j * ((Torus.funRealCoeff (K.f i) k * NegSobolev.fourierCoeff (η ω) k) *
        (Torus.funRealCoeff (K.f j) l * NegSobolev.fourierCoeff (η ω) l)) := by
    intro k l
    rw [S7FCH1_wick_eq μ K k l, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∀ i j : Fin K.n, S7FCH1_part η T (K.f i) ω * S7FCH1_part η T (K.f j) ω =
      ∑ k ∈ T, ∑ l ∈ T, (Torus.funRealCoeff (K.f i) k * NegSobolev.fourierCoeff (η ω) k) *
        (Torus.funRealCoeff (K.f j) l * NegSobolev.fourierCoeff (η ω) l) := by
    intro i j
    unfold S7FCH1_part
    rw [Finset.sum_mul_sum]
  unfold S7FCH1_Y
  congr 1
  simp only [e1, e2, Finset.mul_sum]
  exact S7FCH1_swap4 T (fun i j k l => K.c i j * ((Torus.funRealCoeff (K.f i) k *
    NegSobolev.fourierCoeff (η ω) k) * (Torus.funRealCoeff (K.f j) l * NegSobolev.fourierCoeff (η ω) l)))

/-- Pointwise convergence of `Y_{N n}(ω)` to `K.quad (η ω)` along an exhausting sequence. -/
theorem S7FCH1_Y_tendsto {Ω : Type} {r : ℝ} (η : Ω → NegSobolev d r) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (K : FRKernel d) (ω : Ω) (N : ℕ → Finset (NonzeroLattice d))
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => S7FCH1_Y η μ K (N n) ω) atTop (𝓝 (K.quad (η ω))) := by
  have hpt : ∀ i : Fin K.n, Tendsto (fun n => S7FCH1_part η (N n) (K.f i) ω) atTop
      (𝓝 (NegSobolev.eval (η ω) (K.f i))) :=
    fun i => S7FCH1_part_tendsto η ω (K.smooth i) N hN
  have hsum : Tendsto (fun n => ∑ i, ∑ j, K.c i j * (S7FCH1_part η (N n) (K.f i) ω *
      S7FCH1_part η (N n) (K.f j) ω)) atTop
      (𝓝 (∑ i, ∑ j, K.c i j * (NegSobolev.eval (η ω) (K.f i) * NegSobolev.eval (η ω) (K.f j)))) :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ((hpt i).mul (hpt j)).const_mul (K.c i j)
  have e : K.quad (η ω) = (1 / 2) * ∑ i, ∑ j, K.c i j *
      (NegSobolev.eval (η ω) (K.f i) * NegSobolev.eval (η ω) (K.f j)) := rfl
  rw [e]
  simp only [S7FCH1_Y_eq_part]
  exact hsum.const_mul (1 / 2)

/-! ### `L²` convergence of the partial sums of a test pairing -/

/-- The pairing `eval (η ω) f` is in `L²`. -/
theorem S7FCH1_eval_memLp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (K' : ℝ) (hK : ModeCovBound P η K')
    (hK0 : 0 ≤ K') {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (N : ℕ → Finset (NonzeroLattice d))
    (hN : Tendsto N atTop atTop) :
    MemLp (fun ω => NegSobolev.eval (η ω) f) 2 P := by
  have hxm : AEStronglyMeasurable (fun ω => NegSobolev.eval (η ω) f - S7FCH1_part η ∅ f ω) P :=
    (S7FCH1_eval_aesm hG hf N hN).sub (S7FCH1_part_aesm hG ∅ f)
  have hx := S7FCH1_fatou P η hG K' hK hK0 N hN ∅ f hf
  obtain ⟨hmem, -⟩ := S7FCH1_memLp_of_lintegral P hxm (mul_nonneg hK0 (S7FCH1_tailW_nonneg f ∅)) hx
  have h0 : MemLp (fun ω => S7FCH1_part η ∅ f ω) 2 P := S7FCH1_part_memLp hG ∅ f
  exact MemLp.ae_eq (ae_of_all _ fun ω => by simp) (hmem.add h0)

/-- `L²` convergence of the partial sums `part_T f → eval f` along an exhausting sequence. -/
theorem S7FCH1_part_L2tail {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (K' : ℝ) (hK : ModeCovBound P η K')
    (hK0 : 0 ≤ K') {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (N : ℕ → Finset (NonzeroLattice d))
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => ∫ ω, (S7FCH1_part η (N n) f ω - NegSobolev.eval (η ω) f) ^ 2 ∂P) atTop (𝓝 0) := by
  have hb : ∀ T : Finset (NonzeroLattice d),
      ∫ ω, (S7FCH1_part η T f ω - NegSobolev.eval (η ω) f) ^ 2 ∂P ≤ K' * S7FCH1_tailW f T := by
    intro T
    have hxm : AEStronglyMeasurable (fun ω => NegSobolev.eval (η ω) f - S7FCH1_part η T f ω) P :=
      (S7FCH1_eval_aesm hG hf N hN).sub (S7FCH1_part_aesm hG T f)
    have hx := S7FCH1_fatou P η hG K' hK hK0 N hN T f hf
    obtain ⟨-, hle⟩ := S7FCH1_memLp_of_lintegral P hxm (mul_nonneg hK0 (S7FCH1_tailW_nonneg f T)) hx
    have e : ∫ ω, (S7FCH1_part η T f ω - NegSobolev.eval (η ω) f) ^ 2 ∂P =
        ∫ ω, (NegSobolev.eval (η ω) f - S7FCH1_part η T f ω) ^ 2 ∂P :=
      integral_congr_ae (ae_of_all _ fun ω => by ring)
    rw [e]
    exact hle
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n => integral_nonneg fun ω => sq_nonneg _) (fun n => hb (N n))
  have h := (S7FCH1_tailW_tendsto hf N hN).const_mul K'
  rw [mul_zero] at h
  exact h

/-- Expectations of the Wick quadratic forms converge to the expectation of `K.quad (η)`. -/
theorem S7FCH1_expect {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (K : FRKernel d) (K' : ℝ) (hK : ModeCovBound P η K') (N : ℕ → Finset (NonzeroLattice d))
    (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => ∫ ω, S7FCH1_Y η μ K (N n) ω ∂P) atTop (𝓝 (∫ ω, K.quad (η ω) ∂P)) := by
  have hK2 := S7FCH1_mcb_max P η K' hK
  have hK0 : (0 : ℝ) ≤ max K' 0 := le_max_right _ _
  have hI : ∀ (T : Finset (NonzeroLattice d)) (i j : Fin K.n),
      Integrable (fun ω => S7FCH1_part η T (K.f i) ω * S7FCH1_part η T (K.f j) ω) P :=
    fun T i j => (S7FCH1_part_memLp hG T (K.f i)).integrable_mul (S7FCH1_part_memLp hG T (K.f j))
  have hIe : ∀ i j : Fin K.n,
      Integrable (fun ω => NegSobolev.eval (η ω) (K.f i) * NegSobolev.eval (η ω) (K.f j)) P :=
    fun i j => (S7FCH1_eval_memLp η hG (max K' 0) hK2 hK0 (K.smooth i) N hN).integrable_mul
      (S7FCH1_eval_memLp η hG (max K' 0) hK2 hK0 (K.smooth j) N hN)
  have hY : ∀ T : Finset (NonzeroLattice d), ∫ ω, S7FCH1_Y η μ K T ω ∂P =
      (1 / 2) * ∑ i, ∑ j, K.c i j *
        ∫ ω, S7FCH1_part η T (K.f i) ω * S7FCH1_part η T (K.f j) ω ∂P := by
    intro T
    have e : (fun ω => S7FCH1_Y η μ K T ω) = fun ω => (1 / 2) * ∑ i, ∑ j, K.c i j *
        (S7FCH1_part η T (K.f i) ω * S7FCH1_part η T (K.f j) ω) :=
      funext fun ω => S7FCH1_Y_eq_part η μ K T ω
    rw [e, integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hI T i j).const_mul (K.c i j)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hI T i j).const_mul (K.c i j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hQ : ∫ ω, K.quad (η ω) ∂P = (1 / 2) * ∑ i, ∑ j, K.c i j *
      ∫ ω, NegSobolev.eval (η ω) (K.f i) * NegSobolev.eval (η ω) (K.f j) ∂P := by
    have e : (fun ω => K.quad (η ω)) = fun ω => (1 / 2) * ∑ i, ∑ j, K.c i j *
        (NegSobolev.eval (η ω) (K.f i) * NegSobolev.eval (η ω) (K.f j)) := rfl
    rw [e, integral_const_mul, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hIe i j).const_mul (K.c i j)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hIe i j).const_mul (K.c i j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  have hpair : ∀ i j : Fin K.n, Tendsto (fun n => ∫ ω,
      S7FCH1_part η (N n) (K.f i) ω * S7FCH1_part η (N n) (K.f j) ω ∂P) atTop
      (𝓝 (∫ ω, NegSobolev.eval (η ω) (K.f i) * NegSobolev.eval (η ω) (K.f j) ∂P)) :=
    fun i j => S7FCH1_prod_lim P (fun n ω => S7FCH1_part η (N n) (K.f i) ω)
      (fun n ω => S7FCH1_part η (N n) (K.f j) ω) (fun ω => NegSobolev.eval (η ω) (K.f i))
      (fun ω => NegSobolev.eval (η ω) (K.f j)) (fun n => S7FCH1_part_memLp hG (N n) (K.f i))
      (fun n => S7FCH1_part_memLp hG (N n) (K.f j))
      (S7FCH1_eval_memLp η hG (max K' 0) hK2 hK0 (K.smooth i) N hN)
      (S7FCH1_eval_memLp η hG (max K' 0) hK2 hK0 (K.smooth j) N hN)
      (S7FCH1_part_L2tail η hG (max K' 0) hK2 hK0 (K.smooth i) N hN)
      (S7FCH1_part_L2tail η hG (max K' 0) hK2 hK0 (K.smooth j) N hN)
  rw [hQ]
  simp only [hY]
  exact (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
    (hpair i j).const_mul (K.c i j)).const_mul (1 / 2)

/-! ### Fatou and the conclusion -/

/-- Fatou bound for the Wick section of `Q` at a finite set `S`. -/
theorem S7FCH1_wS_fatou {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (K : FRKernel d) (K' : ℝ) (hK : ModeCovBound P η K') (S : Finset (NonzeroLattice d)) :
    ∫⁻ ω, ‖(K.quad (η ω) - ∫ ω', K.quad (η ω') ∂P) - wickSection P η μ K.toFun S ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((1 / 2) * K' ^ 2 * tailHS (wickCoeff μ K.toFun) S) := by
  obtain ⟨N, hN⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset (NonzeroLattice d)))
  have hN' : Tendsto (fun n => N n ∪ S) atTop atTop :=
    tendsto_atTop_mono (fun n => Finset.subset_union_left) hN
  have hpt : ∀ ω, Tendsto (fun n => wickSection P η μ K.toFun (N n ∪ S) ω) atTop
      (𝓝 (K.quad (η ω) - ∫ ω', K.quad (η ω') ∂P)) := by
    intro ω
    have e : (fun n => wickSection P η μ K.toFun (N n ∪ S) ω) =
        fun n => S7FCH1_Y η μ K (N n ∪ S) ω - ∫ ω', S7FCH1_Y η μ K (N n ∪ S) ω' ∂P :=
      funext fun n => S7FCH1_wS_eq_Y η hG μ K (N n ∪ S) ω
    rw [e]
    exact (S7FCH1_Y_tendsto η μ K ω (fun n => N n ∪ S) hN').sub
      (S7FCH1_expect η hG μ K K' hK (fun n => N n ∪ S) hN')
  have hZ : ∀ ω, Tendsto (fun n => ‖wickSection P η μ K.toFun (N n ∪ S) ω -
      wickSection P η μ K.toFun S ω‖ₑ ^ 2) atTop
      (𝓝 (‖(K.quad (η ω) - ∫ ω', K.quad (η ω') ∂P) - wickSection P η μ K.toFun S ω‖ₑ ^ 2)) := by
    intro ω
    have h1 := (hpt ω).sub_const (wickSection P η μ K.toFun S ω)
    exact ((ENNReal.continuous_pow 2).tendsto _).comp h1.enorm
  have hmeas : ∀ n, AEMeasurable (fun ω => ‖wickSection P η μ K.toFun (N n ∪ S) ω -
      wickSection P η μ K.toFun S ω‖ₑ ^ 2) P := fun n =>
    ((S7FCH1_wS_memLp η hG μ K K' hK S (N n ∪ S) Finset.subset_union_right).aestronglyMeasurable.aemeasurable.enorm).pow_const 2
  have hbound : ∀ n, ∫⁻ ω, ‖wickSection P η μ K.toFun (N n ∪ S) ω -
      wickSection P η μ K.toFun S ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((1 / 2) * K' ^ 2 * tailHS (wickCoeff μ K.toFun) S) := fun n =>
    S7FCH1_wS_L2 η hG μ K K' hK S (N n ∪ S) Finset.subset_union_right
  refine (lintegral_congr fun ω => ((hZ ω).liminf_eq).symm).trans_le ?_
  refine (lintegral_liminf_le' hmeas).trans ?_
  exact liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently

/-- The Gaussian side: `Q` is the `L²`-limit of the Wick sections along finite sets. -/
theorem S7FCH1_halfwick {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (η : Ω → NegSobolev d r) (hG : HasFiniteGaussianCoeffs P η) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (K : FRKernel d) (K' : ℝ) (hK : ModeCovBound P η K') :
    Tendsto (fun S : Finset (NonzeroLattice d) => ∫⁻ ω,
      ‖(K.quad (η ω) - ∫ ω', K.quad (η ω') ∂P) - wickSection P η μ K.toFun S ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hT : Tendsto (fun S : Finset (NonzeroLattice d) =>
      ENNReal.ofReal ((1 / 2) * K' ^ 2 * tailHS (wickCoeff μ K.toFun) S)) atTop
      (𝓝 (ENNReal.ofReal ((1 / 2) * K' ^ 2 * 0))) :=
    ENNReal.tendsto_ofReal ((S7FCH1_tailHS_tendsto (wickCoeff μ K.toFun) (S7FCH1_hs μ K)).const_mul
      ((1 / 2) * K' ^ 2))
  rw [mul_zero, ENNReal.ofReal_zero] at hT
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun S => zero_le) (Eventually.of_forall fun S => S7FCH1_wS_fatou η hG μ K K' hK S)

/-- **H1b (Gaussian side of a finite-rank field)**: the half-Wick chaos of the finite-rank kernel is the
`L²`-limit of the centred Wick sections, i.e. `IsHalfWick` for `Φ_K(η) - E Φ_K(η)`. -/
theorem s7_FC_H1b_gauss_proof {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (r : ℝ)
    (η : Ω → NegSobolev d r) (K' : ℝ) (hG : HasFiniteGaussianCoeffs P η) (hK : ModeCovBound P η K')
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (K : FRKernel d) :
    IsHalfWick P η μ K.toFun (fun ω => K.quad (η ω) - ∫ ω', K.quad (η ω') ∂P) := by
  unfold IsHalfWick
  exact S7FCH1_halfwick η hG μ K K' hK

end HRS.MC.Sec7.S7FCH1

end
