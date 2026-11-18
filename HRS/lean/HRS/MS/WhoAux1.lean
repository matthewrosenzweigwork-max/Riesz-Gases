import HRS.MS.UlClass
import HRS.MS.UlTail
import HRS.Whole.Orbits
import HRS.MP.RdInit

/-!
# S54 (S5.4 `weighted_higher_order`), part 1: the weighted square integral and its calculus

Plan and verdict (file docstring of the packet; scratch copy `S54_PLAN.md`).  Names carry the prefix `who_`, namespace `HRS.MS.Who`.

Verdict on the frozen statement `HRS.Whole.weighted_higher_order`: TRUE and non-vacuous (checked clause by clause: the integrals involve
only functions with bounded derivatives, `⟨x⟩^{-2P}` is integrable for `P > d/2`, the Riesz kernel is locally integrable because
`s + 1 < d`, `IsLinearFlow` forces the matrix exponential).  `k₀ = ⌊4 + d/2⌋ + 1`.

Route and files (in dependency order):
* `WhoAux1`: `wt`, `wSq` (squared weighted `L²` norm), Peetre, translation, linear change of variables, `Nsq` (operator-norm version of
  `weightedSobolevE`; `Esq ≤ d^r Nsq`, `Nsq ≤ d^r Esq`).
* `WhoAux2`: Gaussian averages `ouSg` in the weighted norm (`who_W1`), with one derivative moved onto the Gaussian by Stein's identity
  (`who_W2`, cost `η⁻¹`).
* `WhoAux3`, `WhoAux4`: the cancellation convolution `ultK` (Riesz kernel) in the weighted norm: near part by Young, far part by `L¹`; decay
  classes, weighted Leibniz and `L¹` bounds.
* `WhoAux5`, `WhoAux6`: the perturbation `ulPert = c·∇ - N` splits as `∑ ∂_k G_k + G_0` with zeroth order operators; their weighted bounds.
* `WhoAux7`: sup bound of `ulPert`, weighted bound of `ouSg (ulPert φ)` with the singular cost `1 + η⁻¹`.
* `WhoAux8`: differentiation under the time integral, the weighted bound of the Duhamel integral `who_Vw`.
* `WhoAux9`: weakly singular Gronwall lemma (no project dependency).
* `WhoAux10`: the a priori bound `who_core` for an evolution of large level (mild identity of the merged chain `ul5_mild_of_evolution`).
* `WhoAux11`: clause (c), the local Sobolev embedding in `E_{r,P}`.
* `WhoAux12`: clause (b), the generator conjugated by the flow.
* `WhoTie`: `weighted_higher_order_proof` with the `type_of%` tie (level raising: existence at a large level, `ul6_mono_level`,
  uniqueness `ul_evolution_unique`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Who

open HRS HRS.Whole

variable {d : ℕ}

/-- the weight `⟨x⟩^{-2P}` -/
def wt (P : ℝ) (x : Euc d) : ℝ := jbracket x ^ (-2 * P)

/-- the squared weighted `L²` norm `∫⁻ ⟨x⟩^{-2P} G(x)²` -/
def wSq (P : ℝ) (G : Euc d → ℝ) : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (wt P x * G x ^ 2)

theorem who_jb_sq (x : Euc d) : jbracket x ^ 2 = 1 + ‖x‖ ^ 2 := by
  unfold jbracket
  rw [Real.sq_sqrt (by positivity)]

theorem who_jb_pos (x : Euc d) : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)

theorem who_one_le_jb (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg ‖x‖]

theorem who_wt_pos (P : ℝ) (x : Euc d) : 0 < wt P x := Real.rpow_pos_of_pos (who_jb_pos x) _

theorem who_wt_le_one {P : ℝ} (hP : 0 ≤ P) (x : Euc d) : wt P x ≤ 1 := by
  unfold wt
  apply Real.rpow_le_one_of_one_le_of_nonpos (who_one_le_jb x)
  linarith

theorem who_wt_meas (P : ℝ) : Measurable (wt (d := d) P) := by
  unfold wt jbracket
  fun_prop

theorem who_wSq_meas {P : ℝ} {G : Euc d → ℝ} (hG : Measurable G) :
    Measurable fun x => ENNReal.ofReal (wt P x * G x ^ 2) :=
  ENNReal.measurable_ofReal.comp (((who_wt_meas P).mul (hG.pow_const 2)))

/-- `⟨x⟩^{-2P}` is integrable for `P > d/2` -/
theorem who_wt_integrable {P : ℝ} (hP : (d : ℝ) / 2 < P) : Integrable (wt (d := d) P) volume := by
  have h1 : Integrable (fun x : Euc d => (1 + ‖x‖) ^ (-(2 * P))) volume := by
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace_fin]; linarith
  refine (h1.const_mul (2 ^ P)).mono' (who_wt_meas P).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hx : 0 < 1 + ‖x‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_pos (who_wt_pos P x)]
  have e1 : wt P x = (1 + ‖x‖ ^ 2) ^ (-P) := by
    unfold wt
    rw [show -2 * P = (2 : ℕ) * (-P) by push_cast; ring, Real.rpow_mul (who_jb_pos x).le,
      Real.rpow_natCast, who_jb_sq]
  have e2 : (1 + ‖x‖) ^ (-(2 * P)) = ((1 + ‖x‖) ^ 2) ^ (-P) := by
    rw [show -(2 * P) = (2 : ℕ) * (-P) by push_cast; ring, Real.rpow_mul hx.le, Real.rpow_natCast]
  have hle : ((1 + ‖x‖) ^ 2 / 2) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (1 - ‖x‖)]
  have hpos : 0 < (1 + ‖x‖) ^ 2 / 2 := by positivity
  rw [e1, e2]
  have h3 := Real.rpow_le_rpow_of_nonpos hpos hle (show -P ≤ 0 by linarith [show (0:ℝ) ≤ (d:ℝ)/2 by positivity])
  rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), div_eq_mul_inv, inv_inv] at h3
  linarith


/-! ### Calculus of `wSq` -/

theorem who_wSq_mono {P : ℝ} {G H : Euc d → ℝ} (h : ∀ x, G x ^ 2 ≤ H x ^ 2) : wSq P G ≤ wSq P H :=
  lintegral_mono fun x => ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (h x) (who_wt_pos P x).le)

theorem who_wSq_smul (P a : ℝ) (G : Euc d → ℝ) :
    wSq P (fun x => a * G x) = ENNReal.ofReal (a ^ 2) * wSq P G := by
  unfold wSq
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun x => ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1; ring

theorem who_wSq_zero (P : ℝ) : wSq (d := d) P (fun _ => 0) = 0 := by
  unfold wSq; simp

theorem who_wSq_add_le {P : ℝ} {G H : Euc d → ℝ} (hG : Measurable G) :
    wSq P (fun x => G x + H x) ≤ 2 * (wSq P G + wSq P H) := by
  unfold wSq
  rw [← lintegral_add_left (who_wSq_meas hG), ← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_mono fun x => ?_
  rw [mul_add, ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by have := who_wt_pos P x; positivity) (by have := who_wt_pos P x; positivity)]
  apply ENNReal.ofReal_le_ofReal
  have := who_wt_pos P x
  nlinarith [sq_nonneg (G x - H x), mul_nonneg this.le (sq_nonneg (G x - H x))]

theorem who_wSq_sum_le {ι : Type*} (S : Finset ι) {P : ℝ} {G : ι → Euc d → ℝ}
    (hG : ∀ i, Measurable (G i)) :
    wSq P (fun x => ∑ i ∈ S, G i x) ≤ (S.card : ℝ≥0∞) * ∑ i ∈ S, wSq P (G i) := by
  unfold wSq
  rw [← lintegral_finsetSum _ (fun i _ => who_wSq_meas (hG i)), ← lintegral_const_mul' _ _
    (ENNReal.natCast_ne_top _)]
  refine lintegral_mono fun x => ?_
  have hw := who_wt_pos P x
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [← Finset.mul_sum]
  have := sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => G i x)
  nlinarith [this]


theorem who_wt_eq (P : ℝ) (x : Euc d) : wt P x = (1 + ‖x‖ ^ 2) ^ (-P) := by
  unfold wt
  rw [show -2 * P = (2 : ℕ) * (-P) by push_cast; ring, Real.rpow_mul (who_jb_pos x).le,
    Real.rpow_natCast, who_jb_sq]

/-- Peetre's inequality for the weight -/
theorem who_peetre {P : ℝ} (hP : 0 ≤ P) (x z : Euc d) :
    wt P x ≤ 2 ^ P * jbracket z ^ (2 * P) * wt P (x - z) := by
  have h1 : (1 + ‖x - z‖ ^ 2) / (2 * (1 + ‖z‖ ^ 2)) ≤ 1 + ‖x‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have := norm_sub_le x z
    have h0 := norm_nonneg x
    have h0' := norm_nonneg z
    have : ‖x - z‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
      nlinarith [norm_sub_le x z, norm_nonneg (x - z), sq_nonneg (‖x‖ - ‖z‖)]
    nlinarith [mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖z‖)]
  have hpos : 0 < (1 + ‖x - z‖ ^ 2) / (2 * (1 + ‖z‖ ^ 2)) := by positivity
  have h2 := Real.rpow_le_rpow_of_nonpos hpos h1 (show -P ≤ 0 by linarith)
  rw [who_wt_eq, who_wt_eq]
  refine h2.trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 2 * (1 + ‖z‖ ^ 2)),
    div_eq_mul_inv, inv_inv, Real.mul_rpow (by norm_num) (by positivity)]
  have : jbracket z ^ (2 * P) = (1 + ‖z‖ ^ 2) ^ P := by
    rw [show 2 * P = (2 : ℕ) * P by push_cast; ring, Real.rpow_mul (who_jb_pos z).le, Real.rpow_natCast,
      who_jb_sq]
  rw [this]; ring

/-- translation -/
theorem who_wSq_shift {P : ℝ} (hP : 0 ≤ P) (G : Euc d → ℝ) (z : Euc d) :
    wSq P (fun x => G (x - z)) ≤ ENNReal.ofReal (2 ^ P * jbracket z ^ (2 * P)) * wSq P G := by
  unfold wSq
  have hc : 0 ≤ 2 ^ P * jbracket z ^ (2 * P) := by have := who_jb_pos z; positivity
  calc ∫⁻ x, ENNReal.ofReal (wt P x * G (x - z) ^ 2)
      ≤ ∫⁻ x, ENNReal.ofReal (2 ^ P * jbracket z ^ (2 * P)) * ENNReal.ofReal (wt P (x - z) * G (x - z) ^ 2) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hc]
        apply ENNReal.ofReal_le_ofReal
        have := who_peetre hP x z
        have h0 : 0 ≤ G (x - z) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right this h0]
    _ = ENNReal.ofReal (2 ^ P * jbracket z ^ (2 * P)) * ∫⁻ x, ENNReal.ofReal (wt P x * G x ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (wt P y * G y ^ 2)) z


theorem who_wt_comp_le {P : ℝ} (hP : 0 ≤ P) (E : Euc d →L[ℝ] Euc d) (x : Euc d) :
    wt P x ≤ (1 + ‖E‖) ^ (2 * P) * wt P (E x) := by
  have h1 : (1 + ‖E x‖ ^ 2) / (1 + ‖E‖) ^ 2 ≤ 1 + ‖x‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h2 : ‖E x‖ ≤ ‖E‖ * ‖x‖ := E.le_opNorm x
    have h3 : ‖E x‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖x‖ ^ 2 := by
      calc ‖E x‖ ^ 2 ≤ (‖E‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
        _ = _ := by ring
    nlinarith [norm_nonneg E, sq_nonneg ‖x‖, mul_nonneg (norm_nonneg E) (sq_nonneg ‖x‖)]
  have hpos : 0 < (1 + ‖E x‖ ^ 2) / (1 + ‖E‖) ^ 2 := by positivity
  have h2 := Real.rpow_le_rpow_of_nonpos hpos h1 (show -P ≤ 0 by linarith)
  rw [who_wt_eq, who_wt_eq]
  refine h2.trans (le_of_eq ?_)
  rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ (1 + ‖E‖) ^ 2),
    div_eq_mul_inv, inv_inv, show 2 * P = (2 : ℕ) * P by push_cast; ring, Real.rpow_mul (by positivity),
    Real.rpow_natCast]
  ring

/-- composition with a linear map of nonzero determinant -/
theorem who_wSq_comp_linear {P : ℝ} (hP : 0 ≤ P) (E : Euc d →L[ℝ] Euc d)
    (hE : LinearMap.det (E : Euc d →ₗ[ℝ] Euc d) ≠ 0) {G : Euc d → ℝ} (hG : Measurable G) :
    wSq P (fun x => G (E x)) ≤
      ENNReal.ofReal ((1 + ‖E‖) ^ (2 * P) * |(LinearMap.det (E : Euc d →ₗ[ℝ] Euc d))⁻¹|) * wSq P G := by
  unfold wSq
  have hc : 0 ≤ (1 + ‖E‖) ^ (2 * P) := by positivity
  calc ∫⁻ x, ENNReal.ofReal (wt P x * G (E x) ^ 2)
      ≤ ∫⁻ x, ENNReal.ofReal ((1 + ‖E‖) ^ (2 * P)) *
          (fun y => ENNReal.ofReal (wt P y * G y ^ 2)) (E x) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hc]
        apply ENNReal.ofReal_le_ofReal
        have := who_wt_comp_le hP E x
        have h0 : 0 ≤ G (E x) ^ 2 := sq_nonneg _
        nlinarith [mul_le_mul_of_nonneg_right this h0]
    _ = ENNReal.ofReal ((1 + ‖E‖) ^ (2 * P)) * ∫⁻ y, ENNReal.ofReal (wt P y * G y ^ 2)
          ∂(Measure.map E volume) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        rw [lintegral_map (who_wSq_meas hG) E.continuous.measurable]
    _ = _ := by
        have hmap : Measure.map E (volume : Measure (Euc d)) =
            ENNReal.ofReal |(LinearMap.det (E : Euc d →ₗ[ℝ] Euc d))⁻¹| • volume :=
          Measure.map_linearMap_addHaar_eq_smul_addHaar volume hE
        rw [hmap, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_mul hc]


/-! ### The Sobolev-type quantities -/

/-- `∑_{j ≤ r} ∫ ⟨x⟩^{-2P} ‖D^j f‖²` (operator norms) -/
def Nsq (r : ℕ) (P : ℝ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (r + 1), wSq P (fun x => ‖iteratedFDeriv ℝ j f x‖)

/-- the tuple version: `weightedSobolevE r P f = (Esq r P f)^{1/2}` -/
def Esq (r : ℕ) (P : ℝ) (f : Euc d → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d,
    ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)

theorem who_E_eq (r : ℕ) (P : ℝ) (f : Euc d → ℝ) : weightedSobolevE r P f = (Esq r P f) ^ (1 / 2 : ℝ) := rfl

theorem who_iter_meas {r : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ r f) {j : ℕ} (hj : j ≤ r) :
    Measurable fun x => ‖iteratedFDeriv ℝ j f x‖ :=
  (hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm.measurable

theorem who_pd_meas {r : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ r f) {j : ℕ} (hj : j ≤ r)
    (i : Fin j → Fin d) : Measurable fun x => partialDeriv i f x := by
  unfold partialDeriv
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Euc d) ℝ
    (fun l => EuclideanSpace.single (i l) (1 : ℝ))).continuous.comp
      (hf.continuous_iteratedFDeriv (by exact_mod_cast hj))).measurable

theorem who_Esq_le (hd : 1 ≤ d) {r : ℕ} {P : ℝ} {f : Euc d → ℝ} :
    Esq r P f ≤ ((d : ℝ≥0∞) ^ r) * Nsq r P f := by
  unfold Esq Nsq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  calc ∑ i : Fin j → Fin d, ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2)
      ≤ ∑ i : Fin j → Fin d, wSq P (fun x => ‖iteratedFDeriv ℝ j f x‖) := by
        refine Finset.sum_le_sum fun i _ => who_wSq_mono fun x => ?_
        have := HRS.MP.RdInit.mri_abs_partialDeriv_le i f x
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = (d : ℝ≥0∞) ^ j * wSq P (fun x => ‖iteratedFDeriv ℝ j f x‖) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ (d : ℝ≥0∞) ^ r * wSq P (fun x => ‖iteratedFDeriv ℝ j f x‖) := by
        gcongr
        exact Nat.one_le_cast.2 hd


theorem who_Nsq_le (hd : 1 ≤ d) {r : ℕ} {P : ℝ} {f : Euc d → ℝ} (hf : ContDiff ℝ r f) :
    Nsq r P f ≤ ((d : ℝ≥0∞) ^ r) * Esq r P f := by
  unfold Esq Nsq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  calc wSq P (fun x => ‖iteratedFDeriv ℝ j f x‖)
      ≤ ∫⁻ x, (d : ℝ≥0∞) ^ j * ∑ i : Fin j → Fin d,
          ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) := by
        refine lintegral_mono fun x => ?_
        have hw := who_wt_pos P x
        have h1 := HRS.MP.RdInit.mri_norm_iter_sq j f x
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by have : wt P x = jbracket x ^ (-2 * P) := rfl
                                                          rw [← this]; positivity),
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        rw [← Finset.mul_sum]
        have : wt P x = jbracket x ^ (-2 * P) := rfl
        rw [this] at hw ⊢
        nlinarith [mul_le_mul_of_nonneg_left h1 hw.le]
    _ = (d : ℝ≥0∞) ^ j * ∑ i : Fin j → Fin d,
          ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)),
          lintegral_finsetSum]
        intro i _
        exact who_wSq_meas (P := P) (who_pd_meas hf hjr i)
    _ ≤ (d : ℝ≥0∞) ^ r * ∑ i : Fin j → Fin d,
          ∫⁻ x, ENNReal.ofReal (jbracket x ^ (-2 * P) * (partialDeriv i f x) ^ 2) := by
        gcongr
        exact Nat.one_le_cast.2 hd


/-- total mass of the weight -/
def wtMass (P : ℝ) : ℝ≥0∞ := ∫⁻ x : Euc d, ENNReal.ofReal (wt P x)

theorem who_wtMass_lt_top {P : ℝ} (hP : (d : ℝ) / 2 < P) : wtMass (d := d) P < ⊤ := by
  unfold wtMass
  exact (who_wt_integrable hP).lintegral_lt_top

theorem who_wSq_bdd {P B : ℝ} {G : Euc d → ℝ} (hB : ∀ x, |G x| ≤ B) :
    wSq P G ≤ ENNReal.ofReal (B ^ 2) * wtMass (d := d) P := by
  unfold wSq wtMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have := who_wt_pos P x
  have h2 : G x ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  nlinarith

theorem who_Nsq_lt_top {r : ℕ} {P : ℝ} (hP : (d : ℝ) / 2 < P) {f : Euc d → ℝ}
    (hb : ∀ j ≤ r, ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) : Nsq r P f < ⊤ := by
  unfold Nsq
  refine ENNReal.sum_lt_top.2 fun j hj => ?_
  obtain ⟨B, hB⟩ := hb j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
  refine lt_of_le_of_lt (who_wSq_bdd (B := B) fun x => ?_)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (who_wtMass_lt_top hP))
  rw [abs_of_nonneg (norm_nonneg _)]; exact hB x

end HRS.MS.Who
