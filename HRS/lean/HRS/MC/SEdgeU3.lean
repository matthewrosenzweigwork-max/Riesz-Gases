import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB1
import HRS.MC.SEdgeB4b
import HRS.MC.SEdgeB6
import HRS.MC.SEdgeB7
import HRS.MC.SEdgeB9sym
import HRS.MC.SEdgeB11a
import HRS.MC.SEdgeB11b
import HRS.MC.SEdgeB12
import HRS.MC.SEdgeB13a
import HRS.MC.SEdgeU2

/-!
# Packet U3: equi-Lipschitz continuity of the scaled remainder in `t` (relocated proof of `sed_U3_equilip`)

For `p = 1`, `F_t = cos(t .)` or `sin(t .)`, `f_t` its Stein solution (B11b), the exact decomposition B12 gives
`e_N(t) = sqrt N P_N(t) + beta R_N(t) - (kappa/6) D(t)` with
`P_N(t) = E[(C - A_N) f_t''(W_N)]`, `R_N(t) = E[B_N f_t'(W_N)]`, `D(t) = E D^3 F_t(Z)`.
By U2, `|f_t^{(j)}(x) - f_{t'}^{(j)}(x)| <= K |t - t'| (1 + |x|)` (`j = 1, 2`), hence the `t`-increment of
`e_N` is bounded by `|t - t'|` times `E[|sqrt N (C - A_N)| (1 + |W_N|)]` and `E[|B_N| (1 + |W_N|)]`, which are
bounded uniformly in `N` by B13a/B7/B6 (`L^2`, `L^4` moments of `Y_w`) and B4b (`L^{3/2}` moment of `B_N`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.U3

open HRS.Sec7 HRS.MC.SEdge HRS.MC.SEdge.U2

/-! ### Elementary lemmas -/

lemma u3_norm_E1 (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]; simp [Real.sqrt_sq_eq_abs]

lemma u3_young {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x * y ≤ x ^ (3 / 2 : ℝ) + y ^ 3 := by
  have h32 : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    have : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
    rw [this, Real.rpow_add' hx (by norm_num), Real.rpow_one, Real.sqrt_eq_rpow]
  have hx32 : 0 ≤ x ^ (3 / 2 : ℝ) := Real.rpow_nonneg hx _
  by_cases h : y ≤ Real.sqrt x
  · have : x * y ≤ x * Real.sqrt x := mul_le_mul_of_nonneg_left h hx
    rw [h32]
    nlinarith [pow_nonneg hy 3]
  · have h := not_le.1 h
    have h2 : x ≤ y ^ 2 := by
      have := Real.sq_sqrt hx
      nlinarith [Real.sqrt_nonneg x]
    have : x * y ≤ y ^ 2 * y := mul_le_mul_of_nonneg_right h2 hy
    nlinarith

lemma u3_poly1 (a y w : ℝ) (ha : 0 ≤ a) :
    (a + |y|) * (1 + |w|) ≤ 2 * (a + 1) * (1 + y ^ 2 + w ^ 2) := by
  have h1 : |y| ≤ (1 + y ^ 2) / 2 := by nlinarith [sq_nonneg (|y| - 1), sq_abs y]
  have h2 : |w| ≤ (1 + w ^ 2) / 2 := by nlinarith [sq_nonneg (|w| - 1), sq_abs w]
  have h3 : |y| * |w| ≤ (y ^ 2 + w ^ 2) / 2 := by nlinarith [sq_nonneg (|y| - |w|), sq_abs y, sq_abs w]
  nlinarith [sq_nonneg y, sq_nonneg w, mul_nonneg ha (sq_nonneg y), mul_nonneg ha (sq_nonneg w),
    mul_nonneg ha (abs_nonneg w), abs_nonneg y, abs_nonneg w]

lemma u3_poly2 (w : ℝ) : (1 + |w|) ^ 3 ≤ 8 * (1 + w ^ 4) := by
  have h : |w| ^ 4 = w ^ 4 := by rw [pow_abs]; exact abs_of_nonneg (by positivity)
  nlinarith [sq_nonneg (|w| - 1), sq_nonneg (|w| ^ 2 - 1), abs_nonneg w, sq_abs w,
    mul_nonneg (abs_nonneg w) (sq_nonneg (|w| - 1))]

lemma u3_pow_sub {x y : ℝ} (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    (x - y) ^ (2 * k) ≤ 8 * (x ^ (2 * k) + y ^ (2 * k)) := by
  have h1 : (x - y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x + y)]
  interval_cases k
  · norm_num
    nlinarith [sq_nonneg x, sq_nonneg y]
  · have h2 : ((x - y) ^ 2) ^ 2 ≤ (2 * (x ^ 2 + y ^ 2)) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
    have h3 : (2 * (x ^ 2 + y ^ 2)) ^ 2 ≤ 8 * (x ^ 4 + y ^ 4) := by
      nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
    have h4 : (x - y) ^ 4 = ((x - y) ^ 2) ^ 2 := by ring
    norm_num
    linarith

lemma u3_sqrt_div {N : ℕ} (hN : (0 : ℝ) < N) (C : ℝ) :
    Real.sqrt N * (C / N) = C / Real.sqrt N := by
  have h : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN.le
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  rw [eq_div_iff hs.ne']
  calc Real.sqrt N * (C / N) * Real.sqrt N = C * (Real.sqrt N * Real.sqrt N) / N := by ring
    _ = C := by rw [h]; field_simp

/-- Lipschitz estimate of a weighted difference. -/
lemma u3_lip_int {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {a g g' w : Ω → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hag : Integrable (fun X => a X * g X) Q) (hag' : Integrable (fun X => a X * g' X) Q)
    (hdom : Integrable (fun X => |a X| * (1 + |w X|)) Q)
    (hpt : ∀ X, |g X - g' X| ≤ L * (1 + |w X|)) :
    |∫ X, a X * g X ∂Q - ∫ X, a X * g' X ∂Q| ≤ L * ∫ X, |a X| * (1 + |w X|) ∂Q := by
  rw [← integral_sub hag hag', ← integral_const_mul]
  have := norm_integral_le_of_norm_le (hdom.const_mul L) (μ := Q)
    (f := fun X => a X * g X - a X * g' X) (Filter.Eventually.of_forall fun X => ?_)
  · simpa [Real.norm_eq_abs] using this
  · rw [Real.norm_eq_abs, ← mul_sub, abs_mul]
    calc |a X| * |g X - g' X| ≤ |a X| * (L * (1 + |w X|)) :=
          mul_le_mul_of_nonneg_left (hpt X) (abs_nonneg _)
      _ = L * (|a X| * (1 + |w X|)) := by ring

/-! ### The third-derivative term -/

lemma u3_d3_form (σ : Bool) (t : ℝ) (z : EuclideanSpace ℝ (Fin 1)) :
    iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0] =
      t ^ 3 * iteratedDeriv 3 (u2h σ) (t * z 0) := by
  rw [sed_Ucf_eq, u2_iter_comp (u2P_contDiff (u2h_P σ))]
  have h1 : ∀ i : Fin 3, ![stdVec (0 : Fin 1), stdVec 0, stdVec 0] i 0 = 1 := by
    intro i; fin_cases i <;> simp [stdVec]
  simp only [h1, Fin.prod_univ_three]
  ring

lemma u3_d3_lip (σ : Bool) {T : ℝ} (hT : 0 < T) {γ : Measure (EuclideanSpace ℝ (Fin 1))}
    [IsProbabilityMeasure γ] (hγ : Integrable (fun y : EuclideanSpace ℝ (Fin 1) => ‖y‖) γ) :
    ∃ K : ℝ, ∀ t t' : ℝ, |t| ≤ T → |t'| ≤ T →
      |∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0] ∂γ -
        ∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t') z ![stdVec 0, stdVec 0, stdVec 0] ∂γ| ≤
        K * |t - t'| := by
  set m1 : ℝ := ∫ y, ‖y‖ ∂γ with hm1
  have hm1n : 0 ≤ m1 := integral_nonneg fun _ => norm_nonneg _
  have hh3 : u2P (iteratedDeriv 3 (u2h σ)) := u2P_iter 3 (u2h_P σ)
  have hcont : Continuous (iteratedDeriv 3 (u2h σ)) := (u2P_contDiff hh3).continuous
  have hint : ∀ t : ℝ, |t| ≤ T → Integrable (fun z : EuclideanSpace ℝ (Fin 1) =>
      iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0]) γ := by
    intro t ht
    simp_rw [u3_d3_form]
    refine Integrable.of_bound (C := T ^ 3) ?_ ?_
    · exact (continuous_const.mul (hcont.comp
        (continuous_const.mul (EuclideanSpace.proj (0 : Fin 1)).continuous))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_pow]
      calc |t| ^ 3 * |iteratedDeriv 3 (u2h σ) (t * z 0)| ≤ T ^ 3 * 1 :=
            mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) ht 3) (u2P_bound hh3 _) (abs_nonneg _)
              (by positivity)
        _ = T ^ 3 := mul_one _
  refine ⟨3 * T ^ 2 + T ^ 3 * m1, fun t t' ht ht' => ?_⟩
  rw [← integral_sub (hint t ht) (hint t' ht')]
  have hdom : Integrable (fun z : EuclideanSpace ℝ (Fin 1) =>
      (3 * T ^ 2 + T ^ 3 * ‖z‖) * |t - t'|) γ :=
    ((integrable_const _).add (hγ.const_mul _)).mul_const _
  have := norm_integral_le_of_norm_le hdom (μ := γ)
    (f := fun z => iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0] -
      iteratedFDeriv ℝ 3 (sed_Ucf σ t') z ![stdVec 0, stdVec 0, stdVec 0])
    (Filter.Eventually.of_forall fun z => ?_)
  · rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    have hI : ∫ z, (3 * T ^ 2 + T ^ 3 * ‖z‖) ∂γ = 3 * T ^ 2 + T ^ 3 * m1 := by
      rw [integral_add (integrable_const _) (hγ.const_mul _),
        integral_const_mul (T ^ 3) (fun z : EuclideanSpace ℝ (Fin 1) => ‖z‖), integral_const]
      simp [hm1]
    rw [integral_mul_const, hI]
  · simp only [u3_d3_form]
    set D := iteratedDeriv 3 (u2h σ) (t * z 0)
    set D' := iteratedDeriv 3 (u2h σ) (t' * z 0)
    have hDb : |D| ≤ 1 := u2P_bound hh3 _
    have hz0 : |z 0| ≤ ‖z‖ := (u3_norm_E1 z).ge
    have hDd : |D - D'| ≤ |t - t'| * ‖z‖ := by
      refine (u2P_lip hh3 _ _).trans ?_
      rw [← sub_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left hz0 (abs_nonneg _)
    have ht2 : t ^ 2 ≤ T ^ 2 := by nlinarith [abs_le.1 ht, abs_nonneg t]
    have ht2' : t' ^ 2 ≤ T ^ 2 := by nlinarith [abs_le.1 ht', abs_nonneg t']
    have htt : |t * t'| ≤ T ^ 2 := by
      rw [abs_mul]
      nlinarith [abs_nonneg t, abs_nonneg t']
    have hc : |t ^ 2 + t * t' + t' ^ 2| ≤ 3 * T ^ 2 := by
      rw [abs_le]
      have := abs_le.1 htt
      constructor <;> nlinarith [sq_nonneg t, sq_nonneg t']
    have hpow : |t ^ 3 - t' ^ 3| ≤ 3 * T ^ 2 * |t - t'| := by
      have : t ^ 3 - t' ^ 3 = (t - t') * (t ^ 2 + t * t' + t' ^ 2) := by ring
      rw [this, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
    have e : t ^ 3 * D - t' ^ 3 * D' = (t ^ 3 - t' ^ 3) * D + t' ^ 3 * (D - D') := by ring
    rw [Real.norm_eq_abs, e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_pow]
    have h1 : |t ^ 3 - t' ^ 3| * |D| ≤ 3 * T ^ 2 * |t - t'| := by
      calc _ ≤ |t ^ 3 - t' ^ 3| * 1 := mul_le_mul_of_nonneg_left hDb (abs_nonneg _)
        _ ≤ _ := by rw [mul_one]; exact hpow
    have h2 : |t'| ^ 3 * |D - D'| ≤ T ^ 3 * (|t - t'| * ‖z‖) := by
      calc _ ≤ T ^ 3 * |D - D'| :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ht' 3) (abs_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hDd (by positivity)
    nlinarith

/-! ### Moments under the Gibbs law -/

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

/-- `L^{2k}` moments (`k = 1, 2`) of the centred statistic `Y_u` of a smooth test, uniformly in `N`. -/
theorem u3_Y_moment {u : Torus d → ℝ} (hu : Torus.IsSmooth u) (k : ℕ) (hk1 : 1 ≤ k) (hk2 : k ≤ 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X : Config d N => sed_Y (sed_Q d s N β ρ) u X ^ (2 * k)) (sed_Q d s N β ρ) ∧
      ∫ X, sed_Y (sed_Q d s N β ρ) u X ^ (2 * k) ∂(sed_Q d s N β ρ) ≤ K := by
  have hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  have huc : Continuous u := HRS.Q66.q66_cont_of_smooth hu
  obtain ⟨M, hM⟩ := HRS.Q66.q66_bound_of_smooth hu
  obtain ⟨C7, hC7⟩ := HRS.MC.SEdge.B7.sed_B7_lln_proof hd hs0 hs hβ hρ M k
  obtain ⟨C6, hC6⟩ := HRS.MC.SEdge.B6.sed_B6_mean_bias_proof hd hs0 hs hβ hρ hu
  refine ⟨8 * (max C7 0 + (C6 ^ 2) ^ k), by positivity, fun N hN => ?_⟩
  have hQ : IsProbabilityMeasure (sed_Q d s N β ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
  obtain ⟨hYm, MY, hMY⟩ := HRS.MC.SEdge.B12.b12_Y_facts hN huc.measurable ⟨M, hM⟩ (sed_Q d s N β ρ)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsN1 : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hNpos.le
  set b : ℝ := Real.sqrt N * (∫ Y, pair (empirical Y) u ∂(sed_Q d s N β ρ) -
    pair (withDensityReal ρ) u) with hb
  set U : Config d N → ℝ := fun X => Real.sqrt N *
    (pair (empirical X) u - pair (withDensityReal ρ) u) with hU
  have hYU : ∀ X, sed_Y (sed_Q d s N β ρ) u X = U X - b := by
    intro X; simp only [sed_Y, hU, hb]; ring
  have hbb : b ^ 2 ≤ C6 ^ 2 := by
    have h := hC6 N hN
    have h0 : 0 ≤ C6 / N := (abs_nonneg _).trans h
    have hC60 : 0 ≤ C6 := by
      have := mul_nonneg h0 hNpos.le
      rwa [div_mul_cancel₀ _ hNpos.ne'] at this
    have h1 : |b| ≤ C6 := by
      rw [hb, abs_mul, abs_of_pos hsN]
      calc Real.sqrt N * |∫ Y, pair (empirical Y) u ∂(sed_Q d s N β ρ) - pair (withDensityReal ρ) u|
          ≤ Real.sqrt N * (C6 / N) := mul_le_mul_of_nonneg_left (by
            have e : (∫ Y, pair (empirical Y) u ∂(sed_Q d s N β ρ)) - pair (withDensityReal ρ) u =
                ∫ X, pair (empirical X) u ∂(sed_Q d s N β ρ) - pair (withDensityReal ρ) u := rfl
            rw [e]; exact h) hsN.le
        _ = C6 / Real.sqrt N := u3_sqrt_div hNpos C6
        _ ≤ C6 := div_le_self hC60 hsN1
    calc b ^ 2 = |b| ^ 2 := (sq_abs b).symm
      _ ≤ C6 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hUm : Measurable U :=
    measurable_const.mul ((HRS.MC.SEdge.B5b.b5b_pair_meas hN huc.measurable).sub measurable_const)
  have hUb : ∀ X, |U X| ≤ MY + |b| := fun X => by
    have : U X = sed_Y (sed_Q d s N β ρ) u X + b := by rw [hYU]; ring
    rw [this]
    exact (abs_add_le _ _).trans (add_le_add (hMY X) le_rfl)
  have hYi : Integrable (fun X : Config d N => sed_Y (sed_Q d s N β ρ) u X ^ (2 * k))
      (sed_Q d s N β ρ) := by
    refine Integrable.of_bound (hYm.pow_const _).aestronglyMeasurable (MY ^ (2 * k))
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hMY X) _
  have hUi : Integrable (fun X : Config d N => U X ^ (2 * k)) (sed_Q d s N β ρ) := by
    refine Integrable.of_bound (hUm.pow_const _).aestronglyMeasurable ((MY + |b|) ^ (2 * k))
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hUb X) _
  refine ⟨hYi, ?_⟩
  have hUint : ∫ X, U X ^ (2 * k) ∂(sed_Q d s N β ρ) ≤ max C7 0 := by
    have e : ∀ X, U X ^ (2 * k) = (N : ℝ) ^ k *
        (pair (empirical X) u - pair (withDensityReal ρ) u) ^ (2 * k) := fun X => by
      simp only [hU]
      rw [mul_pow, pow_mul, hsq]
    simp_rw [e]
    rw [integral_const_mul]
    have h7 := hC7 u huc.measurable hM N hN
    have hNk : (0 : ℝ) < (N : ℝ) ^ k := by positivity
    calc (N : ℝ) ^ k * ∫ X, (pair (empirical X) u - pair (withDensityReal ρ) u) ^ (2 * k)
          ∂(sed_Q d s N β ρ) ≤ (N : ℝ) ^ k * (C7 / (N : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left h7 hNk.le
      _ = C7 := by field_simp
      _ ≤ max C7 0 := le_max_left _ _
  calc ∫ X, sed_Y (sed_Q d s N β ρ) u X ^ (2 * k) ∂(sed_Q d s N β ρ)
      ≤ ∫ X, 8 * (U X ^ (2 * k) + b ^ (2 * k)) ∂(sed_Q d s N β ρ) := by
        refine integral_mono hYi ((hUi.add (integrable_const _)).const_mul 8) fun X => ?_
        simp only [hYU]
        exact u3_pow_sub k hk1 hk2
    _ = 8 * (∫ X, U X ^ (2 * k) ∂(sed_Q d s N β ρ) + b ^ (2 * k)) := by
        rw [integral_const_mul, integral_add hUi (integrable_const _)]
        simp
    _ ≤ 8 * (max C7 0 + (C6 ^ 2) ^ k) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hUint ?_) (by norm_num)
        rw [pow_mul]
        exact pow_le_pow_left₀ (sq_nonneg _) hbb k

/-- `L^{3/2}` moment of `B_N` (with integrability). -/
theorem u3_B_l32 {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j)) :
    (∀ N : ℕ, 1 ≤ N → Integrable (fun X : Config d N => sed_B d s ρ β v X) (sed_Q d s N β ρ)) ∧
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X : Config d N => |sed_B d s ρ β v X| ^ (3 / 2 : ℝ)) (sed_Q d s N β ρ) ∧
      ∫ X, |sed_B d s ρ β v X| ^ (3 / 2 : ℝ) ∂(sed_Q d s N β ρ) ≤ K := by
  have hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨hint, C4, hC4⟩ := HRS.MC.SEdge.B4b.sed_B4b_energy_proof hd hs0 hs hβ hρ hv
  refine ⟨fun N hN => ?_, ?_⟩
  · have := HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
    unfold sed_B
    exact ((hint N hN).sub (integrable_const _)).const_mul _
  set J : ℝ := ∫ x, ∫ y, Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hJ
  set K2 : ℝ := 3 * ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ)
    with hK2
  obtain ⟨C43, hC43, T43⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof hd hs0 hs hβ hρ (r := 4 / 3)
    (by norm_num)
  set Ac : ℝ := |J| / 2 + max C4 0 with hAc
  have hAc0 : 0 ≤ Ac := by positivity
  have hK20 : 0 ≤ K2 := by
    rw [hK2]
    exact mul_nonneg (by norm_num) (integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _)
  set A' : ℝ := C43 * (2 * K2 + 2 * Ac ^ 2) ^ (1 / (4 / 3 : ℝ)) with hA'def
  have hA'0 : 0 ≤ A' := mul_nonneg hC43 (Real.rpow_nonneg (by positivity) _)
  refine ⟨A', fun N hN => ?_⟩
  have hG : IsProbabilityMeasure (sed_Q d s N β ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
  have hPP : IsProbabilityMeasure (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
    infer_instance
  obtain ⟨hYm, hYL, hYint⟩ := HRS.MC.SEdge.B4b.b4b_L2 hd hs0 hs hρ hv N hN
  set Y : Config d N → ℝ := HRS.MC.SEdge.B4b.b4b_Y d s ρ v N with hYdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set c : ℝ := J / 2 + ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
    ∂(sed_Q d s N β ρ) with hc
  have hB : ∀ X, sed_B d s ρ β v X = Y X - c := by
    intro X
    have h1 : ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
        ∂(sed_Q d s N β ρ) = (N : ℝ) * ∫ X, modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
        ∂(sed_Q d s N β ρ) := integral_const_mul _ _
    simp only [sed_B, hYdef, HRS.MC.SEdge.B4b.b4b_Y, hc, h1, hJ]
    ring
  have hcA : |c| ≤ Ac := by
    have h2 := (hC4 N hN).1
    calc |c| ≤ |J / 2| + |∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
          ∂(sed_Q d s N β ρ)| := abs_add_le _ _
      _ ≤ |J| / 2 + max C4 0 := by
        have e2 : |J / 2| = |J| / 2 := by rw [abs_div]; norm_num
        exact add_le_add e2.le (h2.trans (le_max_left _ _))
      _ = Ac := rfl
  have hsq : ∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2)
      ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≤ ENNReal.ofReal (2 * K2 + 2 * Ac ^ 2) := by
    have hi : Integrable (fun X => (Y X - c) ^ 2)
        (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
      have := (hYL.sub (memLp_const c)).integrable_sq
      simpa using this
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hdom : Integrable (fun X => 2 * Y X ^ 2 + 2 * c ^ 2)
        (Measure.pi fun _ : Fin N => withDensityReal ρ) :=
      (hYL.integrable_sq.const_mul 2).add (integrable_const _)
    calc ∫ X, (Y X - c) ^ 2 ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)
        ≤ ∫ X, (2 * Y X ^ 2 + 2 * c ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) :=
          integral_mono hi hdom (fun X => by nlinarith [sq_nonneg (Y X + c)])
      _ = 2 * ∫ X, Y X ^ 2 ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) + 2 * c ^ 2 := by
          rw [integral_add (hYL.integrable_sq.const_mul 2) (integrable_const _),
            integral_const_mul]
          simp
      _ ≤ 2 * K2 + 2 * Ac ^ 2 := by
          have : c ^ 2 ≤ Ac ^ 2 := by
            rw [← sq_abs c]
            exact pow_le_pow_left₀ (abs_nonneg _) hcA 2
          have := hYint
          nlinarith
  have hf : Measurable (fun X => ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ))) :=
    ((hYm.sub_const c).abs.pow_const _).ennreal_ofReal
  have h1 := T43 N hN _ hf
  have h2 : ∫⁻ X, (ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ))) ^ (4 / 3 : ℝ)
      ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) =
      ∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2)
        ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) := by
    refine lintegral_congr fun X => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by norm_num),
      ← Real.rpow_mul (abs_nonneg _)]
    have : (3 / 2 : ℝ) * (4 / 3) = (2 : ℕ) := by norm_num
    rw [this, Real.rpow_natCast, sq_abs]
  rw [h2] at h1
  have h3 : ∫⁻ X, ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ)) ∂(sed_Q d s N β ρ) ≤
      ENNReal.ofReal A' := by
    refine h1.trans ?_
    calc ENNReal.ofReal C43 * (∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2)
          ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)) ^ (1 / (4 / 3 : ℝ))
        ≤ ENNReal.ofReal C43 * (ENNReal.ofReal (2 * K2 + 2 * Ac ^ 2)) ^ (1 / (4 / 3 : ℝ)) := by
          gcongr
      _ = ENNReal.ofReal A' := by
          rw [hA'def, ENNReal.ofReal_mul hC43,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  have hg : (fun X => |sed_B d s ρ β v X| ^ (3 / 2 : ℝ)) = fun X => |Y X - c| ^ (3 / 2 : ℝ) :=
    funext fun X => by rw [hB]
  rw [hg]
  have hgm : Measurable (fun X => |Y X - c| ^ (3 / 2 : ℝ)) :=
    (hYm.sub_const c).abs.pow_const _
  have hgn : ∀ X, 0 ≤ |Y X - c| ^ (3 / 2 : ℝ) := fun X => Real.rpow_nonneg (abs_nonneg _) _
  refine ⟨?_, ?_⟩
  · refine ⟨hgm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hgn)]
    exact lt_of_le_of_lt h3 ENNReal.ofReal_lt_top
  · have h4 : ∫ X, |Y X - c| ^ (3 / 2 : ℝ) ∂(sed_Q d s N β ρ) =
        (∫⁻ X, ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ)) ∂(sed_Q d s N β ρ)).toReal :=
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hgn) hgm.aestronglyMeasurable
    rw [h4]
    exact ENNReal.toReal_le_of_le_ofReal hA'0 h3

end Main

/-! ### Bounded measurable functions, difference estimates, the Stein solution family -/

section Bdd

variable {Ω : Type*} [MeasurableSpace Ω]

def u3Bdd (f : Ω → ℝ) : Prop := Measurable f ∧ ∃ M, ∀ X, |f X| ≤ M

lemma u3Bdd.mul {f g : Ω → ℝ} (hf : u3Bdd f) (hg : u3Bdd g) : u3Bdd (fun X => f X * g X) := by
  obtain ⟨hfm, Mf, hMf⟩ := hf
  obtain ⟨hgm, Mg, hMg⟩ := hg
  refine ⟨hfm.mul hgm, Mf * Mg, fun X => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hMf X) (hMg X) (abs_nonneg _) ((abs_nonneg _).trans (hMf X))

lemma u3Bdd.integrable {f : Ω → ℝ} (hf : u3Bdd f) (Q : Measure Ω) [IsFiniteMeasure Q] :
    Integrable f Q := by
  obtain ⟨hm, M, hM⟩ := hf
  exact Integrable.of_bound hm.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hM X)

lemma u3_g_facts {f : EuclideanSpace ℝ (Fin 1) → ℝ} (hf : sed_StBdd f 3)
    {W : Ω → EuclideanSpace ℝ (Fin 1)} (hW : Measurable W) :
    u3Bdd (fun X => iteratedFDeriv ℝ 2 f (W X) ![stdVec 0, stdVec 0]) ∧
    u3Bdd (fun X => fderiv ℝ f (W X) (stdVec 0)) := by
  constructor
  · obtain ⟨hc, M, hM⟩ := HRS.MC.SEdge.B12.b12_second_facts hf 0 0
    exact ⟨hc.measurable.comp hW, M, fun X => hM _⟩
  · obtain ⟨M0, hM0⟩ := (HRS.MC.SEdge.B12.b12_psi_memCb hf 0).2 0 (Nat.zero_le _)
    refine ⟨((HRS.MC.SEdge.B12.b12_psi_memCb hf 0).1.continuous.measurable).comp hW, M0,
      fun X => ?_⟩
    have := hM0 ⟨W X, rfl⟩
    simpa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using this

end Bdd

lemma u3_diff_j2 {f f' : EuclideanSpace ℝ (Fin 1) → ℝ} {x : EuclideanSpace ℝ (Fin 1)} {c : ℝ}
    (h : ‖iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f' x‖ ≤ c) :
    |iteratedFDeriv ℝ 2 f x ![stdVec 0, stdVec 0] - iteratedFDeriv ℝ 2 f' x ![stdVec 0, stdVec 0]|
      ≤ c := by
  have h1 := (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f' x).le_opNorm ![stdVec 0, stdVec 0]
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    HRS.MC.SEdge.B12.b12_stdVec_norm, mul_one, sub_apply] at h1
  rw [← Real.norm_eq_abs]
  exact h1.trans h

lemma u3_diff_j1 {f f' : EuclideanSpace ℝ (Fin 1) → ℝ} {x : EuclideanSpace ℝ (Fin 1)} {c : ℝ}
    (h : ‖iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f' x‖ ≤ c) :
    |fderiv ℝ f x (stdVec 0) - fderiv ℝ f' x (stdVec 0)| ≤ c := by
  have h1 := (iteratedFDeriv ℝ 1 f x - iteratedFDeriv ℝ 1 f' x).le_opNorm ![stdVec 0]
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton, Matrix.cons_val_zero,
    HRS.MC.SEdge.B12.b12_stdVec_norm, mul_one, sub_apply,
    iteratedFDeriv_one_apply] at h1
  rw [← Real.norm_eq_abs]
  exact h1.trans h

lemma u3Bdd.abs {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ} (hf : u3Bdd f) :
    u3Bdd (fun X => |f X|) := by
  obtain ⟨hm, M, hM⟩ := hf
  exact ⟨hm.abs, M, fun X => by simpa using hM X⟩

lemma u3Bdd.const_add {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ} (c : ℝ) (hf : u3Bdd f) :
    u3Bdd (fun X => c + f X) := by
  obtain ⟨hm, M, hM⟩ := hf
  exact ⟨measurable_const.add hm, |c| + M, fun X => (abs_add_le _ _).trans
    (add_le_add le_rfl (hM X))⟩

lemma u3_int_mul_bdd {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω} {f g : Ω → ℝ}
    (hf : Integrable f Q) (hg : u3Bdd g) : Integrable (fun X => f X * g X) Q := by
  obtain ⟨hm, M, hM⟩ := hg
  exact hf.mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun X => by simpa [Real.norm_eq_abs] using hM X)

/-- The Stein solution of `F_t = cos(t .)` resp. `sin(t .)` for the Gaussian `N(0,C)`. -/
def u3f (C : Matrix (Fin 1) (Fin 1) ℝ) (σ : Bool) (t : ℝ) : EuclideanSpace ℝ (Fin 1) → ℝ :=
  steinSolution (multivariateGaussian 0 C) (fun z : EuclideanSpace ℝ (Fin 1) => z) (sed_Ucf σ t)

lemma u3_Fmem (σ : Bool) (t : ℝ) : MemCb 5 (sed_Ucf σ t) := by
  rw [sed_Ucf_eq]; exact u2_memCb (u2h_P σ) t

lemma u3_props (C : Matrix (Fin 1) (Fin 1) ℝ) (hC : C.PosSemidef) (σ : Bool) (t : ℝ) :
    sed_StBdd (u3f C σ t) 3 ∧ ∀ x : EuclideanSpace ℝ (Fin 1),
      ∑ a, ∑ b, C a b * iteratedFDeriv ℝ 2 (u3f C σ t) x ![stdVec a, stdVec b] -
        ∑ a, x a * fderiv ℝ (u3f C σ t) x (stdVec a) =
      sed_Ucf σ t x - ∫ z, sed_Ucf σ t z ∂(multivariateGaussian 0 C) := by
  obtain ⟨f, hfe, hf5, hfb, hst, -⟩ :=
    HRS.MC.SEdge.B11b.sed_B11b_ou_proof C hC (u3_Fmem σ t)
  have hf : u3f C σ t = f := hfe.symm
  rw [hf]
  refine ⟨⟨hf5.of_le (by norm_num), fun j hj1 hj3 => ?_⟩, hst⟩
  exact ⟨(j : ℝ)⁻¹ * ⨆ y, ‖iteratedFDeriv ℝ j (sed_Ucf σ t) y‖, fun x => hfb j hj1 (by omega) x⟩

/-! ### The main theorem -/

theorem sed_U3_equilip_proof {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {β : ℝ} (hβ : 0 ≤ β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (T : ℝ) (hT : 0 < T) (σ : Bool) :
    ∃ L : ℝ, ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (-T) T, ∀ t' ∈ Set.Icc (-T) T,
      |sed_Uerr d s β ρ φ σ N t - sed_Uerr d s β ρ φ σ N t'| ≤ L * |t - t'| := by
  have hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  have hφ1 : ∀ a : Fin 1, Torus.IsSmooth ((fun _ : Fin 1 => φ) a) := fun _ => hφ
  have hCpsd := HRS.MC.SEdge.B11a.sed_B11a_cov_psd_proof hd hs0 hs hβ hρ hφ1
  set Cm : Matrix (Fin 1) (Fin 1) ℝ := sed_Cmat d s β ρ (fun _ : Fin 1 => φ) with hCm
  obtain ⟨r, v, hrs, hvs, -, hresp, -, hdiv⟩ :=
    HRS.MC.SEdge.B1.sed_B1_regular_proof hd hs0 hs hβ hρ hφ
  have hv0 : 0 ≤ Cm 0 0 := hCpsd.diag_nonneg
  have hCmeq : Matrix.of (fun _ _ : Fin 1 => Cm 0 0) = Cm := by
    ext i j; fin_cases i; fin_cases j; rfl
  obtain ⟨K2, hK2⟩ := HRS.MC.SEdge.U2.sed_U2_stein_lipschitz_proof (Cm 0 0) hv0 T hT σ
  rw [hCmeq] at hK2
  have hK2' : ∀ j : ℕ, 1 ≤ j → j ≤ 2 → ∀ t t' : ℝ, |t| ≤ T → |t'| ≤ T →
      ∀ x : EuclideanSpace ℝ (Fin 1),
      ‖iteratedFDeriv ℝ j (u3f Cm σ t) x - iteratedFDeriv ℝ j (u3f Cm σ t') x‖ ≤
        max K2 0 * |t - t'| * (1 + ‖x‖) := by
    intro j hj1 hj2 t t' ht ht' x
    refine (hK2 j hj1 hj2 t t' ht ht' x).trans ?_
    gcongr
    exact le_max_left _ _
  have : IsProbabilityMeasure (multivariateGaussian 0 Cm) := inferInstance
  have hγ1 : Integrable (fun y : EuclideanSpace ℝ (Fin 1) => ‖y‖) (multivariateGaussian 0 Cm) :=
    IsGaussian.integrable_id.norm
  obtain ⟨K3, hK3⟩ := u3_d3_lip σ hT hγ1
  obtain ⟨hBint, KB, hKB⟩ := u3_B_l32 hd hs0 hs hβ hρ hvs
  have hdriftS : Torus.IsSmooth (sed_drift v φ) := by
    unfold sed_drift
    exact HRS.MC.SEdge.B13a.b13a_isSmooth_sum _ fun k =>
      HRS.MC.SEdge.B13a.b13a_isSmooth_mul (hvs k) (HRS.Q66.q66_isSmooth_partialDeriv hφ k)
  obtain ⟨KYw, hKYw0, hKYw⟩ := u3_Y_moment hd hs0 hs hβ hρ hdriftS 1 le_rfl (by norm_num)
  obtain ⟨KW2, hKW20, hKW2⟩ := u3_Y_moment hd hs0 hs hβ hρ hφ 1 le_rfl (by norm_num)
  obtain ⟨KW4, hKW40, hKW4⟩ := u3_Y_moment hd hs0 hs hβ hρ hφ 2 (by norm_num) le_rfl
  obtain ⟨K13, hK13⟩ := HRS.MC.SEdge.B13a.sed_B13a_bias_proof hd hs0 hs hβ hρ
    (φ := fun _ : Fin 1 => φ) hφ1 (a := 0) (b := 0) (ra := r) hrs hvs hdiv hresp
  set κ : ℝ := sed_kappa d s β ρ (fun _ : Fin 1 => φ) 0 0 0 with hκ
  refine ⟨max K2 0 * (2 * (max K13 0 + 1) * (1 + KYw + KW2)) +
    β * max K2 0 * (KB + 8 * (1 + KW4)) + |κ| / 6 * K3, ?_⟩
  intro N hN t ht t' ht'
  have htT : |t| ≤ T := abs_le.2 ⟨ht.1, ht.2⟩
  have ht'T : |t'| ≤ T := abs_le.2 ⟨ht'.1, ht'.2⟩
  have hQ : IsProbabilityMeasure (sed_Q d s N β ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  have hsN1 : 1 ≤ Real.sqrt N := by
    rw [Real.one_le_sqrt]; exact_mod_cast hN
  have hφc : Continuous φ := HRS.Q66.q66_cont_of_smooth hφ
  have hdc : Continuous (sed_drift v φ) := HRS.Q66.q66_cont_of_smooth hdriftS
  have hYφ : u3Bdd (sed_Y (sed_Q d s N β ρ) φ) :=
    HRS.MC.SEdge.B12.b12_Y_facts hN hφc.measurable (HRS.Q66.q66_bound_of_smooth hφ) _
  obtain ⟨hAm, MA, hMA⟩ := HRS.MC.SEdge.B12.b12_A_facts (N := N) hN hvs hφ
  have hWm : Measurable (centeredStat (sed_Q d s N β ρ) (fun _ : Fin 1 => φ)) := by
    unfold centeredStat
    exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun _ => hYφ.1)
  set Q := sed_Q d s N β ρ with hQdef
  set W := centeredStat Q (fun _ : Fin 1 => φ) with hWdef
  set γ := multivariateGaussian 0 Cm with hγdef
  -- the coefficient `a_N = sqrt N (C - A_N)`
  set a : Config d N → ℝ := fun X => Real.sqrt N * (Cm 0 0 - sed_A v φ X) with hadef
  have ha : u3Bdd a :=
    ⟨measurable_const.mul (measurable_const.sub hAm), Real.sqrt N * (|Cm 0 0| + MA), fun X => by
      simp only [hadef]
      rw [abs_mul, abs_of_pos hsN]
      exact mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add le_rfl (hMA X))) hsN.le⟩
  have hab : ∀ X : Config d N, |a X| ≤ max K13 0 + |sed_Y Q (sed_drift v φ) X| := by
    intro X
    have hK := hK13 N hN
    have hK0 : 0 ≤ K13 := by
      have h0 : 0 ≤ K13 / N := (abs_nonneg _).trans hK
      have := mul_nonneg h0 hNpos.le
      rwa [div_mul_cancel₀ _ hNpos.ne'] at this
    have e : a X = Real.sqrt N * (Cm 0 0 - ∫ Y, sed_A v φ Y ∂Q) -
        sed_Y Q (sed_drift v φ) X := by
      have : sed_Y Q (sed_drift v φ) X =
          Real.sqrt N * (sed_A v φ X - ∫ Y, sed_A v φ Y ∂Q) := rfl
      rw [this]; simp only [hadef]; ring
    rw [e]
    refine (abs_sub _ _).trans (add_le_add ?_ le_rfl)
    rw [abs_mul, abs_of_pos hsN]
    calc Real.sqrt N * |Cm 0 0 - ∫ Y, sed_A v φ Y ∂Q| ≤ Real.sqrt N * (K13 / N) :=
          mul_le_mul_of_nonneg_left hK hsN.le
      _ = K13 / Real.sqrt N := u3_sqrt_div hNpos K13
      _ ≤ K13 := div_le_self hK0 hsN1
      _ ≤ max K13 0 := le_max_left _ _
  -- the master identity
  have hint : Integrable
      (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)) Q :=
    (HRS.MC.SEdge.B4b.sed_B4b_energy_proof hd hs0 hs hβ hρ hvs).1 N hN
  have hFc : ∀ t, Continuous (sed_Ucf σ t) := fun t => (u3_Fmem σ t).1.continuous
  have hFb : ∀ t, ∃ M, ∀ z, |sed_Ucf σ t z| ≤ M := fun t => ⟨1, fun z => by
    unfold sed_Ucf
    split_ifs
    · exact Real.abs_cos_le_one _
    · exact Real.abs_sin_le_one _⟩
  have hmaster : ∀ t : ℝ, ∫ X, sed_Ucf σ t (W X) ∂Q - ∫ z, sed_Ucf σ t z ∂γ =
      ∫ X, (Cm 0 0 - sed_A v φ X) *
        iteratedFDeriv ℝ 2 (u3f Cm σ t) (W X) ![stdVec 0, stdVec 0] ∂Q +
      β / Real.sqrt N * ∫ X, sed_B d s ρ β v X * fderiv ℝ (u3f Cm σ t) (W X) (stdVec 0) ∂Q := by
    intro t
    have h := HRS.MC.SEdge.B12.sed_B12_master_proof hd hs0 hs hβ hρ hN hφ1
      (r := fun _ => r) (fun _ => hrs) (v := fun _ => v) (fun _ _ => hvs _) (fun _ => hdiv)
      (fun _ => hresp) (fun _ => hint) (hFc t) (hFb t) (u3_props Cm hCpsd σ t).1
      (u3_props Cm hCpsd σ t).2
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at h
    exact h
  have hPR : ∀ t : ℝ, sed_Uerr d s β ρ φ σ N t =
      ∫ X, a X * iteratedFDeriv ℝ 2 (u3f Cm σ t) (W X) ![stdVec 0, stdVec 0] ∂Q +
      β * ∫ X, sed_B d s ρ β v X * fderiv ℝ (u3f Cm σ t) (W X) (stdVec 0) ∂Q -
      κ / 6 * ∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0] ∂γ := by
    intro t
    have hU : sed_Uerr d s β ρ φ σ N t = Real.sqrt N * (∫ X, sed_Ucf σ t (W X) ∂Q -
        ∫ z, sed_Ucf σ t z ∂γ - 1 / (6 * Real.sqrt N) * κ *
        ∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0] ∂γ) := rfl
    rw [hU, hmaster t]
    have e1 : ∫ X, a X * iteratedFDeriv ℝ 2 (u3f Cm σ t) (W X) ![stdVec 0, stdVec 0] ∂Q =
        Real.sqrt N * ∫ X, (Cm 0 0 - sed_A v φ X) *
          iteratedFDeriv ℝ 2 (u3f Cm σ t) (W X) ![stdVec 0, stdVec 0] ∂Q := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun X => mul_assoc _ _ _)
    rw [e1]
    field_simp
  -- the three increments
  have hdiff : sed_Uerr d s β ρ φ σ N t - sed_Uerr d s β ρ φ σ N t' =
      (∫ X, a X * iteratedFDeriv ℝ 2 (u3f Cm σ t) (W X) ![stdVec 0, stdVec 0] ∂Q -
        ∫ X, a X * iteratedFDeriv ℝ 2 (u3f Cm σ t') (W X) ![stdVec 0, stdVec 0] ∂Q) +
      β * (∫ X, sed_B d s ρ β v X * fderiv ℝ (u3f Cm σ t) (W X) (stdVec 0) ∂Q -
        ∫ X, sed_B d s ρ β v X * fderiv ℝ (u3f Cm σ t') (W X) (stdVec 0) ∂Q) -
      κ / 6 * (∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0] ∂γ -
        ∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t') z ![stdVec 0, stdVec 0, stdVec 0] ∂γ) := by
    rw [hPR t, hPR t']; ring
  have hΔ : 0 ≤ max K2 0 * |t - t'| := mul_nonneg (le_max_right _ _) (abs_nonneg _)
  obtain ⟨hg2t, hg1t⟩ := u3_g_facts (u3_props Cm hCpsd σ t).1 hWm
  obtain ⟨hg2t', hg1t'⟩ := u3_g_facts (u3_props Cm hCpsd σ t').1 hWm
  have hYwb : u3Bdd (sed_Y Q (sed_drift v φ)) :=
    HRS.MC.SEdge.B12.b12_Y_facts hN hdc.measurable (HRS.Q66.q66_bound_of_smooth hdriftS) _
  -- moment facts
  have hYw2 : Integrable (fun X => sed_Y Q (sed_drift v φ) X ^ 2) Q ∧
      ∫ X, sed_Y Q (sed_drift v φ) X ^ 2 ∂Q ≤ KYw := by simpa using hKYw N hN
  have hW2 : Integrable (fun X => sed_Y Q φ X ^ 2) Q ∧ ∫ X, sed_Y Q φ X ^ 2 ∂Q ≤ KW2 := by
    simpa using hKW2 N hN
  have hW4 : Integrable (fun X => sed_Y Q φ X ^ 4) Q ∧ ∫ X, sed_Y Q φ X ^ 4 ∂Q ≤ KW4 := by
    simpa using hKW4 N hN
  have hwd : u3Bdd (fun X => |a X| * (1 + |sed_Y Q φ X|)) :=
    ha.abs.mul (hYφ.abs.const_add 1)
  -- (1) the `P` increment
  have hP1 : |∫ X, a X * iteratedFDeriv ℝ 2 (u3f Cm σ t) (W X) ![stdVec 0, stdVec 0] ∂Q -
        ∫ X, a X * iteratedFDeriv ℝ 2 (u3f Cm σ t') (W X) ![stdVec 0, stdVec 0] ∂Q| ≤
      (max K2 0 * |t - t'|) * (2 * (max K13 0 + 1) * (1 + KYw + KW2)) := by
    have h1 := u3_lip_int (Q := Q) (a := a) (w := fun X => sed_Y Q φ X) hΔ
      ((ha.mul hg2t).integrable Q) ((ha.mul hg2t').integrable Q) (hwd.integrable Q) (fun X => by
        have := u3_diff_j2 (hK2' 2 (by norm_num) le_rfl t t' htT ht'T (W X))
        rw [u3_norm_E1] at this
        exact this)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hΔ)
    have hI : ∫ X, |a X| * (1 + |sed_Y Q φ X|) ∂Q ≤
        ∫ X, 2 * (max K13 0 + 1) *
          (1 + sed_Y Q (sed_drift v φ) X ^ 2 + sed_Y Q φ X ^ 2) ∂Q := by
      refine integral_mono (hwd.integrable Q)
        ((((integrable_const 1).add hYw2.1).add hW2.1).const_mul _) fun X => ?_
      calc |a X| * (1 + |sed_Y Q φ X|) ≤
            (max K13 0 + |sed_Y Q (sed_drift v φ) X|) * (1 + |sed_Y Q φ X|) :=
            mul_le_mul_of_nonneg_right (hab X) (by positivity)
        _ ≤ _ := u3_poly1 _ _ _ (le_max_right _ _)
    refine hI.trans ?_
    have hi1 : Integrable (fun X => 1 + sed_Y Q (sed_drift v φ) X ^ 2) Q :=
      (integrable_const 1).add hYw2.1
    rw [integral_const_mul, integral_add hi1 hW2.1, integral_add (integrable_const 1) hYw2.1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    have : 0 ≤ 2 * (max K13 0 + 1) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith [hYw2.2, hW2.2]) this
  -- (2) the `R` increment
  have hBi := hBint N hN
  have hP2 : |∫ X, sed_B d s ρ β v X * fderiv ℝ (u3f Cm σ t) (W X) (stdVec 0) ∂Q -
        ∫ X, sed_B d s ρ β v X * fderiv ℝ (u3f Cm σ t') (W X) (stdVec 0) ∂Q| ≤
      (max K2 0 * |t - t'|) * (KB + 8 * (1 + KW4)) := by
    have hdomR : Integrable (fun X => |sed_B d s ρ β v X| * (1 + |sed_Y Q φ X|)) Q :=
      u3_int_mul_bdd hBi.abs (hYφ.abs.const_add 1)
    have h1 := u3_lip_int (Q := Q) (a := fun X => sed_B d s ρ β v X) (w := fun X => sed_Y Q φ X)
      hΔ (u3_int_mul_bdd hBi hg1t) (u3_int_mul_bdd hBi hg1t') hdomR (fun X => by
        have := u3_diff_j1 (hK2' 1 le_rfl (by norm_num) t t' htT ht'T (W X))
        rw [u3_norm_E1] at this
        exact this)
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hΔ)
    obtain ⟨hBl1, hBl2⟩ := hKB N hN
    have hI : ∫ X, |sed_B d s ρ β v X| * (1 + |sed_Y Q φ X|) ∂Q ≤
        ∫ X, (|sed_B d s ρ β v X| ^ (3 / 2 : ℝ) + 8 * (1 + sed_Y Q φ X ^ 4)) ∂Q := by
      refine integral_mono hdomR (hBl1.add (((integrable_const 1).add hW4.1).const_mul 8))
        fun X => ?_
      calc |sed_B d s ρ β v X| * (1 + |sed_Y Q φ X|) ≤
            |sed_B d s ρ β v X| ^ (3 / 2 : ℝ) + (1 + |sed_Y Q φ X|) ^ 3 :=
            u3_young (abs_nonneg _) (by positivity)
        _ ≤ _ := add_le_add le_rfl (u3_poly2 _)
    refine hI.trans ?_
    have hi2 : Integrable (fun X => 1 + sed_Y Q φ X ^ 4) Q := (integrable_const 1).add hW4.1
    rw [integral_add hBl1 (hi2.const_mul 8), integral_const_mul, integral_add (integrable_const 1) hW4.1]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    linarith [hW4.2]
  -- (3) the third-derivative increment
  have hP3 := hK3 t t' htT ht'T
  rw [hdiff]
  have hκ6 : 0 ≤ |κ| / 6 := by positivity
  calc _ ≤ |∫ X, a X * iteratedFDeriv ℝ 2 (u3f Cm σ t) (W X) ![stdVec 0, stdVec 0] ∂Q -
        ∫ X, a X * iteratedFDeriv ℝ 2 (u3f Cm σ t') (W X) ![stdVec 0, stdVec 0] ∂Q| +
      β * |∫ X, sed_B d s ρ β v X * fderiv ℝ (u3f Cm σ t) (W X) (stdVec 0) ∂Q -
        ∫ X, sed_B d s ρ β v X * fderiv ℝ (u3f Cm σ t') (W X) (stdVec 0) ∂Q| +
      |κ| / 6 * |∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t) z ![stdVec 0, stdVec 0, stdVec 0] ∂γ -
        ∫ z, iteratedFDeriv ℝ 3 (sed_Ucf σ t') z ![stdVec 0, stdVec 0, stdVec 0] ∂γ| := by
        refine (abs_sub _ _).trans ?_
        refine add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_
        · exact le_of_eq (by rw [abs_mul, abs_of_nonneg hβ])
        · exact le_of_eq (by rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)])
    _ ≤ (max K2 0 * |t - t'|) * (2 * (max K13 0 + 1) * (1 + KYw + KW2)) +
        β * ((max K2 0 * |t - t'|) * (KB + 8 * (1 + KW4))) + |κ| / 6 * (K3 * |t - t'|) := by
        refine add_le_add (add_le_add hP1 (mul_le_mul_of_nonneg_left hP2 hβ))
          (mul_le_mul_of_nonneg_left hP3 hκ6)
    _ = _ := by ring


end HRS.MC.SEdge.U3

end
