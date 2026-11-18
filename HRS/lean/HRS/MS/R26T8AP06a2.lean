import HRS.MS.R26T8AP06a1
import HRS.Torus.Basic

/-!
# S8.2 P06a infrastructure (2): comparison of two directions at equal radius, and the limit at the origin
`r26t8a_p06_limit`: if `G` is differentiable off `0` with `‖fderiv G y‖ <= B |y|^(a-1) (1+|log|y||)^b` (`a>0`, `|y|<=1/2`,
dimension `>= 2`) then `G` has a limit `T` at `0` with rate `‖G z - T‖ <= C B |z|^a (1+|log|z||)^b`.
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_p06_orth (d : ℕ) (hd : 2 ≤ d) (y : Euc d) :
    ∃ w : Euc d, ‖w‖ = 1 ∧ inner ℝ y w = 0 := by
  by_cases hy : y = 0
  · refine ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, by simp, by simp [hy]⟩
  · have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = (d - 1) + 1 := by
      simp; omega
    have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = (d - 1) + 1) := ⟨hfin⟩
    have h1 := Submodule.finrank_orthogonal_span_singleton (𝕜 := ℝ) (n := d - 1) (v := y) hy
    have h2 : 0 < Module.finrank ℝ (ℝ ∙ y)ᗮ := by rw [h1]; omega
    obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 h2
    have hwn : (w : EuclideanSpace ℝ (Fin d)) ≠ 0 := fun h => hw0 (Subtype.ext h)
    refine ⟨(‖(w : EuclideanSpace ℝ (Fin d))‖⁻¹) • (w : EuclideanSpace ℝ (Fin d)), ?_, ?_⟩
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hwn)]
    · rw [inner_smul_right]
      have := (Submodule.mem_orthogonal' _ _).1 w.2 y (Submodule.mem_span_singleton_self y)
      rw [real_inner_comm] at this
      simp [this]

/-- A midpoint direction at the same radius, making an acute angle with both. -/
theorem r26t8a_p06_mid (d : ℕ) (hd : 2 ≤ d) (y y' : Euc d) {s : ℝ} (hs : 0 < s) (hy : ‖y‖ = s)
    (hy' : ‖y'‖ = s) :
    ∃ e : Euc d, ‖e‖ = s ∧ 0 ≤ inner ℝ y e ∧ 0 ≤ inner ℝ e y' := by
  by_cases h : y + y' = 0
  · obtain ⟨w, hw, hyw⟩ := r26t8a_p06_orth d hd y
    refine ⟨s • w, by rw [norm_smul, hw, Real.norm_of_nonneg hs.le, mul_one], ?_, ?_⟩
    · rw [inner_smul_right, hyw]; simp
    · have : y' = -y := by rw [← sub_eq_zero]; simpa [sub_neg_eq_add, add_comm] using h
      rw [this, inner_smul_left, inner_neg_right, real_inner_comm, hyw]; simp
  · have hn : 0 < ‖y + y'‖ := norm_pos_iff.2 h
    refine ⟨(s / ‖y + y'‖) • (y + y'), ?_, ?_, ?_⟩
    · rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hn.ne']
    · have hb : -(s * s) ≤ inner ℝ y y' := by
        have := abs_real_inner_le_norm y y'
        rw [hy, hy'] at this
        linarith [neg_abs_le (inner ℝ y y')]
      rw [inner_smul_right, inner_add_right, real_inner_self_eq_norm_sq, hy]
      exact mul_nonneg (by positivity) (by nlinarith)
    · have hb : -(s * s) ≤ inner ℝ y y' := by
        have := abs_real_inner_le_norm y y'
        rw [hy, hy'] at this
        linarith [neg_abs_le (inner ℝ y y')]
      rw [inner_smul_left, inner_add_left, real_inner_self_eq_norm_sq, hy']
      simp only [conj_trivial]
      exact mul_nonneg (by positivity) (by nlinarith)

theorem r26t8a_p06_seg {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p q : E} {s : ℝ}
    (hs : 0 < s) (hp : ‖p‖ = s) (hq : ‖q‖ = s) (hpq : 0 ≤ inner ℝ p q) :
    (∀ w ∈ segment ℝ p q, s / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ s) ∧ ‖p - q‖ ≤ 2 * s := by
  refine ⟨fun w hw => ?_, ?_⟩
  · obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hw
    constructor
    · have hsq : ‖α • p + β • q‖ ^ 2 = α ^ 2 * s ^ 2 + β ^ 2 * s ^ 2 + 2 * α * β * inner ℝ p q := by
        rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right, hp, hq,
          Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ]
        simp only [conj_trivial]
        ring
      have h1 : (s / 2) ^ 2 ≤ ‖α • p + β • q‖ ^ 2 := by
        rw [hsq]
        have h0 : 0 ≤ α * β * inner ℝ p q := mul_nonneg (mul_nonneg hα hβ) hpq
        have hab : 1 / 2 ≤ α ^ 2 + β ^ 2 := by
          have : β = 1 - α := by linarith
          subst this; nlinarith [sq_nonneg (2 * α - 1)]
        nlinarith [mul_le_mul_of_nonneg_right hab (sq_nonneg s)]
      exact le_of_sq_le_sq (by simpa using h1) (norm_nonneg _)
    · calc ‖α • p + β • q‖ ≤ ‖α • p‖ + ‖β • q‖ := norm_add_le _ _
        _ = s := by
          rw [norm_smul, norm_smul, hp, hq, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ]
          nlinarith
  · have : ‖p - q‖ ^ 2 ≤ (2 * s) ^ 2 := by
      rw [norm_sub_sq_real, hp, hq]
      nlinarith
    exact le_of_sq_le_sq (by simpa using this) (by positivity)

theorem r26t8a_p06_dir {d : ℕ} (hd : 2 ≤ d) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : Euc d → V) (a : ℝ) (b : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdiff : ∀ y : Euc d, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 → DifferentiableAt ℝ G y)
    (hder : ∀ y : Euc d, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 →
      ‖fderiv ℝ G y‖ ≤ B * ‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b)
    {s : ℝ} (hs : 0 < s) (hs2 : s ≤ 1 / 2) (y y' : Euc d) (hy : ‖y‖ = s) (hy' : ‖y'‖ = s) :
    ‖G y - G y'‖ ≤ 2 ^ (b + 2) * 2 ^ |a - 1| * B * (s ^ a * (1 + |Real.log s|) ^ b) := by
  obtain ⟨e, he, h1, h2⟩ := r26t8a_p06_mid d hd y y' hs hy hy'
  set C : ℝ := B * 2 ^ |a - 1| * s ^ (a - 1) * (2 ^ b * (1 + |Real.log s|) ^ b) with hC
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ w : Euc d, s / 2 ≤ ‖w‖ → ‖w‖ ≤ s → ‖fderiv ℝ G w‖ ≤ C := by
    intro w hw1 hw2
    have hw0 : 0 < ‖w‖ := lt_of_lt_of_le (by positivity) hw1
    refine (hder w hw0 (hw2.trans hs2)).trans ?_
    have p1 := r26t8a_p06_pw1 a (l := s / 2) (s := ‖w‖) (by positivity) hw1 (by linarith)
    have p2 := r26t8a_p06_pw2 b (l := s / 2) (s := ‖w‖) (by positivity) hw1 (by linarith)
    have p3 := r26t8a_p06_pw3 b 1 (r := s) hs (by linarith)
    have e1 : 2 * (s / 2) = s := by ring
    rw [e1] at p1
    have p3' : (1 + |Real.log (s / 2)|) ^ b ≤ 2 ^ b * (1 + |Real.log s|) ^ b := by
      have := p3
      rw [pow_one] at this
      rw [show s / 2 = 1 / 2 * s by ring]
      norm_num at this ⊢
      exact this
    rw [hC]
    calc B * ‖w‖ ^ (a - 1) * (1 + |Real.log ‖w‖|) ^ b
        ≤ B * (2 ^ |a - 1| * s ^ (a - 1)) * (2 ^ b * (1 + |Real.log s|) ^ b) :=
          mul_le_mul (mul_le_mul_of_nonneg_left p1 hB) (p2.trans p3') (by positivity) (by positivity)
      _ = _ := by ring
  have hmv : ∀ p q : Euc d, ‖p‖ = s → ‖q‖ = s → 0 ≤ inner ℝ p q → ‖G p - G q‖ ≤ C * (2 * s) := by
    intro p q hp hq hpq
    obtain ⟨hseg, hdist⟩ := r26t8a_p06_seg hs hp hq hpq
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := G) (s := segment ℝ q p)
      (x := q) (y := p)
      (fun w hw => by
        have hw' : w ∈ segment ℝ p q := by rwa [segment_symm] at hw
        exact hdiff w (lt_of_lt_of_le (by positivity) (hseg w hw').1) ((hseg w hw').2.trans hs2))
      (fun w hw => by
        have hw' : w ∈ segment ℝ p q := by rwa [segment_symm] at hw
        exact hbound w (hseg w hw').1 (hseg w hw').2)
      (convex_segment _ _) (left_mem_segment _ _ _) (right_mem_segment _ _ _)
    calc ‖G p - G q‖ ≤ C * ‖p - q‖ := this
      _ ≤ C * (2 * s) := mul_le_mul_of_nonneg_left hdist hC0
  have hq1 := hmv y e hy he h1
  have hq2 := hmv y' e hy' he (by rw [real_inner_comm]; exact h2)
  calc ‖G y - G y'‖ = ‖(G y - G e) + (G e - G y')‖ := by congr 1; abel
    _ ≤ ‖G y - G e‖ + ‖G e - G y'‖ := norm_add_le _ _
    _ ≤ C * (2 * s) + C * (2 * s) := by
        refine add_le_add hq1 ?_
        rw [norm_sub_rev]; exact hq2
    _ = 2 ^ (b + 2) * 2 ^ |a - 1| * B * (s ^ a * (1 + |Real.log s|) ^ b) := by
        have hsa : s ^ (a - 1) * s = s ^ a := by
          rw [← Real.rpow_add_one hs.ne']; congr 1; ring
        rw [hC, pow_add]
        calc _ = B * 2 ^ |a - 1| * (s ^ (a - 1) * s) * (2 ^ b * (1 + |Real.log s|) ^ b) * 4 := by ring
          _ = _ := by rw [hsa]; norm_num; ring

theorem r26t8a_p06_limit {d : ℕ} (hd : 2 ≤ d) {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V]
    (G : Euc d → V) {a : ℝ} (ha : 0 < a) (b : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdiff : ∀ y : Euc d, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 → DifferentiableAt ℝ G y)
    (hder : ∀ y : Euc d, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 →
      ‖fderiv ℝ G y‖ ≤ B * ‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b) :
    ∃ T : V, ∀ z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 →
      ‖G z - T‖ ≤ (2 ^ (b + 2) * 2 ^ |a - 1| * B + 2 * B * r26t8a_p06_K a b) *
        (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by
  set K := r26t8a_p06_K a b with hK
  have hK0 : 0 ≤ K := r26t8a_p06_K_nonneg a b
  set z0 : Euc d := (1 / 2 : ℝ) • EuclideanSpace.single (⟨0, by omega⟩ : Fin d) (1 : ℝ) with hz0
  have hz0n : ‖z0‖ = 1 / 2 := by
    rw [hz0, norm_smul]; simp
  have hrad : ∀ x : Euc d, 0 < ‖x‖ → ‖x‖ ≤ 1 / 2 → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖G x - G (t • x)‖ ≤ 2 * B * K * (‖x‖ ^ a * (1 + |Real.log ‖x‖|) ^ b) :=
    fun x hx hx2 t ht0 ht1 => r26t8a_p06_radial G ha b B hB hdiff hder x hx hx2 t ht0 ht1
  set c : ℕ → ℝ := fun N => ((1:ℝ) / 2) ^ N with hc
  set sq : ℕ → V := fun N => G (c N • z0) with hsq
  have hρ0 : 0 ≤ ((1:ℝ) / 2) ^ a := by positivity
  have hρ1 : ((1:ℝ) / 2) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  set ρ := ((1:ℝ) / 2) ^ a with hρ
  -- the Cauchy bound
  have hcn : ∀ M : ℕ, ‖c M • z0‖ = ((1:ℝ) / 2) ^ (M + 1) := by
    intro M; rw [norm_smul, hz0n, hc]; simp [pow_succ]
  set bM : ℕ → ℝ := fun M => 2 * B * K * (ρ * (((M : ℝ) + 2) ^ b * ρ ^ M)) with hbM
  have hbM0 : Tendsto bM atTop (𝓝 0) := by
    have h := (r26t8a_p06_summable b hρ0 hρ1).tendsto_atTop_zero
    have := (h.const_mul ρ).const_mul (2 * B * K)
    simpa [hbM] using this
  have hMN : ∀ M N : ℕ, M ≤ N → ‖sq M - sq N‖ ≤ bM M := by
    intro M N hMN
    have hx : 0 < ‖c M • z0‖ := by rw [hcn]; positivity
    have hx2 : ‖c M • z0‖ ≤ 1 / 2 := by
      rw [hcn]; calc ((1:ℝ) / 2) ^ (M + 1) ≤ ((1:ℝ) / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        _ = 1 / 2 := by norm_num
    have ht : c N = ((1:ℝ) / 2) ^ (N - M) * c M := by
      rw [hc]; simp only; rw [← pow_add]; congr 1; omega
    have := hrad (c M • z0) hx hx2 (((1:ℝ) / 2) ^ (N - M)) (by positivity)
      (pow_le_one₀ (by norm_num) (by norm_num))
    have e : (((1:ℝ) / 2) ^ (N - M)) • (c M • z0) = c N • z0 := by rw [smul_smul, ← ht]
    rw [e] at this
    refine this.trans ?_
    rw [hcn M, hbM]
    simp only
    have h1 : ((((1:ℝ) / 2) ^ (M + 1)) ^ a) = ρ * ρ ^ M := by
      rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
        Real.rpow_natCast, pow_succ]; ring
    have h2 := r26t8a_p06_pw3 b (M + 1) (r := 1) one_pos le_rfl
    simp only [mul_one, Real.log_one, abs_zero, add_zero, one_pow] at h2
    have h3 : (1 + |Real.log (((1:ℝ) / 2) ^ (M + 1))|) ^ b ≤ ((M : ℝ) + 2) ^ b := by
      refine h2.trans ?_
      push_cast
      rw [show (M : ℝ) + 1 + 1 = M + 2 by ring]
    calc 2 * B * K * ((((1:ℝ) / 2) ^ (M + 1)) ^ a * (1 + |Real.log (((1:ℝ) / 2) ^ (M + 1))|) ^ b)
        ≤ 2 * B * K * ((ρ * ρ ^ M) * ((M : ℝ) + 2) ^ b) := by
          rw [h1]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) (by positivity)
      _ = _ := by ring
  have hcau : CauchySeq sq := by
    refine cauchySeq_of_le_tendsto_0 (fun M => 2 * bM M) (fun n m N hn hm => ?_) (by simpa using hbM0.const_mul 2)
    calc dist (sq n) (sq m) ≤ dist (sq N) (sq n) + dist (sq N) (sq m) := dist_triangle_left _ _ _
      _ ≤ bM N + bM N := by
        rw [dist_eq_norm, dist_eq_norm]
        exact add_le_add (hMN N n hn) (hMN N m hm)
      _ = 2 * bM N := by ring
  obtain ⟨T, hT⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨T, fun z hz hz2 => ?_⟩
  set s := ‖z‖ with hs
  set q : Euc d := (2 * s) • z0 with hq
  have hqn : ‖q‖ = s := by rw [hq, norm_smul, hz0n, Real.norm_of_nonneg (by positivity)]; ring
  have hdir := r26t8a_p06_dir hd G a b B hB hdiff hder hz hz2 z q rfl hqn
  have hqT : ‖G q - T‖ ≤ 2 * B * K * (s ^ a * (1 + |Real.log s|) ^ b) := by
    have hev : ∀ᶠ N in atTop, ‖G q - sq N‖ ≤ 2 * B * K * (s ^ a * (1 + |Real.log s|) ^ b) := by
      have hlim : Tendsto c atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      filter_upwards [hlim.eventually (gt_mem_nhds (by positivity : (0:ℝ) < 2 * s))] with N hN
      have ht0 : 0 < c N / (2 * s) := by positivity
      have ht1 : c N / (2 * s) ≤ 1 := by rw [div_le_one (by positivity)]; exact hN.le
      have := hrad q (by rw [hqn]; exact hz) (by rw [hqn]; exact hz2) _ ht0 ht1
      rw [hqn] at this
      have e : (c N / (2 * s)) • q = c N • z0 := by
        rw [hq, smul_smul]; congr 1; field_simp
      rw [e] at this
      exact this
    have hcont : Tendsto (fun N => ‖G q - sq N‖) atTop (𝓝 ‖G q - T‖) :=
      (tendsto_const_nhds.sub hT).norm
    exact le_of_tendsto hcont hev
  calc ‖G z - T‖ = ‖(G z - G q) + (G q - T)‖ := by congr 1; abel
    _ ≤ ‖G z - G q‖ + ‖G q - T‖ := norm_add_le _ _
    _ ≤ _ := by
        have := add_le_add hdir hqT
        refine this.trans (le_of_eq ?_)
        ring

end HRS.MS.R26T8A
