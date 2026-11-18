import HRS.MS.R26T8AP11kc
import HRS.MS.R26T8AP11jet

/-!
# S8.2 nonlocal layer: pointwise joint-jet bound for the truncated integrand (P11e, part 3b, piece B3)
`G v (x,y) = Kc(x-y-v) chi(v) chi(v/delta) F(y+v,y)`: for `v ≠ 0` it is `C^k` in `(x,y)`, vanishes for `|v| >= 2 delta`, and on a small
ball around `(x0,y0)` (`|x0-y0| >= 4 delta`) its jets of order `<= k` are bounded by `c |v|^(-s) 1_{|v| <= 2 delta}`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

/-- The truncated integrand as a function of the parameter `p = (x,y)`. -/
def r26t8a_G {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ) (δ : ℝ) (F : Euc d → Euc d → ℝ) (v : Euc d)
    (p : Euc d × Euc d) : ℝ :=
  r26t8a_Kc alpha chi δ (p.1 - p.2 - v) * (chi v * chi (δ⁻¹ • v) * F (p.2 + v) p.2)

theorem r26t8a_G_zero {d : ℕ} (alpha : ℝ) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (δ : ℝ) (hδ : 0 < δ)
    (F : Euc d → Euc d → ℝ) {v : Euc d} (hv : 2 * δ ≤ ‖v‖) : r26t8a_G alpha chi δ F v = fun _ => 0 := by
  funext p
  have h : ‖δ⁻¹ • v‖ ≥ 2 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le), inv_mul_eq_div, ge_iff_le, le_div_iff₀ hδ]
    linarith
  simp only [r26t8a_G, hchi.2.2.2.2 _ h, mul_zero, zero_mul]

theorem r26t8a_Fslice_contDiff {d : ℕ} (F : Euc d → Euc d → ℝ) {k : ℕ}
    (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2}) {v : Euc d} (hv : v ≠ 0) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun y : Euc d => F (y + v) y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hmem : (y + v, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := by
    show y + v ≠ y
    intro h; apply hv; simpa using h
  have hlin : ContDiff ℝ (k : WithTop ℕ∞) (fun y : Euc d => (y + v, y)) :=
    (contDiff_id.add contDiff_const).prodMk contDiff_id
  exact ContDiffAt.comp (g := Function.uncurry F) (f := fun y : Euc d => (y + v, y)) y (hF.contDiffAt (hopen.mem_nhds hmem)) hlin.contDiffAt

theorem r26t8a_norm_comp_clm {E G F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : G →L[ℝ] E) {f : E → F} {k : ℕ} (hf : ContDiff ℝ (k : WithTop ℕ∞) f) (x : G) {i : ℕ} (hi : i ≤ k) :
    ‖iteratedFDeriv ℝ i (f ∘ g) x‖ ≤ ‖iteratedFDeriv ℝ i f (g x)‖ * ‖g‖ ^ i := by
  rw [g.iteratedFDeriv_comp_right hf x (by exact_mod_cast hi)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem r26t8a_G_contDiff (d : ℕ) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d) (hd : 2 ≤ d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (F : Euc d → Euc d → ℝ) {k : ℕ}
    (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2}) {δ : ℝ} (hδ : 0 < δ) {v : Euc d} (hv : v ≠ 0) :
    ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_G alpha chi δ F v) := by
  have hK : ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_Kc alpha chi δ) :=
    (r26t8a_Kc_contDiff d hd alpha halpha had chi hchi hδ).of_le (by exact_mod_cast le_top)
  have h1 : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => r26t8a_Kc alpha chi δ (p.1 - p.2 - v)) :=
    hK.comp ((contDiff_fst.sub contDiff_snd).sub contDiff_const)
  have h2 : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => F (p.2 + v) p.2) :=
    (r26t8a_Fslice_contDiff F hF hv).comp contDiff_snd
  exact h1.mul (contDiff_const.mul h2)

theorem r26t8a_G_jet (d : ℕ) (hd : 2 ≤ d) (alpha : ℝ) (halpha : 0 < alpha) (had : alpha < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (k b : ℕ) (M sigma : ℝ) (hM : 0 ≤ M) (hsd : sigma < d) :
    ∃ s : ℝ, 0 < s ∧ s < d ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal k b M sigma A F →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ p0 : Euc d × Euc d, 4 * δ ≤ ‖p0.1 - p0.2‖ →
      ∃ c : ℝ, 0 ≤ c ∧ ∀ i ≤ k, ∀ p : Euc d × Euc d, ‖p - p0‖ ≤ δ / 2 → ∀ v : Euc d, v ≠ 0 →
        ‖iteratedFDeriv ℝ i (r26t8a_G alpha chi δ F v) p‖ ≤
          (closedBall (0 : Euc d) (2 * δ)).indicator (fun v => c * ‖v‖ ^ (-s)) v := by
  obtain ⟨s, hs0, hsd', hFj⟩ := r26t8a_loc_Fjet d k b M sigma hM hsd hd
  refine ⟨s, hs0, hsd', ?_⟩
  intro A hA F hF δ hδ hδ1 p0 hp0
  obtain ⟨CK, hCK0, hCK⟩ := r26t8a_Kc_jets d hd alpha halpha had chi hchi hδ k
  have hFj' := hFj A hA F hF p0.2
  choose! cj hcj0 hcj using hFj'
  set Cs : ℝ := ∑ j ∈ Finset.range (k + 1), cj j with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun j hj => hcj0 j (by rw [Finset.mem_range] at hj; omega)
  have hcjle : ∀ j ≤ k, cj j ≤ Cs := fun j hj =>
    Finset.single_le_sum (f := cj) (fun j hj => hcj0 j (by rw [Finset.mem_range] at hj; omega))
      (Finset.mem_range.2 (by omega))
  refine ⟨2 ^ k * (CK * 2 ^ k * Cs), by positivity, ?_⟩
  have hL : ‖(ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - ContinuousLinearMap.snd ℝ (Euc d) (Euc d))‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun p => ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
      _ ≤ 2 * ‖p‖ := by linarith [norm_fst_le p, norm_snd_le p]
  have hsnd : ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => by simpa using norm_snd_le p
  have hFc : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2} := hF.1
  intro i hi p hp v hv
  by_cases hvb : ‖v‖ ≤ 2 * δ
  swap
  · rw [r26t8a_G_zero alpha chi hchi δ hδ F (by linarith), Set.indicator_of_notMem (by simpa using hvb)]
    simp [iteratedFDeriv_fun_zero]
  rw [Set.indicator_of_mem (by simpa using hvb)]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hv2 : ‖v‖ ≤ 2 := by linarith
  have hp1 : ‖p.1 - p0.1‖ ≤ δ / 2 := (norm_fst_le (p - p0)).trans hp
  have hp2 : ‖p.2 - p0.2‖ ≤ δ / 2 := (norm_snd_le (p - p0)).trans hp
  have hKu : δ ≤ ‖p.1 - p.2 - v‖ := by
    have h1 : ‖p0.1 - p0.2‖ ≤ ‖p.1 - p.2‖ + ‖(p.1 - p0.1) - (p.2 - p0.2)‖ := by
      have : p0.1 - p0.2 = (p.1 - p.2) - ((p.1 - p0.1) - (p.2 - p0.2)) := by abel
      rw [this]; exact norm_sub_le _ _
    have h2 : ‖(p.1 - p0.1) - (p.2 - p0.2)‖ ≤ δ := by
      have := norm_sub_le (p.1 - p0.1) (p.2 - p0.2); linarith
    have h3 : ‖p.1 - p.2‖ ≤ ‖p.1 - p.2 - v‖ + ‖v‖ := by
      have := norm_add_le (p.1 - p.2 - v) v
      simpa using this
    linarith
  set Lm := ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - ContinuousLinearMap.snd ℝ (Euc d) (Euc d) with hLm
  have hLp : ∀ q : Euc d × Euc d, Lm q = q.1 - q.2 := fun q => by
    simp [hLm]
  set c1 : ℝ := chi v * chi (δ⁻¹ • v) with hc1d
  have hc1 : |c1| ≤ 1 := by
    have h1 := hchi.2.2.1 v
    have h2 := hchi.2.2.1 (δ⁻¹ • v)
    rw [hc1d, abs_of_nonneg (mul_nonneg h1.1 h2.1)]
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  have hFvc : ContDiff ℝ (k : WithTop ℕ∞) (fun y : Euc d => F (y + v) y) :=
    r26t8a_Fslice_contDiff F hFc hv
  have hKc : ContDiff ℝ (k : WithTop ℕ∞) (fun u : Euc d => r26t8a_Kc alpha chi δ (u - v)) :=
    ((r26t8a_Kc_contDiff d hd alpha halpha had chi hchi hδ).of_le (by exact_mod_cast le_top)).comp
      (contDiff_id.sub contDiff_const)
  have hgc : ContDiff ℝ (k : WithTop ℕ∞) (fun y : Euc d => c1 • F (y + v) y) := hFvc.const_smul c1
  have hG : r26t8a_G alpha chi δ F v =
      fun q => ((fun u : Euc d => r26t8a_Kc alpha chi δ (u - v)) ∘ Lm) q *
        ((fun y : Euc d => c1 • F (y + v) y) ∘ ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) q := by
    funext q
    simp only [r26t8a_G, Function.comp, hLp, ContinuousLinearMap.coe_snd', smul_eq_mul, hc1d]
  have hf0 : ∀ j ≤ k, ‖iteratedFDeriv ℝ j ((fun u : Euc d => r26t8a_Kc alpha chi δ (u - v)) ∘ Lm) p‖ ≤
      CK * 2 ^ k := by
    intro j hj
    have h1 := r26t8a_norm_comp_clm Lm hKc p hj
    rw [iteratedFDeriv_comp_sub (f := r26t8a_Kc alpha chi δ) j v (Lm p), hLp] at h1
    refine h1.trans ?_
    calc ‖iteratedFDeriv ℝ j (r26t8a_Kc alpha chi δ) (p.1 - p.2 - v)‖ * ‖Lm‖ ^ j ≤ CK * 2 ^ j :=
          mul_le_mul (hCK j hj _ hKu) ((pow_le_pow_left₀ (norm_nonneg _) hL j)) (by positivity) hCK0
      _ ≤ CK * 2 ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) hj) hCK0
  have hg0 : ∀ j ≤ k, ‖iteratedFDeriv ℝ j ((fun y : Euc d => c1 • F (y + v) y) ∘
      ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) p‖ ≤ Cs * ‖v‖ ^ (-s) := by
    intro j hj
    have h1 := r26t8a_norm_comp_clm (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) hgc p hj
    have e : iteratedFDeriv ℝ j (fun y : Euc d => c1 • F (y + v) y) ((ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) p) =
        c1 • iteratedFDeriv ℝ j (fun y : Euc d => F (y + v) y) p.2 :=
      iteratedFDeriv_const_smul_apply' (hFvc.contDiffAt.of_le (by exact_mod_cast hj))
    rw [e, norm_smul, Real.norm_eq_abs] at h1
    refine h1.trans ?_
    have h2 := hcj j hj p.2 (by linarith) v hvpos hv2
    have h3 : ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ^ j ≤ 1 := pow_le_one₀ (norm_nonneg _) hsnd
    have h4 : 0 ≤ ‖v‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
    calc |c1| * ‖iteratedFDeriv ℝ j (fun y : Euc d => F (y + v) y) p.2‖ *
          ‖ContinuousLinearMap.snd ℝ (Euc d) (Euc d)‖ ^ j ≤ 1 * (cj j * ‖v‖ ^ (-s)) * 1 :=
          mul_le_mul (mul_le_mul hc1 h2 (norm_nonneg _) zero_le_one) h3 (by positivity)
            (by have := hcj0 j hj; positivity)
      _ ≤ Cs * ‖v‖ ^ (-s) := by
          rw [one_mul, mul_one]; exact mul_le_mul_of_nonneg_right (hcjle j hj) h4
  have hmul := norm_iteratedFDeriv_mul_le
    (f := (fun u : Euc d => r26t8a_Kc alpha chi δ (u - v)) ∘ Lm)
    (g := (fun y : Euc d => c1 • F (y + v) y) ∘ ContinuousLinearMap.snd ℝ (Euc d) (Euc d))
    (N := (k : WithTop ℕ∞)) (hKc.comp Lm.contDiff) (hgc.comp (ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).contDiff)
    p (n := i) (by exact_mod_cast hi)
  rw [hG]
  refine hmul.trans ?_
  have h4 : 0 ≤ ‖v‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
  calc ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDeriv ℝ j ((fun u : Euc d => r26t8a_Kc alpha chi δ (u - v)) ∘ Lm) p‖ *
        ‖iteratedFDeriv ℝ (i - j) ((fun y : Euc d => c1 • F (y + v) y) ∘
          ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) p‖
      ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ((CK * 2 ^ k) * (Cs * ‖v‖ ^ (-s))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ i := by rw [Finset.mem_range] at hj; omega
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hf0 j (hj'.trans hi)) (hg0 (i - j) (by omega))
          (norm_nonneg _) (by positivity)) (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ i * ((CK * 2 ^ k) * (Cs * ‖v‖ ^ (-s))) := by
        rw [← Finset.sum_mul]
        congr 1
        exact_mod_cast Nat.sum_range_choose i
    _ ≤ 2 ^ k * (CK * 2 ^ k * Cs) * ‖v‖ ^ (-s) := by
        have h2 : (2 : ℝ) ^ i ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hi
        have : 2 ^ k * (CK * 2 ^ k * Cs) * ‖v‖ ^ (-s) = 2 ^ k * ((CK * 2 ^ k) * (Cs * ‖v‖ ^ (-s))) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h2 (by positivity)

end HRS.MS.R26T8A
