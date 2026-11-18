import HRS.PDE.EnergyTorusSqrt

/-!
# Passing to the limit in the form inequality (Prop 3.13 (b))

The form inequality of `energy_form_estimate` for the truncations `P_n F` of a function
`F ∈ H^{m+2}` is transferred to `F` itself.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ET

variable {d : ℕ}

/-! ### Weak convergence of bounded sequences -/

theorem tendsto_hsInner_weak {r : ℝ} (u : ℕ → Coeff d) (u0 H : Coeff d) (B : ℝ) (hB0 : 0 ≤ B)
    (hbd : ∀ n, hsNormSq r (u n) ≤ B ^ 2) (hmem : ∀ n, MemHs r (u n)) (hH : MemHs r H)
    (hc : ∀ k, Tendsto (fun n => u n k) atTop (𝓝 (u0 k))) :
    Tendsto (fun n => hsInner r (u n) H) atTop (𝓝 (hsInner r u0 H)) := by
  have hv : Summable fun k => ‖(((Real.sqrt (sobWeight r k) : ℝ) : ℂ) * conj (H k))‖ ^ 2 :=
    hH.congr fun k => by
      rw [norm_mul, mul_pow, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (sobWeight_pos r k).le]
  have hmain : Tendsto (fun n => ∑' k, wseq r (u n) k *
      (((Real.sqrt (sobWeight r k) : ℝ) : ℂ) * conj (H k))) atTop
      (𝓝 (∑' k, wseq r u0 k * (((Real.sqrt (sobWeight r k) : ℝ) : ℂ) * conj (H k)))) := by
    refine tendsto_tsum_mul (fun n => wseq r (u n)) (wseq r u0) _ B hB0 ?_ hv ?_
    · refine Filter.Eventually.of_forall fun n S => ?_
      calc ∑ k ∈ S, ‖wseq r (u n) k‖ ^ 2 = ∑ k ∈ S, sobWeight r k * ‖u n k‖ ^ 2 :=
            Finset.sum_congr rfl fun k _ => norm_wseq_sq r _ k
        _ ≤ hsNormSq r (u n) := sum_le_hsNormSq (hmem n) S
        _ ≤ B ^ 2 := hbd n
    · intro k
      exact (hc k).const_mul _
  have hcongr : ∀ v : Coeff d, ∑' k, wseq r v k *
      (((Real.sqrt (sobWeight r k) : ℝ) : ℂ) * conj (H k)) = hsInner r v H := by
    intro v
    unfold hsInner
    refine tsum_congr fun k => ?_
    have hsq : (Real.sqrt (sobWeight r k) : ℂ) * (Real.sqrt (sobWeight r k) : ℂ) =
        (sobWeight r k : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (sobWeight_pos r k).le
    simp only [wseq]
    rw [← hsq]; ring
  simp only [hcongr] at hmain
  exact hmain

theorem tendsto_hsNormSq_sub_trunc (r : ℝ) (c : Coeff d) (hc : MemHs r c) :
    Tendsto (fun n : ℕ => hsNormSq r (c - truncCoeff n c)) atTop (𝓝 0) := by
  obtain ⟨-, h⟩ := truncCoeff_tendsto r c hc
  have h2 := h.pow 2
  rw [zero_pow two_ne_zero] at h2
  refine h2.congr fun n => ?_
  unfold hsNorm
  rw [Real.sq_sqrt (hsNormSq_nonnegE _ _)]
  

theorem hsNormSq_trunc_sub (r : ℝ) (c : Coeff d) (n : ℕ) :
    hsNormSq r (truncCoeff n c - c) = hsNormSq r (c - truncCoeff n c) := by
  rw [← neg_sub, hsNormSq_neg]

/-- **L1**: the pairing `Re⟨𝓛P_nG, P_nG⟩_{H^m}` converges for `G ∈ H^{m+2}`. -/
theorem tendsto_hsInner_gen_trunc (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) (D : DynData d) (hDs : D.s = s) (hM : MatBound MB D.M) (hV : VHyp m VB D.V)
    (ρ : Torus d → ℝ) (hp : IsProbDensity ρ) (hk : Torus.IsCk (m + 3) ρ)
    (hb : Torus.cbNorm (m + 3) ρ ≤ Λ) (G : Coeff d) (hG : MemHs ((m : ℝ) + 2) G) :
    Tendsto (fun n : ℕ => (hsInner (m : ℝ) (forwardGen D ρ (truncCoeff n G)) (truncCoeff n G)).re)
      atTop (𝓝 (hsInner (m : ℝ) (forwardGen D ρ G) G).re) := by
  obtain ⟨K, hK0, hK⟩ := forwardGen_hs_bound hd s hs0 hsd m MB Λ VB
  have hm2 : (m : ℝ) ≤ (m : ℝ) + 2 := by linarith
  have hG1 : MemHs 1 G := hG.mono (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have hGm : MemHs (m : ℝ) G := hG.mono hm2
  set P : ℕ → Coeff d := fun n => truncCoeff n G with hP
  have hPm2 : ∀ n, MemHs ((m : ℝ) + 2) (P n) := fun n =>
    memHs_of_isTrigPolyE (isTrigPoly_truncCoeff n G) _
  have hPm : ∀ n, MemHs (m : ℝ) (P n) := fun n => (hPm2 n).mono hm2
  have hP1 : ∀ n, MemHs 1 (P n) := fun n => (hPm2 n).mono
    (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have hgen := fun n => hK D hDs hM hV ρ hp hk hb (P n) (hPm2 n)
  set c3 := 3 * D.invβ ^ 2 + K with hc3
  have hc30 : 0 ≤ c3 := by positivity
  set B := Real.sqrt (c3 * hsNormSq ((m : ℝ) + 2) G) with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hbd : ∀ n, hsNormSq (m : ℝ) (forwardGen D ρ (P n)) ≤ B ^ 2 := by
    intro n
    rw [hBdef, Real.sq_sqrt (mul_nonneg hc30 (hsNormSq_nonnegE _ _))]
    refine (hgen n).2.trans (mul_le_mul_of_nonneg_left ?_ hc30)
    exact (truncCoeff_tendsto _ G hG).1 n
  -- coordinatewise convergence
  obtain ⟨h0, hdr⟩ := coeff_memHs_zero_of_data D ρ hk hV
  set Kc := hsNormSq 0 (coeffOf ρ) + ∑ j, hsNormSq 0 (driftCoeff D ρ j) with hKc
  have hKc0 : 0 ≤ Kc := add_nonneg (hsNormSq_nonnegE _ _)
    (Finset.sum_nonneg fun j _ => hsNormSq_nonnegE _ _)
  have hcoord : ∀ k, Tendsto (fun n => forwardGen D ρ (P n) k) atTop (𝓝 (forwardGen D ρ G k)) := by
    intro k
    refine tendsto_forwardGen_both (l := atTop) D (fun _ : ℕ => ρ) ρ Kc hKc0 (fun _ => h0)
      (fun _ => le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hsNormSq_nonnegE _ _))
      (fun _ => tendsto_const_nhds) (fun _ j => hdr j)
      (fun _ j => (Finset.single_le_sum (f := fun j => hsNormSq 0 (driftCoeff D ρ j))
        (fun j _ => hsNormSq_nonnegE _ _) (Finset.mem_univ j)).trans
        (le_add_of_nonneg_left (hsNormSq_nonnegE _ _)))
      (fun j q => tendsto_const_nhds) P G hP1 hG1 ?_ k
    have := tendsto_hsNormSq_sub_trunc 1 G hG1
    exact this.congr fun n => (hsNormSq_trunc_sub 1 G n).symm
  have hweak := tendsto_hsInner_weak (fun n => forwardGen D ρ (P n)) (forwardGen D ρ G) G B hB0 hbd
    (fun n => (hgen n).1) hGm hcoord
  -- the remainder
  have hrem : Tendsto (fun n => hsInner (m : ℝ) (forwardGen D ρ (P n)) (G - P n)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 := tendsto_hsNormSq_sub_trunc (m : ℝ) G hGm
    have h2 : Tendsto (fun n => B * Real.sqrt (hsNormSq (m : ℝ) (G - P n))) atTop (𝓝 0) := by
      have := ((Real.continuous_sqrt.tendsto 0).comp h1).const_mul B
      simpa using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h2
    obtain ⟨hmem, -⟩ := memHs_sub_sq hGm (hPm n)
    refine (norm_hsInner_le (hgen n).1 hmem).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    rw [hBdef]
    calc Real.sqrt (hsNormSq (m : ℝ) (forwardGen D ρ (P n))) ≤ Real.sqrt (B ^ 2) :=
          Real.sqrt_le_sqrt (hbd n)
      _ = B := Real.sqrt_sq hB0
  have hdiff := hweak.sub hrem
  rw [sub_zero] at hdiff
  refine (Complex.continuous_re.tendsto _ |>.comp hdiff).congr fun n => ?_
  simp only [Function.comp]
  congr 1
  rw [hsInner_sub_right (hgen n).1 hGm (hPm n)]
  ring


/-! ### Weighted sums along truncations -/

theorem tendsto_tsum_weight_trunc (w : Lattice d → ℝ) (hw0 : ∀ k, 0 ≤ w k) (r : ℝ)
    (hw : ∀ k, w k ≤ sobWeight r k) (c : Coeff d) (hc : MemHs r c) :
    Tendsto (fun n : ℕ => ∑' k, w k * ‖truncCoeff n c k‖ ^ 2) atTop
      (𝓝 (∑' k, w k * ‖c k‖ ^ 2)) := by
  refine tendsto_tsum_of_dominated_convergence (bound := fun k => sobWeight r k * ‖c k‖ ^ 2)
    hc (fun k => ?_) (Filter.Eventually.of_forall fun n k => ?_)
  · obtain ⟨N, hN⟩ := exists_inBox k
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [truncCoeff, hN n hn]
  · rw [Real.norm_of_nonneg (mul_nonneg (hw0 k) (sq_nonneg _))]
    by_cases hk : InBox n k
    · simp only [truncCoeff, hk, ite_true]
      exact mul_le_mul_of_nonneg_right (hw k) (sq_nonneg _)
    · simp only [truncCoeff, hk, ite_false, norm_zero]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)

theorem prod_nonneg_even (α : Fin d → ℕ) (k : Lattice d) :
    0 ≤ ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) :=
  Finset.prod_nonneg fun i _ => by rw [pow_mul]; positivity

theorem prod_le_sobWeight {m : ℕ} {α : Fin d → ℕ} (hα : α ∈ multiIndices d m) (k : Lattice d) :
    ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) ≤ sobWeight (m : ℝ) k := by
  rw [sobWeight_nat_eq_sum']
  have hw : (1 : ℝ) ≤ multinomialWeight m α := by exact_mod_cast one_le_multinomialWeight m α hα
  have hp := prod_nonneg_even α k
  calc ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)
      ≤ (multinomialWeight m α : ℝ) * ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) := by
        nlinarith
    _ ≤ _ := Finset.single_le_sum
        (f := fun α => (multinomialWeight m α : ℝ) * ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
        (fun α' _ => mul_nonneg (Nat.cast_nonneg _) (prod_nonneg_even α' k)) hα

theorem gradWeight_le {m : ℕ} {α : Fin d → ℕ} (hα : α ∈ multiIndices d m) (k : Lattice d) :
    (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) ≤
      sobWeight ((m : ℝ) + 1) k := by
  rw [sobWeight_add, sobWeight_one, mul_comm (sobWeight (m : ℝ) k)]
  have h1 := prod_le_sobWeight hα k
  have h2 := prod_nonneg_even α k
  have h3 : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
  calc (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)
      ≤ (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) :=
        mul_le_mul_of_nonneg_right (by linarith) h2
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by linarith)

theorem tendsto_gradDerivL2Sq_trunc {m : ℕ} {α : Fin d → ℕ} (hα : α ∈ multiIndices d m)
    (G : Coeff d) (hG : MemHs ((m : ℝ) + 1) G) :
    Tendsto (fun n : ℕ => gradDerivL2Sq α (truncCoeff n G)) atTop (𝓝 (gradDerivL2Sq α G)) := by
  unfold gradDerivL2Sq
  exact tendsto_tsum_weight_trunc (fun k => (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) *
    ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
    (fun k => mul_nonneg (by positivity) (prod_nonneg_even α k)) _ (gradWeight_le hα) G hG


/-! ### The retained dissipation -/

theorem multiDeriv_memHs_le {m : ℕ} {α : Fin d → ℕ} (hα : α ∈ multiIndices d m) {r : ℝ}
    {c : Coeff d} (hc : MemHs (r + m) c) :
    MemHs r (multiDerivCoeff α c) ∧ hsNormSq r (multiDerivCoeff α c) ≤ hsNormSq (r + m) c := by
  have hle : ∀ k, sobWeight r k * ‖multiDerivCoeff α c k‖ ^ 2 ≤
      sobWeight (r + m) k * ‖c k‖ ^ 2 := by
    intro k
    rw [norm_sq_multiDerivCoeff, sobWeight_add, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (sobWeight_nonnegE _ _)
    exact mul_le_mul_of_nonneg_right (prod_le_sobWeight hα k) (sq_nonneg _)
  have hnn : ∀ k, 0 ≤ sobWeight r k * ‖multiDerivCoeff α c k‖ ^ 2 := fun k =>
    mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)
  have hs : MemHs r (multiDerivCoeff α c) := Summable.of_nonneg_of_le hnn hle hc
  exact ⟨hs, hs.tsum_le_tsum hle hc⟩

theorem multiDerivCoeff_sub (α : Fin d → ℕ) (x y : Coeff d) :
    multiDerivCoeff α (x - y) = multiDerivCoeff α x - multiDerivCoeff α y := by
  funext k; simp [multiDerivCoeff, mul_sub]

theorem mulCoeff_sub_right {a x y : Coeff d} (ha : MemHs 0 a) (hx : MemHs 0 x) (hy : MemHs 0 y) :
    mulCoeff a (x - y) = mulCoeff a x - mulCoeff a y := by
  funext k
  simp only [mulCoeff, Pi.sub_apply, mul_sub]
  exact Summable.tsum_sub (summable_mulCoeff a x ha hx k) (summable_mulCoeff a y ha hy k)

theorem norm_mulCoeff_sub_le {b : Torus d → ℝ} (hb : Continuous b) {x y : Coeff d}
    (hx : MemHs 0 x) (hy : MemHs 0 y) (k : Lattice d) :
    ‖mulCoeff (coeffOf b) x k - mulCoeff (coeffOf b) y k‖ ≤
      Torus.supNorm b * Real.sqrt (hsNormSq 0 (x - y)) := by
  have hxy : MemHs 0 (x - y) := (memHs_sub_sq hx hy).1
  rw [← Pi.sub_apply, ← mulCoeff_sub_right (coeffOf_memHs_zero hb).1 hx hy]
  obtain ⟨hm, hm'⟩ := mulCoeff_l2_bound hb hxy
  have h1 : ‖(mulCoeff (coeffOf b) (x - y)) k‖ ^ 2 ≤ hsNormSq 0 (mulCoeff (coeffOf b) (x - y)) := by
    have := sobWeight_mul_sq_le_hsNormSq hm k
    rwa [sobWeight_zero, one_mul] at this
  have h2 : hsNormSq 0 (mulCoeff (coeffOf b) (x - y)) ≤
      (Torus.supNorm b * Real.sqrt (hsNormSq 0 (x - y))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hsNormSq_nonnegE _ _)]; exact hm'
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (supNorm_nonneg _) (Real.sqrt_nonneg _))).1
    (h1.trans h2)

theorem tendsto_mulCoeff_multiDeriv_trunc {m : ℕ} {α : Fin d → ℕ} (hα : α ∈ multiIndices d m)
    {b : Torus d → ℝ} (hb : Continuous b) {G : Coeff d} (hG : MemHs (m : ℝ) G) (k : Lattice d) :
    Tendsto (fun n : ℕ => mulCoeff (coeffOf b) (multiDerivCoeff α (truncCoeff n G)) k) atTop
      (𝓝 (mulCoeff (coeffOf b) (multiDerivCoeff α G) k)) := by
  have hPm : ∀ n, MemHs (m : ℝ) (truncCoeff n G) := fun n =>
    memHs_of_isTrigPolyE (isTrigPoly_truncCoeff n G) _
  have hz : ∀ n, MemHs 0 (multiDerivCoeff α (truncCoeff n G)) ∧ MemHs 0 (multiDerivCoeff α G) :=
    fun n => ⟨(multiDeriv_memHs_le hα (r := 0) (by simpa using hPm n)).1,
      (multiDeriv_memHs_le hα (r := 0) (by simpa using hG)).1⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := tendsto_hsNormSq_sub_trunc (m : ℝ) G hG
  have h2 : Tendsto (fun n : ℕ => Torus.supNorm b *
      Real.sqrt (hsNormSq 0 (multiDerivCoeff α (truncCoeff n G) - multiDerivCoeff α G))) atTop
      (𝓝 0) := by
    have hb' : ∀ n, hsNormSq 0 (multiDerivCoeff α (truncCoeff n G) - multiDerivCoeff α G) ≤
        hsNormSq (m : ℝ) (G - truncCoeff n G) := by
      intro n
      rw [← multiDerivCoeff_sub, ← hsNormSq_trunc_sub]
      have hmem : MemHs ((0 : ℝ) + m) (truncCoeff n G - G) := by
        simpa using (memHs_sub_sq (hPm n) hG).1
      simpa using (multiDeriv_memHs_le hα (r := 0) hmem).2
    have h3 : Tendsto (fun n : ℕ => hsNormSq 0 (multiDerivCoeff α (truncCoeff n G) -
        multiDerivCoeff α G)) atTop (𝓝 0) :=
      squeeze_zero (fun n => hsNormSq_nonnegE _ _) hb' h1
    have := ((Real.continuous_sqrt.tendsto 0).comp h3).const_mul (Torus.supNorm b)
    simpa using this
  exact squeeze_zero (fun n => norm_nonneg _)
    (fun n => norm_mulCoeff_sub_le hb (hz n).1 (hz n).2 k) h2


/-! ### Assembly of the limit -/

/-- The limit of the non-dissipative part of the form inequality. -/
theorem tendsto_formA (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) (D : DynData d) (hDs : D.s = s) (hM : MatBound MB D.M) (hV : VHyp m VB D.V)
    (ρ : Torus d → ℝ) (hp : IsProbDensity ρ) (hk : Torus.IsCk (m + 3) ρ)
    (hb : Torus.cbNorm (m + 3) ρ ≤ Λ) (Λm : ℝ) (G : Coeff d) (hG : MemHs ((m : ℝ) + 2) G) :
    Tendsto (fun n : ℕ => (hsInner (m : ℝ) (forwardGen D ρ (truncCoeff n G)) (truncCoeff n G)).re)
      atTop (𝓝 (hsInner (m : ℝ) (forwardGen D ρ G) G).re) ∧
    Tendsto (fun n : ℕ => Λm * hsNormSq (m : ℝ) (truncCoeff n G) -
        (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α (truncCoeff n G)) atTop
      (𝓝 (Λm * hsNormSq (m : ℝ) G - (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α G)) := by
  refine ⟨tendsto_hsInner_gen_trunc hd s hs0 hsd m MB Λ VB D hDs hM hV ρ hp hk hb G hG, ?_⟩
  have hm1 : MemHs ((m : ℝ) + 1) G := hG.mono (by linarith)
  have hm0 : MemHs (m : ℝ) G := hG.mono (by linarith)
  refine Tendsto.sub ((tendsto_hsNormSq_trunc _ G hm0).const_mul _) ?_
  refine (tendsto_finsetSum _ fun α hα => ?_).const_mul _
  exact tendsto_gradDerivL2Sq_trunc hα G hm1

theorem form_limit_nonR2 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) (D : DynData d) (hDs : D.s = s) (hM : MatBound MB D.M) (hV : VHyp m VB D.V)
    (ρ : Torus d → ℝ) (hp : IsProbDensity ρ) (hk : Torus.IsCk (m + 3) ρ)
    (hb : Torus.cbNorm (m + 3) ρ ≤ Λ) (Λm : ℝ) (G : Coeff d) (hG : MemHs ((m : ℝ) + 2) G)
    (hform : ∀ n : ℕ, (hsInner (m : ℝ) (forwardGen D ρ (truncCoeff n G)) (truncCoeff n G)).re ≤
      Λm * hsNormSq (m : ℝ) (truncCoeff n G) -
        (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α (truncCoeff n G)) :
    (hsInner (m : ℝ) (forwardGen D ρ G) G).re ≤ Λm * hsNormSq (m : ℝ) G -
      (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α G := by
  obtain ⟨h1, h2⟩ := tendsto_formA hd s hs0 hsd m MB Λ VB D hDs hM hV ρ hp hk hb Λm G hG
  exact le_of_tendsto_of_tendsto' h1 h2 hform

theorem form_limit_R2 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) (D : DynData d) (hDs : D.s = s) (hM : MatBound MB D.M) (hV : VHyp m VB D.V)
    (ρ : Torus d → ℝ) (hp : IsProbDensity ρ) (hk : Torus.IsCk (m + 3) ρ)
    (hb : Torus.cbNorm (m + 3) ρ ≤ Λ) (lam : Fin d → ℝ) (hlam : ∀ l, 0 ≤ lam l)
    (q : Fin d → Euc d) (Λm : ℝ) (G : Coeff d) (hG : MemHs ((m : ℝ) + 2) G)
    (hform : ∀ n : ℕ, WeightedDissipationFinite D m q ρ (truncCoeff n G) ∧
      (hsInner (m : ℝ) (forwardGen D ρ (truncCoeff n G)) (truncCoeff n G)).re ≤
      Λm * hsNormSq (m : ℝ) (truncCoeff n G) -
        (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α (truncCoeff n G) -
        (1 / 2) * weightedDissipation D m lam q ρ (truncCoeff n G)) :
    WeightedDissipationFinite D m q ρ G ∧
    (hsInner (m : ℝ) (forwardGen D ρ G) G).re ≤ Λm * hsNormSq (m : ℝ) G -
      (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α G -
        (1 / 2) * weightedDissipation D m lam q ρ G := by
  obtain ⟨h1, h2⟩ := tendsto_formA hd s hs0 hsd m MB Λ VB D hDs hM hV ρ hp hk hb Λm G hG
  have hm1 : MemHs ((m : ℝ) + 1) G := hG.mono (by linarith)
  have hm0 : MemHs (m : ℝ) G := hG.mono (by linarith)
  have hck2 : Torus.IsCk 2 ρ := isCk_mono' (a := 2) (b := m + 3) (by omega) (isCk_cast hk)
  have hcont : Continuous ρ := continuous_of_isCk (isCk_mono' (a := 1) (b := 2) (by omega) hck2)
  have hsqc : Continuous fun x => Real.sqrt (ρ x) := Real.continuous_sqrt.comp hcont
  have hb2 : Torus.cbNorm 2 ρ ≤ Λ := (cbNorm_mono' (a := 2) (b := m + 3) (by omega) ρ).trans hb
  set a : Coeff d := coeffOf fun x => Real.sqrt (ρ x) with ha
  -- the terms
  set T : (Fin d → ℕ) → Fin d → Coeff d → Lattice d → ℝ := fun α l c k =>
    symbolK d D.s (q l) k * ‖mulCoeff a (multiDerivCoeff α c) k‖ ^ 2 with hT
  have hT0 : ∀ α l c k, 0 ≤ T α l c k := fun α l c k =>
    mul_nonneg (symbolK_nonneg hd (hDs ▸ hs0) (hDs ▸ hsd) _ k) (sq_nonneg _)
  -- summability for G
  have hWG : WeightedDissipationFinite D m q ρ G := by
    intro α hα l
    have hc : MemHs 1 (multiDerivCoeff α G) :=
      (multiDeriv_memHs_le hα (r := 1) (by rwa [add_comm])).1
    exact summable_symbolK_sqrt hd (hDs ▸ hs0) (hDs ▸ hsd) (q l) hck2 hp.nonneg hb2 hc
  refine ⟨hWG, ?_⟩
  set wdS : Finset (Lattice d) → Coeff d → ℝ := fun S c =>
    ∑ α ∈ multiIndices d m, ∑ l, lam l * ∑ k ∈ S, T α l c k with hwdS
  -- finite parts are bounded by the full dissipation
  have hwd_le : ∀ n S, wdS S (truncCoeff n G) ≤ weightedDissipation D m lam q ρ (truncCoeff n G) := by
    intro n S
    unfold weightedDissipation
    refine Finset.sum_le_sum fun α hα => Finset.sum_le_sum fun l _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hlam l)
    exact ((hform n).1 α hα l).sum_le_tsum S fun k _ => hT0 α l _ k
  -- convergence of the finite parts
  have hwdS_lim : ∀ S, Tendsto (fun n : ℕ => wdS S (truncCoeff n G)) atTop (𝓝 (wdS S G)) := by
    intro S
    refine tendsto_finsetSum _ fun α hα => tendsto_finsetSum _ fun l _ => ?_
    refine (tendsto_finsetSum _ fun k _ => ?_).const_mul _
    exact ((tendsto_mulCoeff_multiDeriv_trunc hα hsqc hm0 k).norm.pow 2).const_mul _
  -- the inequality with a finite part
  have hS : ∀ S, (hsInner (m : ℝ) (forwardGen D ρ G) G).re + (1 / 2) * wdS S G ≤
      Λm * hsNormSq (m : ℝ) G - (D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α G := by
    intro S
    refine le_of_tendsto_of_tendsto' (h1.add ((hwdS_lim S).const_mul _)) h2 fun n => ?_
    have := (hform n).2
    have := hwd_le n S
    linarith
  -- passage to the limit over finite sets
  have hlim : Tendsto (fun S : Finset (Lattice d) => wdS S G) atTop
      (𝓝 (weightedDissipation D m lam q ρ G)) := by
    unfold weightedDissipation
    refine tendsto_finsetSum _ fun α hα => tendsto_finsetSum _ fun l _ => ?_
    exact ((hWG α hα l).hasSum).const_mul _
  have hfin := le_of_tendsto' (tendsto_const_nhds.add (hlim.const_mul (1 / 2 : ℝ))) hS
  linarith

end HRS.PDE.ET
