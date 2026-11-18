import HRS.PDE.EnergyDrift

/-!
# Helpers for `energy_torus` (Prop 3.13, literal form) and `adjoint_torus_bound_of_regular`

All declarations live in the namespace `HRS.PDE.ET` to avoid clashes with the helper lemmas of
`EnergyEstimate.lean` (which imports this file).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.ET

variable {d : ℕ}

/-! ### Part I: the generator maps `H^{m+2}` to `H^m` -/

theorem sobWeight_nat_eq_sum' (m : ℕ) (k : Lattice d) :
    sobWeight (m : ℝ) k = ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) *
      ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) := by
  have h1 : sobWeight (m : ℝ) k = (1 + ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2) ^ m := by
    rw [sobWeight_natCast, four_pi_enorm_sq]
  rw [h1, one_add_sum_pow]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul]

/-- The constant of the product estimate. -/
def prodConst (d r : ℕ) (K : ℝ) : ℝ :=
  ∑ α ∈ multiIndices d r, (multinomialWeight r α : ℝ) *
    (((leibnizSet α).card : ℝ) * ∑ β ∈ leibnizSet α, ((binomW α β : ℝ) ^ 2) * K ^ 2)

theorem prodConst_nonneg (r : ℕ) (K : ℝ) : 0 ≤ prodConst d r K := by
  unfold prodConst
  exact Finset.sum_nonneg fun α _ => mul_nonneg (Nat.cast_nonneg _)
    (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun β _ => by positivity))

/-- Product estimate for a `C^r` function and a trigonometric polynomial (finite partial sums). -/
theorem sum_sq_mulCoeff_le (r : ℕ) (K : ℝ) (φ : Torus d → ℝ) (hφ : Torus.IsCk r φ)
    (hB : Torus.cbNorm r φ ≤ K) {n : ℕ} (c : Coeff d) (hc : IsTrigPoly n c)
    (S : Finset (Lattice d)) :
    ∑ k ∈ S, sobWeight (r : ℝ) k * ‖mulCoeff (coeffOf φ) c k‖ ^ 2 ≤
      prodConst d r K * hsNormSq (r : ℝ) c := by
  classical
  have hφ' : ContDiff ℝ (r : WithTop ℕ∞) (Torus.lift φ) := hφ
  have hMem : MemHs (r : ℝ) c := memHs_of_isTrigPolyE hc _
  set H := hsNormSq (r : ℝ) c with hH
  have hα : ∀ α ∈ multiIndices d r,
      ∑ k ∈ S, ‖multiDerivCoeff α (mulCoeff (coeffOf φ) c) k‖ ^ 2 ≤
        (((leibnizSet α).card : ℝ) * ∑ β ∈ leibnizSet α, ((binomW α β : ℝ) ^ 2) * K ^ 2) * H := by
    intro α hα
    have hαr : ∑ i, α i ≤ r := (Finset.mem_filter.mp hα).2
    -- term bound
    have hterm : ∀ β ∈ leibnizSet α,
        ∑ k ∈ S, ‖(binomW α β : ℂ) *
          mulCoeff (multiDerivCoeff β (coeffOf φ)) (multiDerivCoeff (α - β) c) k‖ ^ 2 ≤
        ((binomW α β : ℝ) ^ 2) * K ^ 2 * H := by
      intro β hβ
      have hβα := mem_leibnizSet.mp hβ
      have hsβ : ∑ i, β i ≤ r := le_trans (Finset.sum_le_sum fun i _ => hβα i) hαr
      obtain ⟨ψ, hψc, hψ, hψK⟩ := exists_derivFun φ r hφ' β hsβ
      have hK' : ∀ x, |ψ x| ≤ K := fun x => (hψK x).trans hB
      have h1 := l2_mul_le ψ hψc K hK' n (multiDerivCoeff (α - β) c)
        (isTrigPoly_multiDerivCoeff hc _) S
      rw [hψ] at h1
      have h2 : ∑ k ∈ boxFin d n, ‖multiDerivCoeff (α - β) c k‖ ^ 2 ≤ H := by
        refine sum_sq_multiDeriv_le (α - β) r ?_ c hMem _
        refine le_trans (Finset.sum_le_sum fun i _ => ?_) hαr
        exact Nat.sub_le_of_le_add (by have := hβα i; omega)
      calc ∑ k ∈ S, ‖(binomW α β : ℂ) *
            mulCoeff (multiDerivCoeff β (coeffOf φ)) (multiDerivCoeff (α - β) c) k‖ ^ 2
          = ((binomW α β : ℝ) ^ 2) * ∑ k ∈ S,
            ‖mulCoeff (multiDerivCoeff β (coeffOf φ)) (multiDerivCoeff (α - β) c) k‖ ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [norm_mul, Complex.norm_natCast, mul_pow]
        _ ≤ ((binomW α β : ℝ) ^ 2) * (K ^ 2 * H) := by
            refine mul_le_mul_of_nonneg_left (h1.trans ?_) (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
        _ = _ := by ring
    calc ∑ k ∈ S, ‖multiDerivCoeff α (mulCoeff (coeffOf φ) c) k‖ ^ 2
        ≤ ∑ k ∈ S, ((leibnizSet α).card : ℝ) * ∑ β ∈ leibnizSet α, ‖(binomW α β : ℂ) *
          mulCoeff (multiDerivCoeff β (coeffOf φ)) (multiDerivCoeff (α - β) c) k‖ ^ 2 := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [multiDerivCoeff_mulCoeff α _ c hc k]
          refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
          exact sq_sum_le_card_mul_sum_sq
      _ = ((leibnizSet α).card : ℝ) * ∑ β ∈ leibnizSet α, ∑ k ∈ S, ‖(binomW α β : ℂ) *
          mulCoeff (multiDerivCoeff β (coeffOf φ)) (multiDerivCoeff (α - β) c) k‖ ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ ((leibnizSet α).card : ℝ) * ∑ β ∈ leibnizSet α, ((binomW α β : ℝ) ^ 2) * K ^ 2 * H := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun β hβ => hterm β hβ)
            (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  calc ∑ k ∈ S, sobWeight (r : ℝ) k * ‖mulCoeff (coeffOf φ) c k‖ ^ 2
      = ∑ α ∈ multiIndices d r, (multinomialWeight r α : ℝ) *
          ∑ k ∈ S, ‖multiDerivCoeff α (mulCoeff (coeffOf φ) c) k‖ ^ 2 := by
        simp_rw [norm_sq_multiDerivCoeff, sobWeight_nat_eq_sum', Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun k _ => ?_
        ring
    _ ≤ ∑ α ∈ multiIndices d r, (multinomialWeight r α : ℝ) *
          ((((leibnizSet α).card : ℝ) * ∑ β ∈ leibnizSet α, ((binomW α β : ℝ) ^ 2) * K ^ 2) * H) :=
        Finset.sum_le_sum fun α hα' =>
          mul_le_mul_of_nonneg_left (hα α hα') (Nat.cast_nonneg _)
    _ = prodConst d r K * H := by
        unfold prodConst
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun α _ => ?_
        ring


/-! ### Elementary Sobolev-sequence facts -/

theorem memHs_add_sq {r : ℝ} {x y : Coeff d} (hx : MemHs r x) (hy : MemHs r y) :
    MemHs r (x + y) ∧ hsNormSq r (x + y) ≤ 2 * hsNormSq r x + 2 * hsNormSq r y := by
  have hle : ∀ k, sobWeight r k * ‖(x + y) k‖ ^ 2 ≤
      2 * (sobWeight r k * ‖x k‖ ^ 2) + 2 * (sobWeight r k * ‖y k‖ ^ 2) := by
    intro k
    have h1 : ‖(x + y) k‖ ^ 2 ≤ 2 * ‖x k‖ ^ 2 + 2 * ‖y k‖ ^ 2 := by
      have := norm_add_le (x k) (y k)
      simp only [Pi.add_apply]
      nlinarith [norm_nonneg (x k), norm_nonneg (y k), sq_nonneg (‖x k‖ - ‖y k‖),
        norm_nonneg (x k + y k)]
    have hw := sobWeight_nonnegE r k
    nlinarith [mul_le_mul_of_nonneg_left h1 hw]
  have hs : Summable fun k => 2 * (sobWeight r k * ‖x k‖ ^ 2) + 2 * (sobWeight r k * ‖y k‖ ^ 2) :=
    (hx.mul_left 2).add (hy.mul_left 2)
  have hm : MemHs r (x + y) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonnegE r k) (sq_nonneg _)) hle hs
  refine ⟨hm, ?_⟩
  calc hsNormSq r (x + y) ≤ ∑' k, (2 * (sobWeight r k * ‖x k‖ ^ 2) +
        2 * (sobWeight r k * ‖y k‖ ^ 2)) := hm.tsum_le_tsum hle hs
    _ = _ := by
        rw [(hx.mul_left 2).tsum_add (hy.mul_left 2), tsum_mul_left, tsum_mul_left]
        rfl


theorem memHs_neg {r : ℝ} {x : Coeff d} (hx : MemHs r x) : MemHs r (-x) := by
  simpa [MemHs] using hx

theorem hsNormSq_neg (r : ℝ) (x : Coeff d) : hsNormSq r (-x) = hsNormSq r x := by
  simp [hsNormSq]

theorem memHs_sub_sq {r : ℝ} {x y : Coeff d} (hx : MemHs r x) (hy : MemHs r y) :
    MemHs r (x - y) ∧ hsNormSq r (x - y) ≤ 2 * hsNormSq r x + 2 * hsNormSq r y := by
  have := memHs_add_sq hx (memHs_neg hy)
  rwa [hsNormSq_neg, ← sub_eq_add_neg] at this

/-- Cauchy–Schwarz for the `H^r` pairing. -/
theorem hsInner_summable_norm {r : ℝ} {a b : Coeff d} (ha : MemHs r a) (hb : MemHs r b) :
    Summable (fun k => ‖((sobWeight r k : ℝ) : ℂ) * (a k * conj (b k))‖) ∧
      ∑' k, ‖((sobWeight r k : ℝ) : ℂ) * (a k * conj (b k))‖ ≤
        Real.sqrt (hsNormSq r a) * Real.sqrt (hsNormSq r b) := by
  have hpt : ∀ k, ‖((sobWeight r k : ℝ) : ℂ) * (a k * conj (b k))‖ =
      (Real.sqrt (sobWeight r k) * ‖a k‖) * (Real.sqrt (sobWeight r k) * ‖b k‖) := by
    intro k
    have hw := sobWeight_nonnegE r k
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw,
      RCLike.norm_conj]
    have : Real.sqrt (sobWeight r k) * Real.sqrt (sobWeight r k) = sobWeight r k :=
      Real.mul_self_sqrt hw
    calc sobWeight r k * (‖a k‖ * ‖b k‖)
        = (Real.sqrt (sobWeight r k) * Real.sqrt (sobWeight r k)) * (‖a k‖ * ‖b k‖) := by
          rw [this]
      _ = _ := by ring
  have hX : ∀ S : Finset (Lattice d), ∑ k ∈ S, (Real.sqrt (sobWeight r k) * ‖a k‖) ^ 2 ≤
      (Real.sqrt (hsNormSq r a)) ^ 2 := by
    intro S
    rw [Real.sq_sqrt (hsNormSq_nonnegE r a)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) (sum_le_hsNormSq ha S)
    rw [mul_pow, Real.sq_sqrt (sobWeight_nonnegE r k)]
  have hY : ∀ S : Finset (Lattice d), ∑ k ∈ S, (Real.sqrt (sobWeight r k) * ‖b k‖) ^ 2 ≤
      (Real.sqrt (hsNormSq r b)) ^ 2 := by
    intro S
    rw [Real.sq_sqrt (hsNormSq_nonnegE r b)]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_)) (sum_le_hsNormSq hb S)
    rw [mul_pow, Real.sq_sqrt (sobWeight_nonnegE r k)]
  obtain ⟨h1, h2⟩ := summable_mul_of_sq_bound (fun k => Real.sqrt (sobWeight r k) * ‖a k‖)
    (fun k => Real.sqrt (sobWeight r k) * ‖b k‖)
    (fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (fun k => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) _ _ (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hX hY
  simp_rw [hpt]
  exact ⟨h1, h2⟩

theorem norm_hsInner_le {r : ℝ} {a b : Coeff d} (ha : MemHs r a) (hb : MemHs r b) :
    ‖hsInner r a b‖ ≤ Real.sqrt (hsNormSq r a) * Real.sqrt (hsNormSq r b) := by
  obtain ⟨h1, h2⟩ := hsInner_summable_norm ha hb
  exact (norm_tsum_le_tsum_norm h1).trans h2

theorem hsInner_summable {r : ℝ} {a b : Coeff d} (ha : MemHs r a) (hb : MemHs r b) :
    Summable (fun k => ((sobWeight r k : ℝ) : ℂ) * (a k * conj (b k))) :=
  Summable.of_norm (hsInner_summable_norm ha hb).1

theorem hsInner_sub_left {r : ℝ} {a a' b : Coeff d} (ha : MemHs r a) (ha' : MemHs r a')
    (hb : MemHs r b) : hsInner r (a - a') b = hsInner r a b - hsInner r a' b := by
  unfold hsInner
  rw [← (hsInner_summable ha hb).tsum_sub (hsInner_summable ha' hb)]
  refine tsum_congr fun k => ?_
  simp only [Pi.sub_apply]
  ring

theorem hsInner_sub_right {r : ℝ} {a b b' : Coeff d} (ha : MemHs r a) (hb : MemHs r b)
    (hb' : MemHs r b') : hsInner r a (b - b') = hsInner r a b - hsInner r a b' := by
  unfold hsInner
  rw [← (hsInner_summable ha hb).tsum_sub (hsInner_summable ha hb')]
  refine tsum_congr fun k => ?_
  simp only [Pi.sub_apply, map_sub]
  ring

theorem hsNormSq_deriv_le {r : ℝ} {c : Coeff d} (hc : MemHs (r + 1) c) (j : Fin d) :
    MemHs r (derivCoeff j c) ∧ hsNormSq r (derivCoeff j c) ≤ hsNormSq (r + 1) c := by
  have hle : ∀ k, sobWeight r k * ‖derivCoeff j c k‖ ^ 2 ≤ sobWeight (r + 1) k * ‖c k‖ ^ 2 := by
    intro k
    rw [sobWeight_add, mul_assoc]
    exact mul_le_mul_of_nonneg_left (norm_derivCoeff_sq_le j c k) (sobWeight_nonnegE r k)
  have hm : MemHs r (derivCoeff j c) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_nonnegE r k) (sq_nonneg _)) hle hc
  exact ⟨hm, hm.tsum_le_tsum hle hc⟩

theorem sum_sq_laplace_le {c : Coeff d} (r : ℝ) (hc : MemHs (r + 2) c) (S : Finset (Lattice d)) :
    ∑ k ∈ S, sobWeight r k * ‖laplaceCoeff c k‖ ^ 2 ≤ hsNormSq (r + 2) c := by
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_le_hsNormSq hc S)
  have hl : ‖laplaceCoeff c k‖ = 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 * ‖c k‖ := by
    unfold laplaceCoeff
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h2 : sobWeight (2 : ℝ) k = (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 := by
    unfold sobWeight; rw [Real.rpow_two]
  have hw : (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 ≤ sobWeight (2 : ℝ) k := by
    rw [h2]
    have : 0 ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
    nlinarith
  rw [sobWeight_add, hl, mul_pow]
  have hc2 : (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 * ‖c k‖ ^ 2 ≤ sobWeight (2 : ℝ) k * ‖c k‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hw (sq_nonneg _)
  calc sobWeight r k * ((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 * ‖c k‖ ^ 2)
      ≤ sobWeight r k * (sobWeight (2 : ℝ) k * ‖c k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hc2 (sobWeight_nonnegE r k)
    _ = _ := by ring

theorem sum_sq_gradRiesz_le (s : ℝ) (hsd : s ≤ d) (i : Fin d) (h : Coeff d) (r : ℝ)
    (S : Finset (Lattice d)) :
    ∑ k ∈ S, sobWeight r k * ‖gradRieszCoeff d s i h k‖ ^ 2 ≤
      |rieszConst d s| ^ 2 * ∑ k ∈ S, sobWeight (r + 1) k * ‖h k‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_gradRieszCoeff]
  have h1 := abs_rieszCoeff_mul_le s hsd k i
  have h0 : 0 ≤ 2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszCoeff d s k| * ‖h k‖) := by positivity
  have h2 : 2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszCoeff d s k| * ‖h k‖) ≤
      |rieszConst d s| * Lattice.jp k * ‖h k‖ := by
    calc _ = (|rieszCoeff d s k| * (2 * Real.pi * |((k i : ℤ) : ℝ)|)) * ‖h k‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have h3 := pow_le_pow_left₀ h0 h2 2
  rw [sobWeight_add, ← jp_sq]
  have hw := sobWeight_nonnegE r k
  calc sobWeight r k * (2 * Real.pi * |((k i : ℤ) : ℝ)| * (|rieszCoeff d s k| * ‖h k‖)) ^ 2
      ≤ sobWeight r k * ((|rieszConst d s| * Lattice.jp k * ‖h k‖) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 hw
    _ = _ := by ring


theorem cbNorm_mono' {a b : ℕ} (hab : a ≤ b) (φ : Torus d → ℝ) :
    Torus.cbNorm a φ ≤ Torus.cbNorm b φ := by
  unfold Torus.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ hab))
    (fun j _ _ => Real.iSup_nonneg fun _ => norm_nonneg _)

theorem isCk_mono' {a b : ℕ} (hab : a ≤ b) {φ : Torus d → ℝ} (h : Torus.IsCk b φ) :
    Torus.IsCk a φ := by
  unfold Torus.IsCk at h ⊢
  exact h.of_le (by exact_mod_cast hab)

theorem hsNormSq_trig_deriv_le {n : ℕ} {u : Coeff d} (hu : IsTrigPoly n u) (r : ℝ) (j : Fin d) :
    hsNormSq r (derivCoeff j u) ≤ hsNormSq (r + 1) u :=
  (hsNormSq_deriv_le (memHs_of_isTrigPolyE hu _) j).2

theorem sq_norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2).trans sq_sum_le_card_mul_sum_sq

/-- The generator is bounded `H^{m+2} → H^m` on trigonometric polynomials (partial sums). -/
theorem forwardGen_trig_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp m VB D.V →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (m + 3) ρ → Torus.cbNorm (m + 3) ρ ≤ Λ →
      ∀ (n : ℕ) (u : Coeff d), IsTrigPoly n u → ∀ S : Finset (Lattice d),
        ∑ k ∈ S, sobWeight (m : ℝ) k * ‖forwardGen D ρ u k‖ ^ 2 ≤
          (3 * D.invβ ^ 2 + K) * hsNormSq ((m : ℝ) + 2) u := by
  classical
  obtain ⟨B, hB⟩ := exists_driftFuns hd s hs0 hsd m MB Λ VB
  set rc : ℝ := |rieszConst d s| with hrc
  set P1 : ℝ := prodConst d m B with hP1
  set P2 : ℝ := prodConst d (m + 1) Λ with hP2
  have hP1n : 0 ≤ P1 := prodConst_nonneg _ _
  have hP2n : 0 ≤ P2 := prodConst_nonneg _ _
  have hdn : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨3 * ((d : ℝ) ^ 2 * P1 + (d : ℝ) ^ 4 * (MB ^ 2 * rc ^ 2 * P2)), by positivity, ?_⟩
  intro D hDs hM hV ρ hp hk hb n u hu S
  obtain ⟨b, hb1, hb2, hb3⟩ := hB D hDs hM hV ρ hp hk hb
  have hk' : Torus.IsCk ((m + 3 : ℕ)) ρ := isCk_cast hk
  have hrc' : |rieszConst d D.s| = rc := by rw [hDs]
  set H := hsNormSq ((m : ℝ) + 2) u with hHdef
  have hMem2 : MemHs ((m : ℝ) + 2) u := memHs_of_isTrigPolyE hu _
  have hH0 : 0 ≤ H := hsNormSq_nonnegE _ _
  have hder : ∀ j, IsTrigPoly n (derivCoeff j u) := fun j => hu.derivCoeff j
  -- the three pieces
  have hA : ∑ k ∈ S, sobWeight (m : ℝ) k * ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff u k‖ ^ 2 ≤
      D.invβ ^ 2 * H := by
    have := sum_sq_laplace_le (m : ℝ) hMem2 S
    calc _ = D.invβ ^ 2 * ∑ k ∈ S, sobWeight (m : ℝ) k * ‖laplaceCoeff u k‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (sq_nonneg _)
  have hBj : ∀ j, ∑ k ∈ S, sobWeight (m : ℝ) k *
      ‖mulCoeff (driftCoeff D ρ j) (derivCoeff j u) k‖ ^ 2 ≤ P1 * H := by
    intro j
    have h1 := sum_sq_mulCoeff_le m B (b j) (isCk_mono' (Nat.le_succ m) (hb1 j))
      ((cbNorm_mono' (Nat.le_succ m) _).trans (hb2 j)) (derivCoeff j u) (hder j) S
    rw [← hb3 j]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hP1n)
    refine (hsNormSq_trig_deriv_le hu (m : ℝ) j).trans (hsNormSq_mono (by linarith) hMem2)
  have hCij : ∀ i j, ∑ k ∈ S, sobWeight (m : ℝ) k * ‖((D.M j i : ℝ) : ℂ) *
      gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2 ≤
      MB ^ 2 * rc ^ 2 * P2 * H := by
    intro i j
    have hMj : |D.M j i| ≤ MB := hM j i
    have h1 := sum_sq_gradRiesz_le D.s D.hsd.le i (mulCoeff (coeffOf ρ) (derivCoeff j u)) (m : ℝ) S
    rw [hrc'] at h1
    have h2 : ∑ k ∈ S, sobWeight ((m : ℝ) + 1) k *
        ‖mulCoeff (coeffOf ρ) (derivCoeff j u) k‖ ^ 2 ≤ P2 * H := by
      have h3 := sum_sq_mulCoeff_le (m + 1) Λ ρ (isCk_mono' (by omega) hk')
        ((cbNorm_mono' (by omega) _).trans hb) (derivCoeff j u) (hder j) S
      push_cast at h3
      refine h3.trans (mul_le_mul_of_nonneg_left ?_ hP2n)
      have := hsNormSq_trig_deriv_le hu ((m : ℝ) + 1) j
      exact this.trans (le_of_eq (by rw [hHdef]; congr 1; ring))
    have hterm : ∀ k, sobWeight (m : ℝ) k * ‖((D.M j i : ℝ) : ℂ) *
        gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2 =
        |D.M j i| ^ 2 * (sobWeight (m : ℝ) k *
          ‖gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2) := by
      intro k
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]; ring
    simp_rw [hterm]
    rw [← Finset.mul_sum]
    calc |D.M j i| ^ 2 * ∑ k ∈ S, sobWeight (m : ℝ) k *
          ‖gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2
        ≤ MB ^ 2 * (rc ^ 2 * (P2 * H)) := by
          have h4 : |D.M j i| ^ 2 ≤ MB ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hMj 2
          have h5 : ∑ k ∈ S, sobWeight (m : ℝ) k *
              ‖gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2 ≤
              rc ^ 2 * (P2 * H) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg rc))
          have h6 : 0 ≤ ∑ k ∈ S, sobWeight (m : ℝ) k *
              ‖gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2 :=
            Finset.sum_nonneg fun k _ => mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)
          exact mul_le_mul h4 h5 h6 (sq_nonneg _)
      _ = _ := by ring
  -- pointwise decomposition
  set a : Lattice d → ℝ := fun k => ‖((D.invβ : ℝ) : ℂ) * laplaceCoeff u k‖ ^ 2 with ha
  set bj : Lattice d → Fin d → ℝ := fun k j =>
    ‖mulCoeff (driftCoeff D ρ j) (derivCoeff j u) k‖ ^ 2 with hbj
  set cij : Lattice d → Fin d → Fin d → ℝ := fun k i j => ‖((D.M j i : ℝ) : ℂ) *
        gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2 with hcij
  have hpt : ∀ k, ‖forwardGen D ρ u k‖ ^ 2 ≤
      3 * (a k + (d : ℝ) * ∑ j, bj k j + (d : ℝ) ^ 2 * ∑ i, ∑ j, cij k i j) := by
    intro k
    have e : forwardGen D ρ u k = ((D.invβ : ℝ) : ℂ) * laplaceCoeff u k + transportCoeff D ρ u k
        - nonlocalCoeff D ρ u k := rfl
    set a' := ((D.invβ : ℝ) : ℂ) * laplaceCoeff u k
    set bb := transportCoeff D ρ u k
    set cc := nonlocalCoeff D ρ u k
    have h1 : ‖forwardGen D ρ u k‖ ^ 2 ≤ 3 * (‖a'‖ ^ 2 + ‖bb‖ ^ 2 + ‖cc‖ ^ 2) := by
      rw [e]
      have := norm_sub_le (a' + bb) cc
      have := norm_add_le a' bb
      nlinarith [norm_nonneg a', norm_nonneg bb, norm_nonneg cc, norm_nonneg (a' + bb),
        norm_nonneg (a' + bb - cc), sq_nonneg (‖a'‖ - ‖bb‖), sq_nonneg (‖a'‖ - ‖cc‖),
        sq_nonneg (‖bb‖ - ‖cc‖)]
    have h2 : ‖bb‖ ^ 2 ≤ (d : ℝ) * ∑ j, bj k j := by
      have := sq_norm_sum_le (Finset.univ : Finset (Fin d))
        (fun j => mulCoeff (driftCoeff D ρ j) (derivCoeff j u) k)
      simpa [bb, transportCoeff, bj] using this
    have h3 : ‖cc‖ ^ 2 ≤ (d : ℝ) ^ 2 * ∑ i, ∑ j, cij k i j := by
      have hi : ∀ i : Fin d, ‖∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
          gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2 ≤
          (d : ℝ) * ∑ j, cij k i j := by
        intro i
        have := sq_norm_sum_le (Finset.univ : Finset (Fin d))
          (fun j => ((D.M j i : ℝ) : ℂ) *
            gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k)
        simpa [cij] using this
      have := sq_norm_sum_le (Finset.univ : Finset (Fin d))
        (fun i => ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
          gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k)
      simp only [Finset.card_univ, Fintype.card_fin] at this
      have h4 : ∑ i : Fin d, ‖∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
          gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2 ≤
          ∑ i : Fin d, (d : ℝ) * ∑ j, cij k i j :=
        Finset.sum_le_sum fun i _ => hi i
      rw [← Finset.mul_sum] at h4
      calc ‖cc‖ ^ 2 ≤ (d : ℝ) * ∑ i : Fin d, ‖∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
            gradRieszCoeff d D.s i (mulCoeff (coeffOf ρ) (derivCoeff j u)) k‖ ^ 2 := by
            simpa [cc, nonlocalCoeff] using this
        _ ≤ (d : ℝ) * ((d : ℝ) * ∑ i, ∑ j, cij k i j) :=
            mul_le_mul_of_nonneg_left h4 hdn
        _ = _ := by ring
    have h1' : ‖a'‖ ^ 2 = a k := rfl
    nlinarith [h1, h2, h3]
  -- sum up
  have hw := fun k => sobWeight_nonnegE (m : ℝ) (d := d) k
  calc ∑ k ∈ S, sobWeight (m : ℝ) k * ‖forwardGen D ρ u k‖ ^ 2
      ≤ ∑ k ∈ S, (3 * (sobWeight (m : ℝ) k * a k) +
          3 * (d : ℝ) * ∑ j, (sobWeight (m : ℝ) k * bj k j) +
          3 * (d : ℝ) ^ 2 * ∑ i, ∑ j, (sobWeight (m : ℝ) k * cij k i j)) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h := mul_le_mul_of_nonneg_left (hpt k) (hw k)
        refine h.trans (le_of_eq ?_)
        simp only [← Finset.mul_sum]
        ring
    _ = 3 * ∑ k ∈ S, sobWeight (m : ℝ) k * a k +
          3 * (d : ℝ) * ∑ j, ∑ k ∈ S, sobWeight (m : ℝ) k * bj k j +
          3 * (d : ℝ) ^ 2 * ∑ i, ∑ j, ∑ k ∈ S, sobWeight (m : ℝ) k * cij k i j := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          ← Finset.mul_sum, Finset.sum_comm]
        congr 2
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ ≤ 3 * (D.invβ ^ 2 * H) + 3 * (d : ℝ) * ∑ j : Fin d, (P1 * H) +
          3 * (d : ℝ) ^ 2 * ∑ i : Fin d, ∑ j : Fin d, (MB ^ 2 * rc ^ 2 * P2 * H) := by
        gcongr with j _ i _ j _
        · exact hBj j
        · exact hCij i j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


theorem tendsto_truncCoeff_coord (u : Coeff d) (k : Lattice d) :
    Tendsto (fun n : ℕ => truncCoeff n u k) atTop (𝓝 (u k)) := by
  obtain ⟨N, hN⟩ := exists_inBox k
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  simp [truncCoeff, hN n hn]

theorem isRealCoeff_truncCoeff {u : Coeff d} (hu : IsRealCoeff u) (n : ℕ) :
    IsRealCoeff (truncCoeff n u) := by
  intro k
  by_cases hk : InBox n k
  · have : InBox n (-k) := inBox_neg_iff.2 hk
    simp [truncCoeff, hk, this, hu k]
  · have : ¬ InBox n (-k) := fun h => hk (inBox_neg_iff.1 h)
    simp [truncCoeff, hk, this]

/-- Extension of the bound from trigonometric polynomials to `H^{m+2}`. -/
theorem forwardGen_hs_bound_of_trig (D : DynData d) (ρ : Torus d → ℝ) (m : ℕ) (K' : ℝ)
    (hK' : 0 ≤ K') (hρ0 : MemHs 0 (coeffOf ρ)) (hb : ∀ j, MemHs 0 (driftCoeff D ρ j))
    (htrig : ∀ (n : ℕ) (v : Coeff d), IsTrigPoly n v → ∀ S : Finset (Lattice d),
        ∑ k ∈ S, sobWeight (m : ℝ) k * ‖forwardGen D ρ v k‖ ^ 2 ≤
          K' * hsNormSq ((m : ℝ) + 2) v)
    (u : Coeff d) (hu : MemHs ((m : ℝ) + 2) u) :
    MemHs (m : ℝ) (forwardGen D ρ u) ∧
      hsNormSq (m : ℝ) (forwardGen D ρ u) ≤ K' * hsNormSq ((m : ℝ) + 2) u := by
  have hu1 : MemHs 1 u := hu.mono (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have hS : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight (m : ℝ) k * ‖forwardGen D ρ u k‖ ^ 2 ≤
      K' * hsNormSq ((m : ℝ) + 2) u := by
    intro S
    have hlim : Tendsto (fun n : ℕ => ∑ k ∈ S, sobWeight (m : ℝ) k *
        ‖forwardGen D ρ (truncCoeff n u) k‖ ^ 2) atTop
        (𝓝 (∑ k ∈ S, sobWeight (m : ℝ) k * ‖forwardGen D ρ u k‖ ^ 2)) := by
      refine tendsto_finsetSum S fun k _ => ?_
      refine Tendsto.const_mul _ (Tendsto.pow (Tendsto.norm ?_) 2)
      refine tendsto_forwardGen D ρ hρ0 hb (fun n : ℕ => truncCoeff n u) u
        (Real.sqrt (hsNormSq 1 u)) (Real.sqrt_nonneg _) ?_ (tendsto_truncCoeff_coord u) k
      refine Filter.Eventually.of_forall fun n T => ?_
      rw [Real.sq_sqrt (hsNormSq_nonnegE _ _)]
      refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_le_hsNormSq hu1 T)
      by_cases hk : InBox n k
      · simp [truncCoeff, hk]
      · simp [truncCoeff, hk]
        exact mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)
    refine le_of_tendsto' hlim fun n => ?_
    refine (htrig n (truncCoeff n u) (isTrigPoly_truncCoeff n u) S).trans ?_
    exact mul_le_mul_of_nonneg_left (hsNormSq_truncCoeff_le n hu) hK'
  exact memHs_of_sum_le hS


theorem coeff_memHs_zero_of_data {m : ℕ} {VB : ℝ} (D : DynData d) (ρ : Torus d → ℝ)
    (hk : Torus.IsCk (m + 3) ρ) (hV : VHyp m VB D.V) :
    MemHs 0 (coeffOf ρ) ∧ ∀ j, MemHs 0 (driftCoeff D ρ j) := by
  have hρ := memHs_one_coeffOf_cbNorm (m + 3) (by omega) ρ (isCk_cast hk)
  have hVV := memHs_one_coeffOf_cbNorm (m + 3) (by omega) D.V (isCk_cast hV.1)
  exact ⟨hρ.1.mono (by norm_num), fun j => (driftCoeff_memHs0 D ρ hρ.1 hVV.1 j).1⟩

/-- **The forward generator maps `H^{m+2}` boundedly into `H^m`**, with a constant that is uniform
in the density (given the coefficient bounds). -/
theorem forwardGen_hs_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (MB Λ VB : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp m VB D.V →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → Torus.IsCk (m + 3) ρ → Torus.cbNorm (m + 3) ρ ≤ Λ →
      ∀ u : Coeff d, MemHs ((m : ℝ) + 2) u →
        MemHs (m : ℝ) (forwardGen D ρ u) ∧
          hsNormSq (m : ℝ) (forwardGen D ρ u) ≤ (3 * D.invβ ^ 2 + K) * hsNormSq ((m : ℝ) + 2) u := by
  obtain ⟨K, hK, hmain⟩ := forwardGen_trig_bound hd s hs0 hsd m MB Λ VB
  refine ⟨K, hK, fun D hDs hM hV ρ hp hk hb u hu => ?_⟩
  obtain ⟨h0, hdr⟩ := coeff_memHs_zero_of_data D ρ hk hV
  exact forwardGen_hs_bound_of_trig D ρ m _ (by positivity) h0 hdr
    (fun n v hv S => hmain D hDs hM hV ρ hp hk hb n v hv S) u hu

end HRS.PDE.ET
