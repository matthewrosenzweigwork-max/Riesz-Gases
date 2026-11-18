import HRS.PDE.ForwardEq
import HRS.PDE.TorusCalculus
import HRS.Analysis.Category

/-!
# Appendix C helper lemmas: square-summable coefficient sequences, products and L2 bounds (Lemma C.5 (i))

Auxiliary results for `HRS/PDE/Toolbox.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- The product Haar measure on the torus (Mathlib's `volume` for `UnitAddTorus`). -/
abbrev haarT (d : ℕ) : Measure (Torus d) :=
  Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)

theorem volume_eq_haarT : (volume : Measure (Torus d)) = haarT d := Torus.volume_eq_pi_haar

theorem memLp_haarT_iff {F : Torus d → ℂ} : MemLp F 2 (haarT d) ↔ MemLp F 2 volume := by
  rw [volume_eq_haarT]

/-! ### Parseval for complex `L²` functions and realisation of `ℓ²` sequences -/

theorem coeffOf_eq_coeffOfC (b : Torus d → ℝ) :
    coeffOf b = coeffOfC (fun x => (b x : ℂ)) := rfl

theorem coeffOfC_apply (F : Torus d → ℂ) (k : Lattice d) :
    coeffOfC F k = UnitAddTorus.mFourierCoeff F k := rfl

theorem coeffOfC_eq_integral (F : Torus d → ℂ) (k : Lattice d) :
    coeffOfC F k = ∫ x, conj (Torus.mode k x) * F x ∂(haarT d) := by
  simp only [coeffOfC_apply, UnitAddTorus.mFourierCoeff, smul_eq_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show UnitAddTorus.mFourier (-k) x * F x = conj (Torus.mode k x) * F x
  rw [UnitAddTorus.mFourier_neg]; rfl

theorem coeffOfC_eq_integral' (F : Torus d → ℂ) (k : Lattice d) :
    coeffOfC F k = ∫ x, conj (Torus.mode k x) * F x := by
  rw [volume_eq_haarT]; exact coeffOfC_eq_integral F k

theorem coeffOfC_congr_ae {F G : Torus d → ℂ} (h : F =ᵐ[haarT d] G) :
    coeffOfC F = coeffOfC G := by
  funext k
  simp only [coeffOfC_apply, UnitAddTorus.mFourierCoeff]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  simp [hx]

theorem mFourierCoeff_toLp_eq {F : Torus d → ℂ} (hF : MemLp F 2 (haarT d)) :
    coeffOfC (hF.toLp F : Torus d → ℂ) = coeffOfC F :=
  coeffOfC_congr_ae (MemLp.coeFn_toLp hF)

theorem sobWeight_zeroC (k : Lattice d) : sobWeight 0 k = 1 := by
  simp [sobWeight]

theorem memHs_zero_iffC (c : Coeff d) : MemHs 0 c ↔ Summable fun k => ‖c k‖ ^ 2 := by
  simp [MemHs, sobWeight_zeroC]

theorem hsNormSq_zero (c : Coeff d) : hsNormSq 0 c = ∑' k, ‖c k‖ ^ 2 := by
  simp [hsNormSq, sobWeight_zeroC]

/-- Parseval for complex `L²` functions. -/
theorem hsNormSq_zero_coeffOfC (F : Torus d → ℂ) (hF : MemLp F 2 volume) :
    MemHs 0 (coeffOfC F) ∧ hsNormSq 0 (coeffOfC F) = ∫ x, ‖F x‖ ^ 2 := by
  have hF' : MemLp F 2 (haarT d) := memLp_haarT_iff.2 hF
  have h := UnitAddTorus.hasSum_sq_mFourierCoeff (hF'.toLp F)
  have h1 := mFourierCoeff_toLp_eq hF'
  have h1' : (fun i => ‖UnitAddTorus.mFourierCoeff (hF'.toLp F : Torus d → ℂ) i‖ ^ 2) =
      fun i => ‖coeffOfC F i‖ ^ 2 := by
    funext i; rw [← h1]; rfl
  rw [h1'] at h
  have hint : ∫ t, ‖(hF'.toLp F : Torus d → ℂ) t‖ ^ 2 ∂(haarT d) = ∫ x, ‖F x‖ ^ 2 ∂(haarT d) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hF'] with x hx
    rw [hx]
  have h2 : HasSum (fun k => ‖coeffOfC F k‖ ^ 2) (∫ x, ‖F x‖ ^ 2 ∂(haarT d)) := by
    rw [← hint]; exact h
  refine ⟨(memHs_zero_iffC _).2 h2.summable, ?_⟩
  rw [hsNormSq_zero, h2.tsum_eq, volume_eq_haarT]

theorem memℓp_two_of_memHs (c : Coeff d) (h : MemHs 0 c) :
    Memℓp c 2 := by
  refine memℓp_gen ?_
  simpa using (memHs_zero_iffC c).1 h

open Classical in
/-- A realisation (an `L²` representative) of the `ℓ²` sequence `c`; junk (`0`) if `c ∉ ℓ²`. -/
def ofCoeff (c : Coeff d) : Torus d → ℂ :=
  if h : MemHs 0 c then
    ((UnitAddTorus.mFourierBasis (d := Fin d)).repr.symm
      ⟨c, memℓp_two_of_memHs c h⟩ : Lp ℂ 2 (haarT d))
  else 0

theorem memLp_ofCoeff_haarT {c : Coeff d} (h : MemHs 0 c) : MemLp (ofCoeff c) 2 (haarT d) := by
  simp only [ofCoeff, h, ↓reduceDIte]
  exact Lp.memLp _

theorem memLp_ofCoeff {c : Coeff d} (h : MemHs 0 c) : MemLp (ofCoeff c) 2 volume :=
  memLp_haarT_iff.1 (memLp_ofCoeff_haarT h)

theorem coeffOfC_ofCoeff {c : Coeff d} (h : MemHs 0 c) : coeffOfC (ofCoeff c) = c := by
  funext k
  have e : ofCoeff c = ((UnitAddTorus.mFourierBasis (d := Fin d)).repr.symm
      ⟨c, memℓp_two_of_memHs c h⟩ : Lp ℂ 2 (haarT d)) := by
    simp only [ofCoeff, h, ↓reduceDIte]
  rw [e, coeffOfC_apply, ← UnitAddTorus.mFourierBasis_repr]
  simp

/-! ### Products with a continuous real function -/

theorem memLp_two_of_continuous {g : Torus d → ℂ} (hg : Continuous g) : MemLp g 2 volume :=
  hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem memLp_top_of_continuous {g : Torus d → ℂ} (hg : Continuous g) : MemLp g ⊤ volume :=
  hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem conj_coeffOfC (b : Torus d → ℝ) (m : Lattice d) : conj (coeffOf b m) = coeffOf b (-m) := by
  rw [coeffOf_eq_coeffOfC, coeffOfC_eq_integral', coeffOfC_eq_integral', ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Torus.mode_neg]

theorem norm_le_supNorm {b : Torus d → ℝ} (hb : Continuous b) (x : Torus d) :
    ‖b x‖ ≤ Torus.supNorm b :=
  le_ciSup (f := fun x => ‖b x‖) (isCompact_range hb.norm).bddAbove x

theorem supNorm_nonneg (b : Torus d → ℝ) : 0 ≤ Torus.supNorm b :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem memLp_mul_of_continuous {b : Torus d → ℝ} (hb : Continuous b) {F : Torus d → ℂ}
    (hF : MemLp F 2 volume) : MemLp (fun x => (b x : ℂ) * F x) 2 volume := by
  have h1 : MemLp (fun x => (b x : ℂ)) ⊤ volume :=
    memLp_top_of_continuous (Complex.continuous_ofReal.comp hb)
  exact h1.mul hF

/-- The key Parseval identity: `(bF)^(k) = ∑_j b̂(k-j) F̂(j)` (unconditionally summable). -/
theorem hasSum_coeffOfC_mul {b : Torus d → ℝ} (hb : Continuous b) {F : Torus d → ℂ}
    (hF : MemLp F 2 volume) (k : Lattice d) :
    HasSum (fun j => coeffOf b (k - j) * coeffOfC F j)
      (coeffOfC (fun x => (b x : ℂ) * F x) k) := by
  have hF' : MemLp F 2 (haarT d) := memLp_haarT_iff.2 hF
  set f : Torus d → ℂ := fun x => (b x : ℂ) * Torus.mode k x with hfdef
  have hfc : Continuous f :=
    (Complex.continuous_ofReal.comp hb).mul (Torus.continuous_mode k)
  have hf : MemLp f 2 (haarT d) := memLp_haarT_iff.2 (memLp_two_of_continuous hfc)
  have h := UnitAddTorus.hasSum_prod_mFourierCoeff (hf.toLp f) (hF'.toLp F)
  have e1 := mFourierCoeff_toLp_eq hf
  have e2 := mFourierCoeff_toLp_eq hF'
  have hcoef : ∀ j, coeffOfC f j = coeffOf b (j - k) := by
    intro j
    rw [coeffOf_eq_coeffOfC, coeffOfC_eq_integral', coeffOfC_eq_integral']
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have : Torus.mode (j - k) x = Torus.mode j x * conj (Torus.mode k x) := by
      rw [sub_eq_add_neg, Torus.mode_add, Torus.mode_neg]
    simp only [hfdef, this, map_mul, Complex.conj_conj]
    ring
  have hterm : ∀ j, conj (UnitAddTorus.mFourierCoeff (hf.toLp f : Torus d → ℂ) j) *
      UnitAddTorus.mFourierCoeff (hF'.toLp F : Torus d → ℂ) j =
      coeffOf b (k - j) * coeffOfC F j := by
    intro j
    have a1 : UnitAddTorus.mFourierCoeff (hf.toLp f : Torus d → ℂ) j = coeffOfC f j := by
      rw [← e1]; rfl
    have a2 : UnitAddTorus.mFourierCoeff (hF'.toLp F : Torus d → ℂ) j = coeffOfC F j := by
      rw [← e2]; rfl
    rw [a1, a2, hcoef, conj_coeffOfC, neg_sub]
  have hint : ∫ t, conj ((hf.toLp f : Torus d → ℂ) t) * (hF'.toLp F : Torus d → ℂ) t ∂(haarT d)
      = coeffOfC (fun x => (b x : ℂ) * F x) k := by
    rw [coeffOfC_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hF'] with x h1 h2
    rw [h1, h2]
    simp only [hfdef, map_mul, Complex.conj_ofReal]
    ring
  have h2 : HasSum (fun j => conj (UnitAddTorus.mFourierCoeff (hf.toLp f : Torus d → ℂ) j) *
      UnitAddTorus.mFourierCoeff (hF'.toLp F : Torus d → ℂ) j)
      (∫ t, conj ((hf.toLp f : Torus d → ℂ) t) * (hF'.toLp F : Torus d → ℂ) t ∂(haarT d)) := h
  simp_rw [hterm] at h2
  rwa [hint] at h2

theorem summable_mul_coeffOf {b : Torus d → ℝ} (hb : Continuous b) {F : Torus d → ℂ}
    (hF : MemLp F 2 volume) (k : Lattice d) :
    Summable fun j => coeffOf b (k - j) * coeffOfC F j :=
  (hasSum_coeffOfC_mul hb hF k).summable

/-- (B) The coefficient convolution with `b̂` is the coefficient sequence of the product. -/
theorem mulCoeff_coeffOfC_mul {b : Torus d → ℝ} (hb : Continuous b) {F : Torus d → ℂ}
    (hF : MemLp F 2 volume) :
    (∀ k, Summable fun j => coeffOf b (k - j) * coeffOfC F j) ∧
      mulCoeff (coeffOf b) (coeffOfC F) = coeffOfC (fun x => (b x : ℂ) * F x) := by
  refine ⟨summable_mul_coeffOf hb hF, ?_⟩
  funext k
  exact (hasSum_coeffOfC_mul hb hF k).tsum_eq

/-- (B) `L²` bound for multiplication by a continuous function. -/
theorem mulCoeff_l2_bound {b : Torus d → ℝ} (hb : Continuous b) {c : Coeff d} (hc : MemHs 0 c) :
    MemHs 0 (mulCoeff (coeffOf b) c) ∧
      hsNormSq 0 (mulCoeff (coeffOf b) c) ≤ Torus.supNorm b ^ 2 * hsNormSq 0 c := by
  set F := ofCoeff c with hFdef
  have hF : MemLp F 2 volume := memLp_ofCoeff hc
  have hFc : coeffOfC F = c := coeffOfC_ofCoeff hc
  have hmul := (mulCoeff_coeffOfC_mul hb hF).2
  rw [hFc] at hmul
  rw [hmul]
  have hbF := memLp_mul_of_continuous hb hF
  obtain ⟨h1, h2⟩ := hsNormSq_zero_coeffOfC _ hbF
  obtain ⟨h3, h4⟩ := hsNormSq_zero_coeffOfC F hF
  refine ⟨h1, ?_⟩
  rw [h2, ← hFc, h4, ← integral_const_mul]
  refine integral_mono hbF.norm.integrable_sq (hF.norm.integrable_sq.const_mul _) fun x => ?_
  simp only [norm_mul, Complex.norm_real]
  have := norm_le_supNorm hb x
  calc (‖b x‖ * ‖F x‖) ^ 2 = ‖b x‖ ^ 2 * ‖F x‖ ^ 2 := by ring
    _ ≤ Torus.supNorm b ^ 2 * ‖F x‖ ^ 2 := by
      gcongr

/-! ### H¹ and derivatives -/

theorem enorm_sq_eq_sumC (k : Lattice d) : Lattice.enorm k ^ 2 = ∑ j, ((k j : ℝ)) ^ 2 := by
  unfold Lattice.enorm Lattice.toEuc
  rw [EuclideanSpace.norm_sq_eq]
  simp

theorem sobWeight_one_eq (k : Lattice d) :
    sobWeight 1 k = 1 + ∑ j, (2 * Real.pi * (k j : ℝ)) ^ 2 := by
  unfold sobWeight
  rw [Real.rpow_one, enorm_sq_eq_sumC, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

theorem norm_derivCoeff_sq (j : Fin d) (c : Coeff d) (k : Lattice d) :
    ‖derivCoeff j c k‖ ^ 2 = (2 * Real.pi * (k j : ℝ)) ^ 2 * ‖c k‖ ^ 2 := by
  unfold derivCoeff
  rw [norm_mul, mul_pow]
  congr 1
  rw [norm_mul, norm_mul, mul_pow, mul_pow]
  simp [Complex.norm_real, abs_of_pos Real.pi_pos, mul_pow]
  
theorem sobWeight_one_mul_sq (c : Coeff d) (k : Lattice d) :
    sobWeight 1 k * ‖c k‖ ^ 2 = ‖c k‖ ^ 2 + ∑ j, ‖derivCoeff j c k‖ ^ 2 := by
  simp_rw [norm_derivCoeff_sq, sobWeight_one_eq, add_mul, one_mul, Finset.sum_mul]

theorem memHs_one_iff (c : Coeff d) :
    MemHs 1 c ↔ MemHs 0 c ∧ ∀ j, MemHs 0 (derivCoeff j c) := by
  simp only [MemHs, sobWeight_zeroC, one_mul]
  constructor
  · intro h
    have hle : ∀ k, 0 ≤ sobWeight 1 k * ‖c k‖ ^ 2 := fun k => by
      have : 0 ≤ sobWeight 1 k := by unfold sobWeight; positivity
      positivity
    refine ⟨?_, fun j => ?_⟩
    · refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) h
      rw [sobWeight_one_mul_sq]
      have : 0 ≤ ∑ j, ‖derivCoeff j c k‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
    · refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) h
      rw [sobWeight_one_mul_sq]
      have := Finset.single_le_sum (f := fun j => ‖derivCoeff j c k‖ ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j)
      linarith [sq_nonneg ‖c k‖]
  · rintro ⟨h0, h1⟩
    simp_rw [sobWeight_one_mul_sq]
    exact h0.add (summable_sum fun j _ => h1 j)

theorem hsNormSq_one_eq (c : Coeff d) (h : MemHs 1 c) :
    hsNormSq 1 c = hsNormSq 0 c + ∑ j, hsNormSq 0 (derivCoeff j c) := by
  obtain ⟨h0, h1⟩ := (memHs_one_iff c).1 h
  unfold hsNormSq
  simp_rw [sobWeight_zeroC, one_mul, sobWeight_one_mul_sq]
  rw [Summable.tsum_add ((memHs_zero_iffC c).1 h0) (summable_sum fun j _ => (memHs_zero_iffC _).1 (h1 j)),
    Summable.tsum_finsetSum fun j _ => (memHs_zero_iffC _).1 (h1 j)]

theorem coeffOf_partialDeriv_eq (j : Fin d) (b : Torus d → ℝ) (hb : Torus.IsCk 1 b) :
    coeffOf (Torus.partialDeriv j b) = derivCoeff j (coeffOf b) := by
  funext k
  exact funFourierCoeff_partialDeriv j b hb k

theorem isOpenQuotientMap_mk' : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  exact h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap

theorem continuous_of_lift' {E : Type*} [TopologicalSpace E] {f : Torus d → E}
    (h : Continuous (Torus.lift f)) : Continuous f :=
  isOpenQuotientMap_mk'.isQuotientMap.continuous_iff.2 h

theorem continuous_of_isCk {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) : Continuous b :=
  continuous_of_lift' hb.continuous

theorem cbNorm_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ)
    (φ : Torus d → E) : 0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem supNorm_le_cbNorm {b : Torus d → ℝ} (k : ℕ) (hb : Torus.IsCk k b) :
    Torus.supNorm b ≤ Torus.cbNorm k b := by
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ 0 (Torus.lift b) x‖) :=
    Torus.bddAbove_norm_iteratedFDeriv_lift 0 b (hb.of_le (by exact_mod_cast Nat.zero_le k))
  refine ciSup_le fun x => ?_
  have h1 : ‖b x‖ ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift b) y‖ := by
    refine le_trans ?_ (le_ciSup hbdd (Torus.rep x))
    rw [norm_iteratedFDeriv_zero]
    simp [Torus.lift, Torus.mk_rep]
  refine h1.trans ?_
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift b) y‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (Nat.succ_pos k))

theorem abs_partialDeriv_le {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) (j : Fin d) (x : Torus d) :
    |Torus.partialDeriv j b x| ≤ Torus.cbNorm 1 b := by
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ 1 (Torus.lift b) x‖) :=
    Torus.bddAbove_norm_iteratedFDeriv_lift 1 b (by exact_mod_cast hb)
  have h1 : |Torus.partialDeriv j b x| ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift b) y‖ := by
    refine le_trans ?_ (le_ciSup hbdd (Torus.rep x))
    rw [norm_iteratedFDeriv_one]
    have := (fderiv ℝ (Torus.lift b) (Torus.rep x)).le_opNorm (EuclideanSpace.single j (1 : ℝ))
    rw [PiLp.norm_single] at this
    simpa [Torus.partialDeriv] using this
  refine h1.trans ?_
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift b) y‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num))

theorem supNorm_partialDeriv_le {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) (j : Fin d) :
    Torus.supNorm (Torus.partialDeriv j b) ≤ Torus.cbNorm 1 b :=
  ciSup_le fun x => by simpa using abs_partialDeriv_le hb j x

theorem continuous_partialDeriv' {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) (j : Fin d) :
    Continuous (Torus.partialDeriv j b) := continuous_partialDeriv j b hb

theorem coeffOf_memHs_zero {g : Torus d → ℝ} (hg : Continuous g) :
    MemHs 0 (coeffOf g) ∧ hsNormSq 0 (coeffOf g) ≤ Torus.supNorm g ^ 2 := by
  have hm : MemLp (fun x => (g x : ℂ)) 2 volume :=
    memLp_two_of_continuous (Complex.continuous_ofReal.comp hg)
  obtain ⟨h1, h2⟩ := hsNormSq_zero_coeffOfC _ hm
  refine ⟨h1, ?_⟩
  rw [coeffOf_eq_coeffOfC, h2]
  calc ∫ x, ‖(g x : ℂ)‖ ^ 2 ≤ ∫ _ : Torus d, Torus.supNorm g ^ 2 := by
        refine integral_mono (hm.norm.integrable_sq) (integrable_const _) fun x => ?_
        simp only [Complex.norm_real]
        have := norm_le_supNorm hg x
        gcongr
    _ = Torus.supNorm g ^ 2 := by simp

/-- `H¹` regularity of the coefficients of a `C¹` function, with the bound
`‖b̂‖²_{H¹} ≤ (d+1) ‖b‖²_{C¹}`. -/
theorem memHs_one_coeffOf (b : Torus d → ℝ) (hb : Torus.IsCk 1 b) :
    MemHs 1 (coeffOf b) ∧ hsNormSq 1 (coeffOf b) ≤ ((d : ℝ) + 1) * Torus.cbNorm 1 b ^ 2 := by
  have hc := continuous_of_isCk hb
  have hS := cbNorm_nonneg 1 b
  have hder : ∀ j, MemHs 0 (derivCoeff j (coeffOf b)) ∧
      hsNormSq 0 (derivCoeff j (coeffOf b)) ≤ Torus.cbNorm 1 b ^ 2 := by
    intro j
    rw [← coeffOf_partialDeriv_eq j b hb]
    obtain ⟨h1, h2⟩ := coeffOf_memHs_zero (continuous_partialDeriv' hb j)
    refine ⟨h1, h2.trans ?_⟩
    have := supNorm_partialDeriv_le hb j
    have := supNorm_nonneg (Torus.partialDeriv j b)
    gcongr
  obtain ⟨h0, h0'⟩ := coeffOf_memHs_zero hc
  have hmem : MemHs 1 (coeffOf b) := (memHs_one_iff _).2 ⟨h0, fun j => (hder j).1⟩
  refine ⟨hmem, ?_⟩
  rw [hsNormSq_one_eq _ hmem]
  have h1 : hsNormSq 0 (coeffOf b) ≤ Torus.cbNorm 1 b ^ 2 := by
    refine h0'.trans ?_
    have := supNorm_le_cbNorm 1 hb
    have := supNorm_nonneg b
    gcongr
  have h2 : ∑ j, hsNormSq 0 (derivCoeff j (coeffOf b)) ≤ ∑ _j : Fin d, Torus.cbNorm 1 b ^ 2 :=
    Finset.sum_le_sum fun j _ => (hder j).2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  nlinarith

/-! ### Peetre's inequality -/

theorem toEuc_sub (k j : Lattice d) : Lattice.toEuc (k - j) = Lattice.toEuc k - Lattice.toEuc j := by
  ext i; simp [Lattice.toEuc]

theorem enorm_le_add (k j : Lattice d) :
    Lattice.enorm k ≤ Lattice.enorm j + Lattice.enorm (k - j) := by
  unfold Lattice.enorm
  rw [toEuc_sub]
  have := norm_le_norm_add_norm_sub' (Lattice.toEuc k) (Lattice.toEuc j)
  linarith [norm_sub_rev (Lattice.toEuc k) (Lattice.toEuc j)]

theorem enorm_neg (k : Lattice d) : Lattice.enorm (-k) = Lattice.enorm k := by
  unfold Lattice.enorm
  have : Lattice.toEuc (-k) = -Lattice.toEuc k := by ext i; simp [Lattice.toEuc]
  rw [this, norm_neg]

theorem enorm_sub_comm (k j : Lattice d) : Lattice.enorm (j - k) = Lattice.enorm (k - j) := by
  rw [← neg_sub k j, enorm_neg]

theorem sobWeight_base_pos (k : Lattice d) : 0 < 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by
  positivity

theorem sobWeight_base_le (k j : Lattice d) :
    1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤
      2 * (1 + 4 * Real.pi ^ 2 * Lattice.enorm j ^ 2) *
        (1 + 4 * Real.pi ^ 2 * Lattice.enorm (k - j) ^ 2) := by
  have h1 := enorm_le_add k j
  have h0 : 0 ≤ Lattice.enorm k := norm_nonneg _
  have h2 : Lattice.enorm k ^ 2 ≤ 2 * Lattice.enorm j ^ 2 + 2 * Lattice.enorm (k - j) ^ 2 := by
    nlinarith [sq_nonneg (Lattice.enorm j - Lattice.enorm (k - j)), norm_nonneg (Lattice.toEuc j),
      norm_nonneg (Lattice.toEuc (k - j))]
  set x := 4 * Real.pi ^ 2 * Lattice.enorm j ^ 2 with hx
  set y := 4 * Real.pi ^ 2 * Lattice.enorm (k - j) ^ 2 with hy
  have hx0 : 0 ≤ x := by positivity
  have hy0 : 0 ≤ y := by positivity
  have : 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤ 2 * x + 2 * y := by
    rw [hx, hy]; nlinarith [Real.pi_pos, sq_nonneg Real.pi]
  nlinarith [mul_nonneg hx0 hy0]

/-- Peetre's inequality. -/
theorem sobWeight_le_peetre (s : ℝ) (k j : Lattice d) :
    sobWeight s k ≤ 2 ^ |s| * sobWeight s j * sobWeight |s| (k - j) := by
  unfold sobWeight
  set A := 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 with hA
  set B := 1 + 4 * Real.pi ^ 2 * Lattice.enorm j ^ 2 with hB
  set C := 1 + 4 * Real.pi ^ 2 * Lattice.enorm (k - j) ^ 2 with hC
  have hApos : 0 < A := sobWeight_base_pos k
  have hBpos : 0 < B := sobWeight_base_pos j
  have hCpos : 0 < C := sobWeight_base_pos _
  have h1 : A ≤ 2 * B * C := sobWeight_base_le k j
  have h2 : B ≤ 2 * A * C := by
    have := sobWeight_base_le j k
    rw [enorm_sub_comm] at this
    exact this
  rcases le_or_gt 0 s with hs | hs
  · rw [abs_of_nonneg hs]
    calc A ^ s ≤ (2 * B * C) ^ s := Real.rpow_le_rpow hApos.le h1 hs
      _ = 2 ^ s * B ^ s * C ^ s := by
        rw [Real.mul_rpow (by positivity) hCpos.le, Real.mul_rpow (by norm_num) hBpos.le]
  · rw [abs_of_neg hs]
    have ht : 0 ≤ -s := by linarith
    have h3 : B ^ (-s) ≤ 2 ^ (-s) * A ^ (-s) * C ^ (-s) := by
      calc B ^ (-s) ≤ (2 * A * C) ^ (-s) := Real.rpow_le_rpow hBpos.le h2 ht
        _ = 2 ^ (-s) * A ^ (-s) * C ^ (-s) := by
          rw [Real.mul_rpow (by positivity) hCpos.le, Real.mul_rpow (by norm_num) hApos.le]
    have key : ∀ a e c g : ℝ, 0 < a → 0 < e → 0 ≤ c → 0 ≤ g → e ≤ c * a * g →
        a⁻¹ ≤ c * e⁻¹ * g := by
      intro a e c g ha he hc hg h
      calc a⁻¹ = e * (a⁻¹ * e⁻¹) := by field_simp
        _ ≤ (c * a * g) * (a⁻¹ * e⁻¹) := by gcongr
        _ = c * e⁻¹ * g := by field_simp
    have hAs : A ^ s = (A ^ (-s))⁻¹ := by rw [Real.rpow_neg hApos.le, inv_inv]
    have hBs : B ^ s = (B ^ (-s))⁻¹ := by rw [Real.rpow_neg hBpos.le, inv_inv]
    rw [hAs, hBs]
    exact key (A ^ (-s)) (B ^ (-s)) (2 ^ (-s)) (C ^ (-s)) (by positivity) (by positivity)
      (by positivity) (by positivity) (by linarith [h3, mul_comm (2 ^ (-s) * A ^ (-s)) (C ^ (-s))])

/-! ### Leibniz rule and products in `H¹` -/

theorem summable_coeffOf_mul_of_memHs {b : Torus d → ℝ} (hb : Continuous b) {c : Coeff d}
    (hc : MemHs 0 c) (k : Lattice d) : Summable fun j => coeffOf b (k - j) * c j := by
  have := summable_mul_coeffOf hb (memLp_ofCoeff hc) k
  rwa [coeffOfC_ofCoeff hc] at this

/-- Leibniz rule for coefficient convolution (pure algebra `k_j = (k-l)_j + l_j`). -/
theorem derivCoeff_mulCoeff_of_summable (a c : Coeff d) (j : Fin d)
    (h2 : ∀ k, Summable fun l => derivCoeff j a (k - l) * c l)
    (h3 : ∀ k, Summable fun l => a (k - l) * derivCoeff j c l) :
    derivCoeff j (mulCoeff a c) = mulCoeff (derivCoeff j a) c + mulCoeff a (derivCoeff j c) := by
  funext k
  have h2' := h2 k
  have h3' := h3 k
  simp only [derivCoeff, mulCoeff, Pi.add_apply] at h2' h3' ⊢
  rw [← tsum_mul_left, ← h2'.tsum_add h3']
  refine tsum_congr fun l => ?_
  have : (k j : ℂ) = ((k - l) j : ℂ) + (l j : ℂ) := by simp
  rw [this]; ring

/-- Leibniz rule for a `C¹` function times an `H¹` sequence. -/
theorem derivCoeff_mulCoeffC {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) {c : Coeff d}
    (hc : MemHs 1 c) (j : Fin d) :
    derivCoeff j (mulCoeff (coeffOf b) c) =
      mulCoeff (coeffOf (Torus.partialDeriv j b)) c + mulCoeff (coeffOf b) (derivCoeff j c) := by
  obtain ⟨hc0, hcj⟩ := (memHs_one_iff c).1 hc
  rw [coeffOf_partialDeriv_eq j b hb]
  refine derivCoeff_mulCoeff_of_summable _ _ j (fun k => ?_) (fun k => ?_)
  · have := summable_coeffOf_mul_of_memHs (continuous_partialDeriv' hb j) hc0 k
    rwa [coeffOf_partialDeriv_eq j b hb] at this
  · exact summable_coeffOf_mul_of_memHs (continuous_of_isCk hb) (hcj j) k

theorem hsNormSq_zero_add_le {x y : Coeff d} (hx : MemHs 0 x) (hy : MemHs 0 y) :
    MemHs 0 (x + y) ∧ hsNormSq 0 (x + y) ≤ 2 * hsNormSq 0 x + 2 * hsNormSq 0 y := by
  rw [memHs_zero_iffC] at hx hy ⊢
  have hle : ∀ k, ‖(x + y) k‖ ^ 2 ≤ 2 * ‖x k‖ ^ 2 + 2 * ‖y k‖ ^ 2 := by
    intro k
    have := norm_add_le (x k) (y k)
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg (x k), norm_nonneg (y k), sq_nonneg (‖x k‖ - ‖y k‖),
      norm_nonneg (x k + y k)]
  have hs : Summable fun k => ‖(x + y) k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) hle ((hx.mul_left 2).add (hy.mul_left 2))
  refine ⟨hs, ?_⟩
  rw [hsNormSq_zero, hsNormSq_zero, hsNormSq_zero, ← tsum_mul_left, ← tsum_mul_left,
    ← (hx.mul_left 2).tsum_add (hy.mul_left 2)]
  exact hs.tsum_le_tsum hle ((hx.mul_left 2).add (hy.mul_left 2))

theorem hsNormSq_zero_nonneg (c : Coeff d) : 0 ≤ hsNormSq 0 c := by
  rw [hsNormSq_zero]; exact tsum_nonneg fun _ => sq_nonneg _

/-- (E) Products in `H¹`: squared form. -/
theorem mulCoeff_memHs_one {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) {c : Coeff d}
    (hc : MemHs 1 c) :
    MemHs 1 (mulCoeff (coeffOf b) c) ∧
      hsNormSq 1 (mulCoeff (coeffOf b) c) ≤
        (2 * (d : ℝ) + 2) * Torus.cbNorm 1 b ^ 2 * hsNormSq 1 c := by
  obtain ⟨hc0, hcj⟩ := (memHs_one_iff c).1 hc
  have hcont := continuous_of_isCk hb
  have hS := cbNorm_nonneg 1 b
  set S := Torus.cbNorm 1 b with hSdef
  have hsup : Torus.supNorm b ≤ S := supNorm_le_cbNorm 1 hb
  have hsup0 := supNorm_nonneg b
  set w := mulCoeff (coeffOf b) c with hw
  obtain ⟨hw0, hw0'⟩ := mulCoeff_l2_bound hcont hc0
  have hA := hsNormSq_zero_nonneg c
  have hsq : ∀ t : ℝ, 0 ≤ t → t ≤ S → t ^ 2 ≤ S ^ 2 := fun t h0 h1 => by gcongr
  have hdw : ∀ j, MemHs 0 (derivCoeff j w) ∧
      hsNormSq 0 (derivCoeff j w) ≤
        2 * S ^ 2 * hsNormSq 0 c + 2 * S ^ 2 * hsNormSq 0 (derivCoeff j c) := by
    intro j
    rw [hw, derivCoeff_mulCoeffC hb hc j]
    obtain ⟨hP, hP'⟩ := mulCoeff_l2_bound (continuous_partialDeriv' hb j) hc0
    obtain ⟨hQ, hQ'⟩ := mulCoeff_l2_bound hcont (hcj j)
    obtain ⟨hPQ, hPQ'⟩ := hsNormSq_zero_add_le hP hQ
    refine ⟨hPQ, hPQ'.trans ?_⟩
    have e1 : Torus.supNorm (Torus.partialDeriv j b) ^ 2 ≤ S ^ 2 :=
      hsq _ (supNorm_nonneg _) (supNorm_partialDeriv_le hb j)
    have e2 : Torus.supNorm b ^ 2 ≤ S ^ 2 := hsq _ hsup0 hsup
    have hD := hsNormSq_zero_nonneg (derivCoeff j c)
    nlinarith [mul_le_mul_of_nonneg_right e1 hA, mul_le_mul_of_nonneg_right e2 hD]
  have hmem : MemHs 1 w := (memHs_one_iff _).2 ⟨hw0, fun j => (hdw j).1⟩
  refine ⟨hmem, ?_⟩
  rw [hsNormSq_one_eq _ hmem, hsNormSq_one_eq _ hc]
  have e0 : Torus.supNorm b ^ 2 ≤ S ^ 2 := hsq _ hsup0 hsup
  have h1 : hsNormSq 0 w ≤ S ^ 2 * hsNormSq 0 c :=
    hw0'.trans (mul_le_mul_of_nonneg_right e0 hA)
  have h2 : ∑ j, hsNormSq 0 (derivCoeff j w) ≤
      ∑ j, (2 * S ^ 2 * hsNormSq 0 c + 2 * S ^ 2 * hsNormSq 0 (derivCoeff j c)) :=
    Finset.sum_le_sum fun j _ => (hdw j).2
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum] at h2
  have hD : 0 ≤ ∑ j, hsNormSq 0 (derivCoeff j c) :=
    Finset.sum_nonneg fun j _ => hsNormSq_zero_nonneg _
  have hS2 : 0 ≤ S ^ 2 := sq_nonneg S
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_nonneg hS2 hA, mul_nonneg hS2 hD, mul_nonneg (mul_nonneg hS2 hD) hd0]

/-- The `H¹` product constant. -/
def prodConstH1 (d : ℕ) : ℝ := Real.sqrt (2 * (d : ℝ) + 2)

theorem prodConstH1_nonneg (d : ℕ) : 0 ≤ prodConstH1 d := Real.sqrt_nonneg _

theorem hsNorm_mulCoeff_one_le {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) {c : Coeff d}
    (hc : MemHs 1 c) :
    MemHs 1 (mulCoeff (coeffOf b) c) ∧
      hsNorm 1 (mulCoeff (coeffOf b) c) ≤ prodConstH1 d * Torus.cbNorm 1 b * hsNorm 1 c := by
  obtain ⟨h1, h2⟩ := mulCoeff_memHs_one hb hc
  refine ⟨h1, ?_⟩
  unfold hsNorm prodConstH1
  have hS := cbNorm_nonneg 1 b
  calc Real.sqrt (hsNormSq 1 (mulCoeff (coeffOf b) c))
      ≤ Real.sqrt ((2 * (d : ℝ) + 2) * Torus.cbNorm 1 b ^ 2 * hsNormSq 1 c) :=
        Real.sqrt_le_sqrt h2
    _ = Real.sqrt (2 * (d : ℝ) + 2) * Torus.cbNorm 1 b * Real.sqrt (hsNormSq 1 c) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hS]

/-! ### Cauchy–Schwarz between `H^s` and `H^{-s}` -/

theorem sobWeight_posC (s : ℝ) (k : Lattice d) : 0 < sobWeight s k :=
  Real.rpow_pos_of_pos (sobWeight_base_pos k) s

theorem sobWeight_sub_comm (s : ℝ) (j k : Lattice d) : sobWeight s (j - k) = sobWeight s (k - j) := by
  unfold sobWeight; rw [enorm_sub_comm]

theorem sobWeight_mul_neg (s : ℝ) (k : Lattice d) : sobWeight s k * sobWeight (-s) k = 1 := by
  unfold sobWeight
  rw [← Real.rpow_add (sobWeight_base_pos k)]
  simp

theorem summable_tsum_norm_mul_le (s : ℝ) {x y : Coeff d} (hx : MemHs s x) (hy : MemHs (-s) y) :
    Summable (fun j => ‖x j‖ * ‖y j‖) ∧ ∑' j, ‖x j‖ * ‖y j‖ ≤ hsNorm s x * hsNorm (-s) y := by
  set f : Lattice d → ℝ := fun j => Real.sqrt (sobWeight s j) * ‖x j‖ with hf
  set g : Lattice d → ℝ := fun j => Real.sqrt (sobWeight (-s) j) * ‖y j‖ with hg
  have hfg : ∀ j, f j * g j = ‖x j‖ * ‖y j‖ := by
    intro j
    have : Real.sqrt (sobWeight s j) * Real.sqrt (sobWeight (-s) j) = 1 := by
      rw [← Real.sqrt_mul (sobWeight_posC s j).le, sobWeight_mul_neg]; simp
    calc f j * g j = (Real.sqrt (sobWeight s j) * Real.sqrt (sobWeight (-s) j)) *
          (‖x j‖ * ‖y j‖) := by simp only [hf, hg]; ring
      _ = _ := by rw [this, one_mul]
  have hf2 : ∀ j, f j ^ (2 : ℝ) = sobWeight s j * ‖x j‖ ^ 2 := by
    intro j
    rw [Real.rpow_two]
    simp only [hf, mul_pow, Real.sq_sqrt (sobWeight_posC s j).le]
  have hg2 : ∀ j, g j ^ (2 : ℝ) = sobWeight (-s) j * ‖y j‖ ^ 2 := by
    intro j
    rw [Real.rpow_two]
    simp only [hg, mul_pow, Real.sq_sqrt (sobWeight_posC (-s) j).le]
  have hfs : Summable fun j => f j ^ (2 : ℝ) := by simp_rw [hf2]; exact hx
  have hgs : Summable fun j => g j ^ (2 : ℝ) := by simp_rw [hg2]; exact hy
  have hf0 : ∀ j, 0 ≤ f j := fun j => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hg0 : ∀ j, 0 ≤ g j := fun j => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  obtain ⟨h1, h2⟩ := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two hf0 hg0 hfs hgs
  simp_rw [hfg] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  simp_rw [hf2, hg2] at h2
  unfold hsNorm hsNormSq
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simp_rw [hf2, hg2]
  norm_num

/-! ### Lemma C.5 (i): the dual product bound -/

theorem summable_mulCoeff_dual {a : Torus d → ℝ} (ha : Torus.IsCk 1 a) {u : Coeff d}
    (hu : MemHs (-1) u) (k : Lattice d) : Summable fun j => coeffOf a (k - j) * u j := by
  obtain ⟨ha1, -⟩ := memHs_one_coeffOf a ha
  set p : Lattice d → ℝ := fun j => Real.sqrt (sobWeight 1 j) * ‖coeffOf a (k - j)‖ with hp
  set q : Lattice d → ℝ := fun j => Real.sqrt (sobWeight (-1) j) * ‖u j‖ with hq
  have hpq : ∀ j, ‖coeffOf a (k - j) * u j‖ = p j * q j := by
    intro j
    have : Real.sqrt (sobWeight 1 j) * Real.sqrt (sobWeight (-1) j) = 1 := by
      rw [← Real.sqrt_mul (sobWeight_posC 1 j).le]
      have := sobWeight_mul_neg 1 j
      rw [this]; simp
    calc ‖coeffOf a (k - j) * u j‖ = (Real.sqrt (sobWeight 1 j) * Real.sqrt (sobWeight (-1) j)) *
          (‖coeffOf a (k - j)‖ * ‖u j‖) := by rw [this, norm_mul, one_mul]
      _ = _ := by simp only [hp, hq]; ring
  have hp2 : ∀ j, p j ^ 2 ≤ 2 * sobWeight 1 k * (sobWeight 1 (k - j) * ‖coeffOf a (k - j)‖ ^ 2) := by
    intro j
    have h := sobWeight_le_peetre 1 j k
    rw [abs_one, Real.rpow_one, sobWeight_sub_comm] at h
    simp only [hp, mul_pow, Real.sq_sqrt (sobWeight_posC 1 j).le]
    have := sq_nonneg ‖coeffOf a (k - j)‖
    nlinarith
  have hq2 : ∀ j, q j ^ 2 = sobWeight (-1) j * ‖u j‖ ^ 2 := by
    intro j
    simp only [hq, mul_pow, Real.sq_sqrt (sobWeight_posC (-1) j).le]
  have hsa : Summable fun j => sobWeight 1 (k - j) * ‖coeffOf a (k - j)‖ ^ 2 :=
    (Equiv.subLeft k).summable_iff.2 ha1
  have hps : Summable fun j => p j ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) hp2 ((hsa.mul_left _))
  have hqs : Summable fun j => q j ^ 2 := by simp_rw [hq2]; exact hu
  have hdom : Summable fun j => (p j ^ 2 + q j ^ 2) := hps.add hqs
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_) hdom
  rw [hpq]
  nlinarith [sq_nonneg (p j - q j)]

theorem conj_coeffOf_sub (b : Torus d → ℝ) (j k : Lattice d) :
    conj (coeffOf b (j - k)) = coeffOf b (k - j) := by
  rw [conj_coeffOfC, neg_sub]

/-- Lemma C.5 (i), core estimate: `‖a u‖_{H^{-1}} ≤ C ‖a‖_{C¹} ‖u‖_{H^{-1}}`, by duality against
finitely supported test sequences. -/
theorem product_dual_aux {a : Torus d → ℝ} (ha : Torus.IsCk 1 a) {u : Coeff d}
    (hu : MemHs (-1) u) :
    MemHs (-1) (mulCoeff (coeffOf a) u) ∧
      hsNorm (-1) (mulCoeff (coeffOf a) u) ≤
        prodConstH1 d * Torus.cbNorm 1 a * hsNorm (-1) u := by
  classical
  have hsum := summable_mulCoeff_dual ha hu
  set w := mulCoeff (coeffOf a) u with hw
  set A := prodConstH1 d * Torus.cbNorm 1 a * hsNorm (-1) u with hA
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (prodConstH1_nonneg d) (cbNorm_nonneg 1 a))
    (Real.sqrt_nonneg _)
  have hnn : ∀ k, 0 ≤ sobWeight (-1) k * ‖w k‖ ^ 2 := fun k =>
    mul_nonneg (sobWeight_posC _ k).le (sq_nonneg _)
  have key : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight (-1) k * ‖w k‖ ^ 2 ≤ A ^ 2 := by
    intro S
    set X := ∑ k ∈ S, sobWeight (-1) k * ‖w k‖ ^ 2 with hX
    have hXn : 0 ≤ X := Finset.sum_nonneg fun k _ => hnn k
    set φ : Coeff d := fun k => if k ∈ S then ((sobWeight (-1) k : ℝ) : ℂ) * w k else 0 with hφ
    have hφsupp : ∀ k ∉ S, φ k = 0 := fun k hk => by simp [hφ, hk]
    have hφ1 : MemHs 1 φ :=
      summable_of_ne_finset_zero (s := S) (fun k hk => by simp [hφsupp k hk])
    have hnorm : hsNormSq 1 φ = X := by
      unfold hsNormSq
      rw [tsum_eq_sum (s := S) (fun k hk => by simp [hφsupp k hk])]
      refine Finset.sum_congr rfl fun k hk => ?_
      have h1 := sobWeight_mul_neg 1 k
      simp only [hφ, hk, ite_true, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (sobWeight_posC (-1) k).le]
      linear_combination (sobWeight (-1) k * ‖w k‖ ^ 2) * h1
    obtain ⟨hM1, hM⟩ := hsNorm_mulCoeff_one_le ha hφ1
    set M := mulCoeff (coeffOf a) φ with hMdef
    have hpair : ∑ k ∈ S, w k * conj (φ k) = (X : ℂ) := by
      rw [hX]; push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [hφ, hk, ite_true, map_mul, Complex.conj_ofReal]
      rw [show w k * (((sobWeight (-1) k : ℝ) : ℂ) * conj (w k)) =
        ((sobWeight (-1) k : ℝ) : ℂ) * (w k * conj (w k)) by ring, Complex.mul_conj']
    have hswap : ∑ k ∈ S, w k * conj (φ k) = ∑' j, u j * conj (M j) := by
      have e1 : ∀ k ∈ S, w k * conj (φ k) = ∑' j, coeffOf a (k - j) * u j * conj (φ k) :=
        fun k _ => by rw [hw]; simp only [mulCoeff]; rw [tsum_mul_right]
      rw [Finset.sum_congr rfl e1, ← Summable.tsum_finsetSum (fun k _ => (hsum k).mul_right _)]
      refine tsum_congr fun j => ?_
      have hMj : M j = ∑ k ∈ S, coeffOf a (j - k) * φ k := by
        simp only [hMdef, mulCoeff]
        exact tsum_eq_sum (fun k hk => by simp [hφsupp k hk])
      rw [hMj, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, conj_coeffOf_sub]; ring
    have hcs := summable_tsum_norm_mul_le (-1) (y := M) hu (by simpa using hM1)
    simp only [neg_neg] at hcs
    have hbound : ‖∑' j, u j * conj (M j)‖ ≤ hsNorm (-1) u * hsNorm 1 M := by
      have hs : Summable fun j => ‖u j * conj (M j)‖ := by
        simpa [norm_mul] using hcs.1
      refine (norm_tsum_le_tsum_norm hs).trans ?_
      simpa [norm_mul] using hcs.2
    have hsq : hsNorm 1 φ = Real.sqrt X := by unfold hsNorm; rw [hnorm]
    have hX_le : X ≤ A * Real.sqrt X := by
      calc X = ‖(X : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hXn]
        _ = ‖∑' j, u j * conj (M j)‖ := by rw [← hpair, hswap]
        _ ≤ hsNorm (-1) u * hsNorm 1 M := hbound
        _ ≤ hsNorm (-1) u * (prodConstH1 d * Torus.cbNorm 1 a * hsNorm 1 φ) := by
          gcongr
          exact Real.sqrt_nonneg _
        _ = A * Real.sqrt X := by rw [hsq, hA]; ring
    by_contra hcon
    push Not at hcon
    have ht : A < Real.sqrt X := by
      rw [Real.lt_sqrt hA0]; exact hcon
    have hX2 : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hXn
    nlinarith [Real.sqrt_nonneg X]
  refine ⟨summable_of_sum_le (fun k => hnn k) key, ?_⟩
  have h2 : hsNormSq (-1) w ≤ A ^ 2 := Real.tsum_le_of_sum_le (fun k => hnn k) key
  unfold hsNorm
  calc Real.sqrt (hsNormSq (-1) w) ≤ Real.sqrt (A ^ 2) := Real.sqrt_le_sqrt h2
    _ = A := Real.sqrt_sq hA0

end HRS.PDE
