import HRS.Commutator.Torus.NRSTAux11
import HRS.Commutator.Torus.TEXTAux19

/-!
# NRS-T, part 12: Fejér means are real trigonometric polynomials
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ}

lemma fcoef_eq_coeffOf (φ : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef φ k = KernelGrad.coeffOf φ k :=
  (KernelGrad.coeffOf_eq_integral φ k).symm

lemma ev_real_of_symm (T : TPA d) (hT : ∀ k, T.coeff (-k) = (starRingEnd ℂ) (T.coeff k)) (x : Torus d) :
    (ev T x).im = 0 := by
  classical
  set S : Finset (Lattice d) := T.coeff.support ∪ T.coeff.support.image Neg.neg with hS
  have hsub : T.coeff.support ⊆ S := Finset.subset_union_left
  have hev : ev T x = ∑ k ∈ S, T.coeff k * Torus.mode k x := by
    rw [ev_apply_sum]
    refine Finset.sum_subset hsub fun k _ hk => ?_
    have : T.coeff k = 0 := by simpa using hk
    simp [this]
  have hconj : (starRingEnd ℂ) (ev T x) = ev T x := by
    rw [hev, map_sum]
    refine Finset.sum_nbij' Neg.neg Neg.neg (fun k hk => ?_) (fun k hk => ?_) (fun k _ => neg_neg k)
      (fun k _ => neg_neg k) (fun k _ => ?_)
    · rw [hS] at hk ⊢
      simp only [Finset.mem_union, Finset.mem_image] at hk ⊢
      rcases hk with hk | ⟨a, ha, rfl⟩
      · exact Or.inr ⟨k, hk, rfl⟩
      · exact Or.inl (by simpa using ha)
    · rw [hS] at hk ⊢
      simp only [Finset.mem_union, Finset.mem_image] at hk ⊢
      rcases hk with hk | ⟨a, ha, rfl⟩
      · exact Or.inr ⟨k, hk, rfl⟩
      · exact Or.inl (by simpa using ha)
    · rw [map_mul, ← hT, Torus.mode_neg]
  have := congrArg Complex.im hconj
  simp at this
  linarith

/-- Fejér multiplier `∏_i (1 - |k_i|/(n+1))_+`. -/
def fejCoef (n : ℕ) (k : Lattice d) : ℝ := ∏ i : Fin d, max (1 - |(k i : ℝ)| / ((n : ℝ) + 1)) 0

lemma fejCoef_eq_zero (n : ℕ) {k : Lattice d} (h : ¬ ∀ i, k i ∈ Finset.Icc (-(n : ℤ)) n) :
    fejCoef n k = 0 := by
  push Not at h
  obtain ⟨i, hi⟩ := h
  unfold fejCoef
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [Finset.mem_Icc] at hi
  have h3 : (n : ℤ) < |k i| := by
    by_contra hc
    push Not at hc
    exact hi (abs_le.1 hc)
  have h4 : ((n : ℤ) + 1 : ℤ) ≤ |k i| := h3
  have h5 : (n : ℝ) + 1 ≤ |(k i : ℝ)| := by
    have := (Int.cast_le (R := ℝ)).2 h4
    simpa [Int.cast_abs] using this
  have h2 : (1 : ℝ) ≤ |(k i : ℝ)| / ((n : ℝ) + 1) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact max_eq_right (by linarith)

/-- The trigonometric polynomial `∑_k φ_n(k) ĥ(k) e_k` (the Fejér mean of `h`). -/
def trigOf (n : ℕ) (h : Torus d → ℝ) : TPA d :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset
    (Fintype.piFinset fun _ : Fin d => Finset.Icc (-(n : ℤ)) n)
    (fun k => ((fejCoef n k : ℝ) : ℂ) * Torus.fcoef h k) (fun k hk => by
      rw [Fintype.mem_piFinset]
      by_contra hc
      apply hk
      rw [fejCoef_eq_zero n hc]; simp))

@[simp] lemma coeff_trigOf (n : ℕ) (h : Torus d → ℝ) (k : Lattice d) :
    (trigOf n h).coeff k = ((fejCoef n k : ℝ) : ℂ) * Torus.fcoef h k := by
  simp [trigOf]

lemma fcoef_neg_conj (h : Torus d → ℝ) (k : Lattice d) :
    Torus.fcoef h (-k) = (starRingEnd ℂ) (Torus.fcoef h k) := by
  unfold Torus.fcoef
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Torus.mode_neg, neg_neg, Complex.conj_ofReal]
  rw [Complex.conj_conj]

lemma fejCoef_neg (n : ℕ) (k : Lattice d) : fejCoef n (-k) = fejCoef n k := by
  unfold fejCoef
  simp

lemma trigOf_symm (n : ℕ) (h : Torus d → ℝ) (k : Lattice d) :
    (trigOf n h).coeff (-k) = (starRingEnd ℂ) ((trigOf n h).coeff k) := by
  rw [coeff_trigOf, coeff_trigOf, fejCoef_neg, fcoef_neg_conj, map_mul, Complex.conj_ofReal]

lemma continuous_convFun (g h : Torus d → ℝ) (hg : Continuous g) (hh : Continuous h) :
    Continuous (HRS.convFun g h) := by
  unfold HRS.convFun
  have : Continuous (Function.uncurry fun (x y : Torus d) => g (x - y) * h y) :=
    (hg.comp (continuous_fst.sub continuous_snd)).mul (hh.comp continuous_snd)
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d))) this isCompact_univ
  simpa using this

lemma ev_trigOf (n : ℕ) {h : Torus d → ℝ} (hh : Continuous h) (x : Torus d) :
    ev (trigOf n h) x = ((HRS.convFun (fj d n) h x : ℝ) : ℂ) := by
  set T := trigOf n h with hT
  have hr : ∀ x, (ev T x).im = 0 := ev_real_of_symm T (trigOf_symm n h)
  have hu : Continuous (HRS.convFun (fj d n) h) := continuous_convFun _ _ (fj_cont n) hh
  have ht : Continuous (fun x => (ev T x).re) := Complex.continuous_re.comp (continuous_ev T)
  have hui : Integrable (HRS.convFun (fj d n) h) :=
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hti : Integrable (fun x => (ev T x).re) :=
    ht.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hhi : Integrable h := hh.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae : (fun x => HRS.convFun (fj d n) h x - (ev T x).re) =ᵐ[volume] 0 := by
    refine text_ae_eq_zero_of_fcoef (hui.sub hti) fun k => ?_
    rw [text_fcoef_sub hui hti]
    have h1 : Torus.fcoef (HRS.convFun (fj d n) h) k = Torus.fcoef (fj d n) k * Torus.fcoef h k :=
      text_fcoef_conv (fj_integrable n) hhi k
    have h2 : Torus.fcoef (fj d n) k = ((fejCoef n k : ℝ) : ℂ) := by
      rw [fcoef_eq_coeffOf]
      have := HRS.PDE.MFThermalExist.coeffOf_fejer (d := d) (n + 1) (Nat.succ_pos n) k
      have e0 : KernelGrad.coeffOf (HRS.PDE.MFThermalExist.fejer (n + 1)) k =
          HRS.PDE.coeffOf (HRS.PDE.MFThermalExist.fejer (n + 1)) k := rfl
      rw [show (fj d n) = HRS.PDE.MFThermalExist.fejer (n + 1) from rfl, e0, this]
      unfold fejCoef
      push_cast
      rfl
    have h3 : Torus.fcoef (fun x => (ev T x).re) k = T.coeff k := by
      rw [fcoef_eq_coeffOf]; exact coeffOf_re_ev T hr k
    rw [h1, h2, h3, hT, coeff_trigOf]
    ring
  have heq : HRS.convFun (fj d n) h = fun x => (ev T x).re := by
    have h0 : (fun x => HRS.convFun (fj d n) h x - (ev T x).re) = fun _ => (0 : ℝ) :=
      (Continuous.ae_eq_iff_eq (volume : Measure (Torus d)) (hu.sub ht) continuous_const).1
        (by filter_upwards [hae] with x hx; simpa using hx)
    funext x
    have := congrFun h0 x
    simpa [sub_eq_zero] using this
  rw [heq, ev_re_cast T hr x]

end HRS.Commutator.TorusNote.NRST
