import HRS.PDE.Galerkin
import HRS.PDE.HsAnalysis
import HRS.PDE.GalerkinLimit

/-!
# Helper lemmas for the assembly of Proposition 3.9 (`adjoint_torus`)

* `weakContinuousInHs_mono`: `C_w H^m ⊂ C_w H^{m'}` for `m' ≤ m`;
* Pythagoras for `a + i b` with `a, b` Hermitian-symmetric trigonometric polynomials, and the
  decomposition of a complex datum into real and imaginary parts;
* linearity of the Galerkin system in the datum.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Weak continuity at lower regularity -/

lemma weakContinuousInHs_mono {m m' : ℝ} (h : m' ≤ m) {F : ℝ → Coeff d} {t : ℝ}
    (hF : WeakContinuousInHs m F t) : WeakContinuousInHs m' F t := by
  refine ⟨fun τ hτ => (hF.1 τ hτ).mono h, fun G hG => ?_⟩
  set G' : Coeff d := fun k => ((sobWeight (m' - m) k : ℝ) : ℂ) * G k with hG'
  have hG'mem : MemHs m G' := by
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _))
      (fun k => ?_) hG
    have e : sobWeight m k * ‖G' k‖ ^ 2 =
        sobWeight m' k * (sobWeight (m' - m) k * ‖G k‖ ^ 2) := by
      have : sobWeight m' k = sobWeight (m' - m) k * sobWeight m k := by
        rw [← sobWeight_add]; ring_nf
      simp only [hG', norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sobWeight_pos (m' - m) k).le]
      rw [this]; ring
    rw [e]
    have h1 : sobWeight (m' - m) k ≤ 1 := by
      rw [← sobWeight_zero k]; exact sobWeight_mono (by linarith) k
    have h2 := (sobWeight_pos m' k).le
    have h3 : sobWeight (m' - m) k * ‖G k‖ ^ 2 ≤ ‖G k‖ ^ 2 := by
      nlinarith [sq_nonneg ‖G k‖]
    exact mul_le_mul_of_nonneg_left h3 h2
  refine (hF.2 G' hG'mem).congr fun τ _ => ?_
  unfold hsInner
  refine tsum_congr fun k => ?_
  have : sobWeight m' k = sobWeight (m' - m) k * sobWeight m k := by
    rw [← sobWeight_add]; ring_nf
  simp only [hG', map_mul, Complex.conj_ofReal, this]
  push_cast
  ring

/-! ### Trigonometric polynomials are in every `H^m` -/

lemma isTrigPoly_memHs {n : ℕ} {c : Coeff d} (h : IsTrigPoly n c) (m : ℝ) : MemHs m c := by
  refine summable_of_ne_finset_zero (s := boxFinset d n) fun k hk => ?_
  rw [h.eq_zero (fun hb => hk (mem_boxFinset.2 hb))]
  simp

/-! ### Pythagoras for `a + i b` -/

lemma hsNormSq_add_I_smul {n : ℕ} {a b : Coeff d} (ha : IsTrigPoly n a) (hb : IsTrigPoly n b)
    (har : IsRealCoeff a) (hbr : IsRealCoeff b) (m : ℝ) :
    hsNormSq m (a + Complex.I • b) = hsNormSq m a + hsNormSq m b := by
  have hab : IsTrigPoly n (a + Complex.I • b) := ha.add (hb.smul _)
  rw [hsNormSq_trig hab, hsNormSq_trig ha, hsNormSq_trig hb, ← Finset.sum_add_distrib]
  have key : ∀ k, sobWeight m k * ‖(a + Complex.I • b) k‖ ^ 2 =
      sobWeight m k * ‖a k‖ ^ 2 + sobWeight m k * ‖b k‖ ^ 2 +
        2 * (sobWeight m k * (a k * conj (b k)).im) := by
    intro k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.sq_norm, Complex.normSq_apply,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.conj_re, Complex.conj_im]
    ring
  simp_rw [key, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hT : ∑ k ∈ boxFinset d n, sobWeight m k * (a k * conj (b k)).im = 0 := by
    set T := ∑ k ∈ boxFinset d n, sobWeight m k * (a k * conj (b k)).im with hT
    have : T = ∑ k ∈ boxFinset d n, -(sobWeight m k * (a k * conj (b k)).im) := by
      refine Finset.sum_nbij' (fun k => -k) (fun k => -k)
        (fun k hk => by simpa [mem_boxFinset, inBox_neg_iff] using hk)
        (fun k hk => by simpa [mem_boxFinset, inBox_neg_iff] using hk)
        (fun k _ => by simp) (fun k _ => by simp) ?_
      intro k _
      have e1 := har k
      have e2 := hbr k
      have hw : sobWeight m (-k) = sobWeight m k := by
        unfold sobWeight; rw [enorm_neg']
      simp only [hw, e1, e2, Complex.conj_conj, Complex.mul_im, Complex.conj_re,
        Complex.conj_im]
      ring
    rw [Finset.sum_neg_distrib] at this
    linarith
  rw [hT]; ring

/-! ### Real and imaginary parts of a datum -/

/-- `Re c = (c + c̃)/2`, `c̃ = reflConj c`. -/
def rePart (c : Coeff d) : Coeff d := fun k => (1 / 2 : ℂ) * (c k + conj (c (-k)))

/-- `Im c = (c - c̃)/(2i)`. -/
def imPart (c : Coeff d) : Coeff d := fun k => (-Complex.I / 2 : ℂ) * (c k - conj (c (-k)))

lemma isRealCoeff_rePart (c : Coeff d) : IsRealCoeff (rePart c) := by
  intro k
  simp only [rePart, neg_neg, map_mul, map_add, Complex.conj_conj]
  simp [map_ofNat]
  ring

lemma isRealCoeff_imPart (c : Coeff d) : IsRealCoeff (imPart c) := by
  intro k
  simp only [imPart, neg_neg, map_mul, map_sub, Complex.conj_conj]
  simp [Complex.conj_I, map_ofNat]
  ring

lemma rePart_add_I_imPart (c : Coeff d) : rePart c + Complex.I • imPart c = c := by
  funext k
  simp only [rePart, imPart, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(1 / 2 : ℂ) * (c k - conj (c (-k)))) * this
    
lemma sobWeight_neg (m : ℝ) (k : Lattice d) : sobWeight m (-k) = sobWeight m k := by
  unfold sobWeight; rw [enorm_neg']

lemma norm_rePart_sq_add (c : Coeff d) (k : Lattice d) :
    ‖rePart c k‖ ^ 2 + ‖imPart c k‖ ^ 2 = (‖c k‖ ^ 2 + ‖c (-k)‖ ^ 2) / 2 := by
  have h1 : ‖c (-k)‖ = ‖conj (c (-k))‖ := (Complex.norm_conj _).symm
  rw [h1]
  simp only [rePart, imPart]
  generalize conj (c (-k)) = y
  generalize c k = x
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.div_ofNat_re,
    Complex.div_ofNat_im, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

lemma memHs_rePart_imPart {m : ℝ} {c : Coeff d} (hc : MemHs m c) :
    MemHs m (rePart c) ∧ MemHs m (imPart c) ∧
      hsNormSq m (rePart c) + hsNormSq m (imPart c) = hsNormSq m c := by
  have hneg : Summable fun k : Lattice d => sobWeight m k * ‖c (-k)‖ ^ 2 := by
    have := (Equiv.summable_iff (Equiv.neg (Lattice d))).2 hc
    refine this.congr fun k => ?_
    simp [sobWeight_neg]
  have htneg : ∑' k : Lattice d, sobWeight m k * ‖c (-k)‖ ^ 2 = hsNormSq m c := by
    have := (Equiv.neg (Lattice d)).tsum_eq (fun k : Lattice d => sobWeight m k * ‖c k‖ ^ 2)
    unfold hsNormSq
    rw [← this]
    exact tsum_congr fun k => by simp [sobWeight_neg]
  have hpt : ∀ k, sobWeight m k * ‖rePart c k‖ ^ 2 + sobWeight m k * ‖imPart c k‖ ^ 2 =
      (sobWeight m k * ‖c k‖ ^ 2 + sobWeight m k * ‖c (-k)‖ ^ 2) / 2 := by
    intro k
    rw [← mul_add, norm_rePart_sq_add]; ring
  have hu : Summable fun k : Lattice d =>
      (sobWeight m k * ‖c k‖ ^ 2 + sobWeight m k * ‖c (-k)‖ ^ 2) / 2 :=
    (hc.add hneg).div_const 2
  have hre : MemHs m (rePart c) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _))
      (fun k => by
        have := hpt k
        nlinarith [mul_nonneg (sobWeight_pos m k).le (sq_nonneg ‖imPart c k‖)]) hu
  have him : MemHs m (imPart c) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos _ k).le (sq_nonneg _))
      (fun k => by
        have := hpt k
        nlinarith [mul_nonneg (sobWeight_pos m k).le (sq_nonneg ‖rePart c k‖)]) hu
  refine ⟨hre, him, ?_⟩
  unfold hsNormSq
  rw [← hre.tsum_add him]
  simp_rw [hpt]
  rw [tsum_div_const, hc.tsum_add hneg, htneg]
  unfold hsNormSq
  ring

/-! ### Linearity of the Galerkin system -/

lemma galGen_add_smul (D : DynData d) (ρ : Torus d → ℝ) (n : ℕ) (F₁ F₂ : Coeff d) (z : ℂ) :
    galGen D ρ n (F₁ + z • F₂) = galGen D ρ n F₁ + z • galGen D ρ n F₂ := by
  unfold galGen
  rw [truncCoeff_add, truncCoeff_smul,
    forwardGen_add D ρ _ _ (isTrigPoly_truncCoeff n F₁) ((isTrigPoly_truncCoeff n F₂).smul z),
    forwardGen_smul, truncCoeff_add, truncCoeff_smul]

lemma IsGalSol.add_smul {m : ℕ} {Λ T : ℝ} {μ : ℝ → Torus d → ℝ} (h : CoeffHyp m Λ T μ) {t : ℝ}
    (ht : t ∈ Set.Ioc 0 T) {D : DynData d} {n : ℕ} {φ₁ φ₂ : Coeff d} {F₁ F₂ : ℝ → Coeff d}
    (z : ℂ) (h₁ : IsGalSol D μ t n φ₁ F₁) (h₂ : IsGalSol D μ t n φ₂ F₂) :
    IsGalSol D μ t n (φ₁ + z • φ₂) (fun τ => F₁ τ + z • F₂ τ) := by
  refine ⟨fun τ => (h₁.trig τ).add ((h₂.trig τ).smul z), fun k => ?_, fun k τ hτ => ?_⟩
  · exact (h₁.cont k).add ((h₂.cont k).const_smul z)
  · have hτ0 : (0 : ℝ) ≤ τ := hτ.1
    have hsub : Set.uIcc 0 τ ⊆ Set.Icc 0 t := Set.uIcc_subset_Icc ⟨le_rfl, ht.1.le⟩ hτ
    have i₁ : IntervalIntegrable (fun σ => galGen D (μ (t - σ)) n (F₁ σ) k) volume 0 τ :=
      ((h₁.integrand_continuousOn h ht k).mono hsub).intervalIntegrable
    have i₂ : IntervalIntegrable (fun σ => galGen D (μ (t - σ)) n (F₂ σ) k) volume 0 τ :=
      ((h₂.integrand_continuousOn h ht k).mono hsub).intervalIntegrable
    have e1 := h₁.eq k τ hτ
    have e2 := h₂.eq k τ hτ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, galGen_add_smul, truncCoeff_add,
      truncCoeff_smul]
    rw [intervalIntegral.integral_add i₁ (i₂.const_mul z), intervalIntegral.integral_const_mul,
      e1, e2]
    ring

/-- A complex datum: from the bound for real data to the bound for complex data. -/
lemma galSol_complex_exists {m : ℕ} {Λ T VB : ℝ} {μ : ℝ → Torus d → ℝ} (h : CoeffHyp m Λ T μ)
    {D : DynData d} (hV : VHyp m VB D.V) {t : ℝ} (ht : t ∈ Set.Ioc 0 T) (E : ℝ → ℝ)
    (hE0 : ∀ τ, 0 ≤ E τ)
    (hreal : ∀ (φ' : Coeff d), MemHs m φ' → IsRealCoeff φ' → ∀ (n : ℕ) (F : ℝ → Coeff d),
      IsGalSol D μ t n φ' F → ∀ τ ∈ Set.Icc 0 t, hsNorm m (F τ) ≤ E τ * hsNorm m φ')
    (n : ℕ) (φ : Coeff d) (hφ : MemHs m φ) :
    ∃ F : ℝ → Coeff d, IsGalSol D μ t n φ F ∧
      ∀ τ ∈ Set.Icc 0 t, hsNorm m (F τ) ≤ E τ * hsNorm m φ := by
  obtain ⟨hre, him, hsum⟩ := memHs_rePart_imPart hφ
  obtain ⟨F₁, hF₁, -⟩ := galSol_exists_unique h ht D n (rePart φ)
  obtain ⟨F₂, hF₂, -⟩ := galSol_exists_unique h ht D n (imPart φ)
  have hF := IsGalSol.add_smul h ht Complex.I hF₁ hF₂
  rw [rePart_add_I_imPart] at hF
  refine ⟨_, hF, fun τ hτ => ?_⟩
  have r₁ := hF₁.isReal h hV ht (isRealCoeff_rePart φ) τ hτ
  have r₂ := hF₂.isReal h hV ht (isRealCoeff_imPart φ) τ hτ
  have b₁ := hreal _ hre (isRealCoeff_rePart φ) n F₁ hF₁ τ hτ
  have b₂ := hreal _ him (isRealCoeff_imPart φ) n F₂ hF₂ τ hτ
  have py := hsNormSq_add_I_smul (hF₁.trig τ) (hF₂.trig τ) r₁ r₂ (m : ℝ)
  have sq : ∀ c : Coeff d, hsNorm m c ^ 2 = hsNormSq m c := fun c =>
    Real.sq_sqrt (hsNormSq_nonneg _ _)
  have hnorm : hsNorm m (F₁ τ + Complex.I • F₂ τ) ^ 2 ≤ (E τ * hsNorm m φ) ^ 2 := by
    show hsNorm m ((fun τ => F₁ τ + Complex.I • F₂ τ) τ) ^ 2 ≤ _
    simp only [sq, py]
    rw [← sq (F₁ τ), ← sq (F₂ τ)]
    have e0 := hE0 τ
    calc hsNorm m (F₁ τ) ^ 2 + hsNorm m (F₂ τ) ^ 2
        ≤ (E τ * hsNorm m (rePart φ)) ^ 2 + (E τ * hsNorm m (imPart φ)) ^ 2 :=
          add_le_add (pow_le_pow_left₀ (Real.sqrt_nonneg _) b₁ 2)
            (pow_le_pow_left₀ (Real.sqrt_nonneg _) b₂ 2)
      _ = E τ ^ 2 * (hsNorm m (rePart φ) ^ 2 + hsNorm m (imPart φ) ^ 2) := by ring
      _ = (E τ * hsNorm m φ) ^ 2 := by rw [sq, sq, hsum, ← sq]; ring
  exact (pow_le_pow_iff_left₀ (Real.sqrt_nonneg _) (mul_nonneg (hE0 τ) (Real.sqrt_nonneg _))
    two_ne_zero).1 hnorm

/-! ### Lower semicontinuity of the norm under coordinatewise convergence -/

lemma bound_of_coord_limit {m : ℝ} {t : ℝ} {Fn : ℕ → ℝ → Coeff d} {G : ℝ → Coeff d}
    (hconv : ∀ k, TendstoUniformlyOn (fun n τ => Fn n τ k) (fun τ => G τ k) atTop
      (Set.Icc 0 t))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 t) (b : ℝ) (hmem : ∀ n, MemHs m (Fn n τ))
    (hb : ∀ n, hsNormSq m (Fn n τ) ≤ b) : MemHs m (G τ) ∧ hsNormSq m (G τ) ≤ b := by
  refine memHs_of_sum_le fun S => ?_
  have ht : Tendsto (fun n => ∑ k ∈ S, sobWeight m k * ‖Fn n τ k‖ ^ 2) atTop
      (𝓝 (∑ k ∈ S, sobWeight m k * ‖G τ k‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun k _ => ?_
    exact (((hconv k).tendsto_at hτ).norm.pow 2).const_mul _
  exact le_of_tendsto' ht fun n => (sum_le_hsNormSq (hmem n) S).trans (hb n)

end HRS.PDE
