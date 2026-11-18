import Mathlib

/-!
# Packet CEPP2 (aux 1): test class, calculus for `χ cos ℓ_ζ`, `χ sin ℓ_ζ`
-/

open MeasureTheory

noncomputable section
namespace HRS.MC.CepP2

abbrev XS (n : ℕ) := ℝ × EuclideanSpace ℝ (Fin n)
abbrev smTop : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

variable {n : ℕ}


lemma d2_mul {u v : XS n → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) (p w : XS n) :
    fderiv ℝ (fderiv ℝ (fun q => u q * v q)) p w w =
      fderiv ℝ (fderiv ℝ u) p w w * v p + 2 * (fderiv ℝ u p w * fderiv ℝ v p w)
        + u p * fderiv ℝ (fderiv ℝ v) p w w := by
  have h1 : fderiv ℝ (fun q => u q * v q) = fun q => u q • fderiv ℝ v q + v q • fderiv ℝ u q := by
    funext q
    rw [fderiv_fun_mul (hu.differentiable (by norm_num) q) (hv.differentiable (by norm_num) q)]
  have hdu : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hdv : Differentiable ℝ v := hv.differentiable (by norm_num)
  have hu' : Differentiable ℝ (fderiv ℝ u) :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hv' : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hA := (hdu p).hasFDerivAt.smul (hv' p).hasFDerivAt
  have hB := (hdv p).hasFDerivAt.smul (hu' p).hasFDerivAt
  have h2 : fderiv ℝ (fun q => u q • fderiv ℝ v q + v q • fderiv ℝ u q) p = _ :=
    (hA.add hB).fderiv
  rw [h1, h2]
  simp
  ring

/-- Smooth, compactly supported, with topological support inside `O`. -/
def IsTest (O : Set (XS n)) (g : XS n → ℝ) : Prop :=
  ContDiff ℝ smTop g ∧ HasCompactSupport g ∧ tsupport g ⊆ O

lemma tsupport_apply_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : XS n → (XS n →L[ℝ] F)) (v : XS n) : tsupport (fun p => A p v) ⊆ tsupport A := by
  apply closure_mono
  intro p hp
  simp only [Function.mem_support] at hp ⊢
  intro h
  apply hp
  simp [h]

variable {O : Set (XS n)} {g h : XS n → ℝ}

lemma IsTest.contDiff (hg : IsTest O g) : ContDiff ℝ smTop g := hg.1
lemma IsTest.compact (hg : IsTest O g) : HasCompactSupport g := hg.2.1
lemma IsTest.tsub (hg : IsTest O g) : tsupport g ⊆ O := hg.2.2

lemma IsTest.add (hg : IsTest O g) (hh : IsTest O h) : IsTest O (fun p => g p + h p) := by
  refine ⟨hg.1.add hh.1, hg.2.1.add hh.2.1, ?_⟩
  exact (tsupport_add g h).trans (Set.union_subset hg.2.2 hh.2.2)

lemma IsTest.neg (hg : IsTest O g) : IsTest O (fun p => - g p) := by
  refine ⟨hg.1.neg, ?_, ?_⟩
  · exact hg.2.1.comp_left (g := fun x : ℝ => -x) neg_zero
  · simpa [tsupport] using hg.2.2

lemma IsTest.const_mul (c : ℝ) (hg : IsTest O g) : IsTest O (fun p => c * g p) := by
  refine ⟨contDiff_const.mul hg.1, ?_, ?_⟩
  · exact hg.2.1.mul_left (f := fun _ => c)
  · exact (tsupport_mul_subset_right (f := fun _ => c) (g := g)).trans hg.2.2

lemma IsTest.mul_smooth {u : XS n → ℝ} (hu : ContDiff ℝ smTop u) (hg : IsTest O g) :
    IsTest O (fun p => u p * g p) := by
  refine ⟨hu.mul hg.1, hg.2.1.mul_left (f := u), ?_⟩
  exact (tsupport_mul_subset_right (f := u) (g := g)).trans hg.2.2

lemma IsTest.sum {ι : Type*} (s : Finset ι) {G : ι → XS n → ℝ} (hG : ∀ i ∈ s, IsTest O (G i)) :
    IsTest O (fun p => ∑ i ∈ s, G i p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using contDiff_const, by exact HasCompactSupport.zero, ?_⟩
    simp
  | insert a s ha ih =>
    have h1 := hG a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hG i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1.add h2

lemma IsTest.fderiv_apply (hg : IsTest O g) (v : XS n) :
    IsTest O (fun p => fderiv ℝ g p v) := by
  refine ⟨?_, hg.2.1.fderiv_apply ℝ v, (tsupport_fderiv_apply_subset ℝ v).trans hg.2.2⟩
  exact (hg.1.fderiv_right (m := smTop) (by simp)).clm_apply contDiff_const

lemma IsTest.fderiv2_apply (hg : IsTest O g) (v w : XS n) :
    IsTest O (fun p => fderiv ℝ (fderiv ℝ g) p v w) := by
  have hc : ContDiff ℝ smTop (fderiv ℝ g) := hg.1.fderiv_right (m := smTop) (by simp)
  have hc2 : ContDiff ℝ smTop (fderiv ℝ (fderiv ℝ g)) := hc.fderiv_right (m := smTop) (by simp)
  refine ⟨(hc2.clm_apply contDiff_const).clm_apply contDiff_const, ?_, ?_⟩
  · have h1 : HasCompactSupport (fderiv ℝ g) := hg.2.1.fderiv ℝ
    have h2 : HasCompactSupport (fderiv ℝ (fderiv ℝ g)) := h1.fderiv ℝ
    have h3 : HasCompactSupport (fun p => fderiv ℝ (fderiv ℝ g) p v) :=
      h2.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_apply_subset (fun p => fderiv ℝ (fderiv ℝ g) p) v)
    exact h3.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_apply_subset (fun p => fderiv ℝ (fderiv ℝ g) p v) w)
  · refine (tsupport_apply_subset (fun p => fderiv ℝ (fderiv ℝ g) p v) w).trans ?_
    refine (tsupport_apply_subset (fun p => fderiv ℝ (fderiv ℝ g) p) v).trans ?_
    exact (tsupport_fderiv_subset ℝ).trans ((tsupport_fderiv_subset ℝ).trans hg.2.2)


lemma IsTest.mul_coord (hO : IsOpen O) {b : XS n → EuclideanSpace ℝ (Fin n)}
    (hb : ContDiffOn ℝ smTop b O) (hg : IsTest O g) (k : Fin n) :
    IsTest O (fun p => g p * (b p) k) := by
  refine ⟨?_, hg.2.1.mul_right (f' := fun p => (b p) k), ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hp : p ∈ O
    · have h1 : ContDiffAt ℝ smTop b p := hb.contDiffAt (hO.mem_nhds hp)
      have h2 : ContDiffAt ℝ smTop (fun q => (b q) k) p :=
        ((EuclideanSpace.proj k : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).contDiff.contDiffAt).comp p h1
      exact hg.1.contDiffAt.mul h2
    · have hp' : p ∉ tsupport g := fun h => hp (hg.2.2 h)
      have hev : g =ᶠ[nhds p] 0 := notMem_tsupport_iff_eventuallyEq.1 hp'
      have hev2 : (fun q => g q * (b q) k) =ᶠ[nhds p] fun _ => 0 := by
        filter_upwards [hev] with q hq
        simp [hq]
      exact (contDiffAt_const).congr_of_eventuallyEq hev2
  · exact (tsupport_mul_subset_left (f := g) (g := fun p => (b p) k)).trans hg.2.2

/-- The phase `ℓ_ζ(p) = τ t + ⟪ξ, x⟫`, as a continuous linear form on `X`. -/
def ell (ζ : XS n) : XS n →L[ℝ] ℝ :=
  ζ.1 • ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)) +
    (innerSL ℝ ζ.2).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin n)))

lemma ell_apply (ζ p : XS n) : ell ζ p = ζ.1 * p.1 + inner ℝ ζ.2 p.2 := by
  simp [ell]

lemma ell_time (ζ : XS n) : ell ζ ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n))) = ζ.1 := by
  simp [ell_apply]

lemma ell_space (ζ : XS n) (v : EuclideanSpace ℝ (Fin n)) :
    ell ζ ((0 : ℝ), v) = ∑ k, ζ.2 k * v k := by
  simp [ell_apply, PiLp.inner_apply, mul_comm]

lemma ell_single (ζ : XS n) (k : Fin n) :
    ell ζ ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) = ζ.2 k := by
  simp [ell_space]

lemma fderiv_cos_ell (ζ p : XS n) :
    fderiv ℝ (fun q => Real.cos (ell ζ q)) p = -(Real.sin (ell ζ p)) • ell ζ := by
  have := ((ell ζ).hasFDerivAt (x := p)).cos
  rw [this.fderiv]

lemma fderiv_sin_ell (ζ p : XS n) :
    fderiv ℝ (fun q => Real.sin (ell ζ q)) p = (Real.cos (ell ζ p)) • ell ζ := by
  have := ((ell ζ).hasFDerivAt (x := p)).sin
  rw [this.fderiv]

lemma fderiv2_cos_ell (ζ p w : XS n) :
    fderiv ℝ (fderiv ℝ (fun q => Real.cos (ell ζ q))) p w w = - Real.cos (ell ζ p) * (ell ζ w) ^ 2 := by
  have h1 : fderiv ℝ (fun q => Real.cos (ell ζ q)) = fun q => (-(Real.sin (ell ζ q))) • ell ζ := by
    funext q; exact fderiv_cos_ell ζ q
  have h2 : HasFDerivAt (fun q => -(Real.sin (ell ζ q)))
      (-(Real.cos (ell ζ p) • ell ζ)) p := (((ell ζ).hasFDerivAt (x := p)).sin).neg
  have h3 := h2.smul_const (ell ζ)
  rw [h1, h3.fderiv]
  simp
  ring

lemma fderiv2_sin_ell (ζ p w : XS n) :
    fderiv ℝ (fderiv ℝ (fun q => Real.sin (ell ζ q))) p w w = - Real.sin (ell ζ p) * (ell ζ w) ^ 2 := by
  have h1 : fderiv ℝ (fun q => Real.sin (ell ζ q)) = fun q => (Real.cos (ell ζ q)) • ell ζ := by
    funext q; exact fderiv_sin_ell ζ q
  have h2 : HasFDerivAt (fun q => Real.cos (ell ζ q))
      (-(Real.sin (ell ζ p)) • ell ζ) p := by
    have := (((ell ζ).hasFDerivAt (x := p)).cos)
    simpa using this
  have h3 := h2.smul_const (ell ζ)
  rw [h1, h3.fderiv]
  simp
  ring


/-- The integrand of the weak equation. -/
def feq (invβ : ℝ) (b : XS n → EuclideanSpace ℝ (Fin n)) (Φ : XS n → ℝ) (p : XS n) : ℝ :=
  fderiv ℝ Φ p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))
    + invβ * ∑ k : Fin n, fderiv ℝ (fderiv ℝ Φ) p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
        ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
    + fderiv ℝ Φ p ((0 : ℝ), b p)

/-- The `k`-th component of the first-order coefficient. -/
def gone (invβ : ℝ) (b : XS n → EuclideanSpace ℝ (Fin n)) (χ : XS n → ℝ) (k : Fin n) (p : XS n) : ℝ :=
  2 * invβ * fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) + χ p * (b p) k

lemma feq_cos (invβ : ℝ) (b : XS n → EuclideanSpace ℝ (Fin n)) {χ : XS n → ℝ}
    (hχ : ContDiff ℝ smTop χ) (ζ p : XS n) :
    feq invβ b (fun q => χ q * Real.cos (ell ζ q)) p =
      feq invβ b χ p * Real.cos (ell ζ p)
        - (ζ.1 * χ p + ∑ k, ζ.2 k * gone invβ b χ k p) * Real.sin (ell ζ p)
        - invβ * ‖ζ.2‖ ^ 2 * χ p * Real.cos (ell ζ p) := by
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by simp)
  have hc2 : ContDiff ℝ 2 (fun q => Real.cos (ell ζ q)) :=
    Real.contDiff_cos.comp (ell ζ).contDiff
  have hD1 : ∀ v, fderiv ℝ (fun q => χ q * Real.cos (ell ζ q)) p v =
      fderiv ℝ χ p v * Real.cos (ell ζ p) - χ p * (Real.sin (ell ζ p) * ell ζ v) := by
    intro v
    rw [fderiv_fun_mul (hχ2.differentiable (by norm_num) p)
      ((hc2.differentiable (by norm_num)) p), fderiv_cos_ell]
    simp
    ring
  have hD2 : ∀ w, fderiv ℝ (fderiv ℝ (fun q => χ q * Real.cos (ell ζ q))) p w w =
      fderiv ℝ (fderiv ℝ χ) p w w * Real.cos (ell ζ p)
        - 2 * (fderiv ℝ χ p w * (Real.sin (ell ζ p) * ell ζ w))
        - χ p * (Real.cos (ell ζ p) * (ell ζ w) ^ 2) := by
    intro w
    rw [d2_mul hχ2 hc2, fderiv_cos_ell, fderiv2_cos_ell]
    simp
    ring
  unfold feq gone
  rw [hD1, hD1, ell_time, ell_space]
  simp only [hD2, ell_single]
  have hnorm : ‖ζ.2‖ ^ 2 = ∑ k, ζ.2 k ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq]
  set c := Real.cos (ell ζ p)
  set s := Real.sin (ell ζ p)
  have ha : ∑ k : Fin n, (fderiv ℝ (fderiv ℝ χ) p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
        ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) * c
        - 2 * (fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) * (s * ζ.2 k))
        - χ p * (c * ζ.2 k ^ 2)) =
      (∑ k : Fin n, fderiv ℝ (fderiv ℝ χ) p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
        ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))) * c
        - 2 * s * (∑ k : Fin n, ζ.2 k * fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)))
        - χ p * c * ∑ k : Fin n, ζ.2 k ^ 2 := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hb : ∑ k : Fin n, ζ.2 k * (2 * invβ * fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
        + χ p * (b p) k) =
      2 * invβ * (∑ k : Fin n, ζ.2 k * fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)))
        + χ p * ∑ k : Fin n, ζ.2 k * (b p) k := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [ha, hb, hnorm]
  ring


lemma feq_sin (invβ : ℝ) (b : XS n → EuclideanSpace ℝ (Fin n)) {χ : XS n → ℝ}
    (hχ : ContDiff ℝ smTop χ) (ζ p : XS n) :
    feq invβ b (fun q => χ q * Real.sin (ell ζ q)) p =
      feq invβ b χ p * Real.sin (ell ζ p)
        + (ζ.1 * χ p + ∑ k, ζ.2 k * gone invβ b χ k p) * Real.cos (ell ζ p)
        - invβ * ‖ζ.2‖ ^ 2 * χ p * Real.sin (ell ζ p) := by
  have hχ2 : ContDiff ℝ 2 χ := hχ.of_le (by simp)
  have hc2 : ContDiff ℝ 2 (fun q => Real.sin (ell ζ q)) :=
    Real.contDiff_sin.comp (ell ζ).contDiff
  have hD1 : ∀ v, fderiv ℝ (fun q => χ q * Real.sin (ell ζ q)) p v =
      fderiv ℝ χ p v * Real.sin (ell ζ p) + χ p * (Real.cos (ell ζ p) * ell ζ v) := by
    intro v
    rw [fderiv_fun_mul (hχ2.differentiable (by norm_num) p)
      ((hc2.differentiable (by norm_num)) p), fderiv_sin_ell]
    simp
    ring
  have hD2 : ∀ w, fderiv ℝ (fderiv ℝ (fun q => χ q * Real.sin (ell ζ q))) p w w =
      fderiv ℝ (fderiv ℝ χ) p w w * Real.sin (ell ζ p)
        + 2 * (fderiv ℝ χ p w * (Real.cos (ell ζ p) * ell ζ w))
        - χ p * (Real.sin (ell ζ p) * (ell ζ w) ^ 2) := by
    intro w
    rw [d2_mul hχ2 hc2, fderiv_sin_ell, fderiv2_sin_ell]
    simp
    ring
  unfold feq gone
  rw [hD1, hD1, ell_time, ell_space]
  simp only [hD2, ell_single]
  have hnorm : ‖ζ.2‖ ^ 2 = ∑ k, ζ.2 k ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq]
  set c := Real.cos (ell ζ p)
  set s := Real.sin (ell ζ p)
  have ha : ∑ k : Fin n, (fderiv ℝ (fderiv ℝ χ) p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
        ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) * s
        + 2 * (fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) * (c * ζ.2 k))
        - χ p * (s * ζ.2 k ^ 2)) =
      (∑ k : Fin n, fderiv ℝ (fderiv ℝ χ) p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
        ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))) * s
        + 2 * c * (∑ k : Fin n, ζ.2 k * fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)))
        - χ p * s * ∑ k : Fin n, ζ.2 k ^ 2 := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hb : ∑ k : Fin n, ζ.2 k * (2 * invβ * fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
        + χ p * (b p) k) =
      2 * invβ * (∑ k : Fin n, ζ.2 k * fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)))
        + χ p * ∑ k : Fin n, ζ.2 k * (b p) k := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [ha, hb, hnorm]
  ring


lemma fderiv_apply_b (χ : XS n → ℝ) (b : XS n → EuclideanSpace ℝ (Fin n)) (p : XS n) :
    fderiv ℝ χ p ((0 : ℝ), b p) =
      ∑ k : Fin n, fderiv ℝ χ p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) * (b p) k := by
  have h : ((0 : ℝ), b p) = ∑ k : Fin n, (b p) k • ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) := by
    ext
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Pi.single_apply]
  conv_lhs => rw [h]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

lemma isTest_feq (hO : IsOpen O) {b : XS n → EuclideanSpace ℝ (Fin n)}
    (hb : ContDiffOn ℝ smTop b O) (invβ : ℝ) (hg : IsTest O g) : IsTest O (feq invβ b g) := by
  have e : feq invβ b g = fun p => fderiv ℝ g p ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin n)))
      + invβ * ∑ k : Fin n, fderiv ℝ (fderiv ℝ g) p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
        ((0 : ℝ), EuclideanSpace.single k (1 : ℝ))
      + ∑ k : Fin n, fderiv ℝ g p ((0 : ℝ), EuclideanSpace.single k (1 : ℝ)) * (b p) k := by
    funext p
    simp only [feq, fderiv_apply_b]
  rw [e]
  refine ((hg.fderiv_apply _).add ?_).add ?_
  · exact IsTest.const_mul invβ (IsTest.sum _ fun k _ => hg.fderiv2_apply _ _)
  · exact IsTest.sum _ fun k _ => (hg.fderiv_apply _).mul_coord hO hb k

lemma isTest_gone (hO : IsOpen O) {b : XS n → EuclideanSpace ℝ (Fin n)}
    (hb : ContDiffOn ℝ smTop b O) (invβ : ℝ) (hg : IsTest O g) (k : Fin n) :
    IsTest O (gone invβ b g k) :=
  (IsTest.const_mul (2 * invβ) (hg.fderiv_apply _)).add (hg.mul_coord hO hb k)

/-- Test functions are integrable against a measure that is finite on compacta of `O`. -/
lemma integrable_of_supp {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤)
    {u : XS n → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ O) :
    Integrable u ρ := by
  obtain ⟨M, hM⟩ := hu.bounded_above_of_compact_support hc
  have hK : IntegrableOn u (tsupport u) ρ := by
    refine Measure.integrableOn_of_bounded (M := M) (hρ _ hs hc).ne hu.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall hM
  refine hK.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  exact image_eq_zero_of_notMem_tsupport hx

lemma IsTest.integrable {ρ : Measure (XS n)} (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤)
    (hg : IsTest O g) : Integrable g ρ :=
  integrable_of_supp hρ (hg.1.continuous) hg.2.1 hg.2.2

end HRS.MC.CepP2
