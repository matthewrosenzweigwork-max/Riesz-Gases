import HRS.Sections.QuenchAux3
import HRS.Equilibrium.FieldSingAux

/-!
# Packet QUENCH (Q27), part 4: second moments of the mode coordinates

From `ModeField`: Gaussian laws of finite coordinate vectors, covariance of the noise coordinates
(`ouK`), means, independence of noise and initial coordinates, and the covariance of `Z`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ}

theorem gauss_prod_fin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (W : Ω → EuclideanSpace ℝ (Fin p)) (hW : AEMeasurable W P) (S : Matrix (Fin p) (Fin p) ℝ)
    (hS : S.PosSemidef) (h : Measure.map W P = multivariateGaussian 0 S) (a b : Fin p) :
    ∫ ω, W ω a * W ω b ∂P = S a b := by
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin p) => x a * x b := by fun_prop
  have hint : ∫ ω, W ω a * W ω b ∂P =
      ∫ x, x a * x b ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) := by
    rw [← h, integral_map hW hcont.aestronglyMeasurable]
  rw [hint]
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S with hγ
  have hmem : ∀ i : Fin p, MemLp (fun x : EuclideanSpace ℝ (Fin p) => x i) 2 γ := by
    intro i
    have := (IsGaussian.memLp_two_id (μ := γ))
    exact (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).comp_memLp' this
  have hmean : ∀ i : Fin p, ∫ x, x i ∂γ = 0 := by
    intro i
    have h := (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).integral_comp_id_comm
      (μ := γ) IsGaussian.integrable_id
    simpa [hγ, integral_id_multivariateGaussian] using h
  have hcov := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin p))) hS a b
  rw [covariance_eq_sub (hmem a) (hmem b), hmean a, hmean b] at hcov
  simpa using hcov

theorem gauss_mean_fin {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {p : ℕ}
    (W : Ω → EuclideanSpace ℝ (Fin p)) (hW : AEMeasurable W P) (S : Matrix (Fin p) (Fin p) ℝ)
    (h : Measure.map W P = multivariateGaussian 0 S) (a : Fin p) :
    ∫ ω, W ω a ∂P = 0 := by
  have hcont : Continuous fun x : EuclideanSpace ℝ (Fin p) => x a := by fun_prop
  have hint : ∫ ω, W ω a ∂P = ∫ x, x a ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) := by
    rw [← h, integral_map hW hcont.aestronglyMeasurable]
  rw [hint]
  have h := (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ).integral_comp_id_comm
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S) IsGaussian.integrable_id
  simpa [integral_id_multivariateGaussian] using h

section Noise

variable {s β β₀ m : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {Z : ℝ → Ω → NegSobolev d m} {Y : Ω → NegSobolev d m}

lemma aemeas_fc (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) :
    AEMeasurable (fun ω => NegSobolev.fourierCoeff (Y ω) j) P :=
  (HRS.FieldSingAux.coordCLM m j).continuous.measurable.comp_aemeasurable mf.measY

lemma meas_fcZ (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) (t : ℝ) :
    Measurable (fun ω => NegSobolev.fourierCoeff (Z t ω) j) :=
  (HRS.FieldSingAux.coordCLM m j).continuous.measurable.comp (mf.meas t)

lemma aemeas_ncoord (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) (t : ℝ) :
    AEMeasurable (ncoord s β Y Z j t) P :=
  (meas_fcZ mf j t).aemeasurable.sub ((aemeas_fc mf j).const_mul _)

lemma aemeas_Gvec (mf : ModeField d s β β₀ m P Z Y) {p : ℕ} (js : Fin p → NonzeroLattice d)
    (ts : Fin p → ℝ) :
    AEMeasurable (fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (js a) (ts a) ω) :
      EuclideanSpace ℝ (Fin p))) P := by
  have : AEMeasurable (fun ω => fun a => ncoord s β Y Z (js a) (ts a) ω) P :=
    aemeasurable_pi_iff.2 fun a => aemeas_ncoord mf (js a) (ts a)
  exact (PiLp.continuous_toLp 2 _).measurable.comp_aemeasurable this

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

include hd hs0 hsd hβ in
lemma Gvec_psd (mf : ModeField d s β β₀ m P Z Y) {p : ℕ} (js : Fin p → NonzeroLattice d)
    (ts : Fin p → ℝ) (ht : ∀ a, 0 ≤ ts a) :
    (covMat (fun j => varMode d s β j.1) (fun j => lamMode d s β j.1) js ts).PosSemidef :=
  covMat_posSemidef _ _ (fun j => (varMode_pos hd hs0 hsd hβ j).le)
    (fun j => lamMode_pos hd hs0 hsd hβ j) js ts ht

include hd hs0 hsd hβ in
/-- `E[G_j(t) G_{j'}(r)] = δ_{jj'} v_{β,j} K_{λ_j}(t,r)`. -/
theorem noise_cov (mf : ModeField d s β β₀ m P Z Y) (j j' : NonzeroLattice d) {t r : ℝ}
    (ht : 0 ≤ t) (hr : 0 ≤ r) :
    ∫ ω, ncoord s β Y Z j t ω * ncoord s β Y Z j' r ω ∂P =
      if j = j' then varMode d s β j.1 * ouK (lamMode d s β j.1) t r else 0 := by
  have hts : ∀ a : Fin 2, 0 ≤ (![t, r] : Fin 2 → ℝ) a := by
    intro a; fin_cases a <;> simp [ht, hr]
  obtain ⟨-, hl⟩ := mf.gp 2 ![j, j'] ![t, r] hts
  have := gauss_prod_fin P _ (aemeas_Gvec mf ![j, j'] ![t, r])
    (covMat (fun j => varMode d s β j.1) (fun j => lamMode d s β j.1) ![j, j'] ![t, r])
    (Gvec_psd hd hs0 hsd hβ mf _ _ hts) hl 0 1
  simpa [covMat] using this

include hd hs0 hsd hβ in
theorem noise_mean (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, ncoord s β Y Z j t ω ∂P = 0 := by
  have hts : ∀ a : Fin 1, 0 ≤ (![t] : Fin 1 → ℝ) a := by
    intro a; fin_cases a; simpa using ht
  obtain ⟨-, hl⟩ := mf.gp 1 ![j] ![t] hts
  have := gauss_mean_fin P _ (aemeas_Gvec mf ![j] ![t]) _ hl 0
  simpa using this

include hd hs0 hsd hβ in
lemma memLp2_ncoord (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (ncoord s β Y Z j t) 2 P := by
  have hts : ∀ a : Fin 1, 0 ≤ (![t] : Fin 1 → ℝ) a := by
    intro a; fin_cases a; simpa using ht
  obtain ⟨-, hl⟩ := mf.gp 1 ![j] ![t] hts
  haveI : IsGaussian (Measure.map (fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (![j] a) (![t] a) ω) :
      EuclideanSpace ℝ (Fin 1))) P) := by rw [hl]; infer_instance
  have hG := IsGaussian.hasGaussianLaw (aemeas_Gvec mf ![j] ![t])
  have := ((hG.map (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ)).memLp_two)
  simpa [Function.comp_def] using this

lemma memLp2_fcY (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) :
    MemLp (fun ω => NegSobolev.fourierCoeff (Y ω) j) 2 P := by
  have h1 := mf.cenY.1
  have := IsGaussian.memLp_dual (P.map Y) (HRS.FieldSingAux.coordCLM m j) 2 (by simp)
  have hmeas : AEMeasurable Y P := mf.measY
  rw [memLp_map_measure_iff (HRS.FieldSingAux.coordCLM m j).continuous.measurable.aestronglyMeasurable hmeas] at this
  exact this

lemma mean_fcY (mf : ModeField d s β β₀ m P Z Y) (j : NonzeroLattice d) :
    ∫ ω, NegSobolev.fourierCoeff (Y ω) j ∂P = 0 := by
  have h := mf.cenY.2 (HRS.FieldSingAux.coordCLM m j)
  rw [integral_map mf.measY (HRS.FieldSingAux.coordCLM m j).continuous.measurable.aestronglyMeasurable] at h
  exact h

include hd hs0 hsd hβ in
lemma indep_ncoord_fcY (mf : ModeField d s β β₀ m P Z Y) (j j' : NonzeroLattice d) {t : ℝ} (ht : 0 ≤ t) :
    IndepFun (ncoord s β Y Z j t) (fun ω => NegSobolev.fourierCoeff (Y ω) j') P := by
  have hts : ∀ a : Fin 1, 0 ≤ (![t] : Fin 1 → ℝ) a := by
    intro a; fin_cases a; simpa using ht
  obtain ⟨hi, -⟩ := mf.gp 1 ![j] ![t] hts
  have := hi.comp (φ := fun v : EuclideanSpace ℝ (Fin 1) => v 0)
    (ψ := fun F : NegSobolev d m => NegSobolev.fourierCoeff F j')
    (by fun_prop) (HRS.FieldSingAux.coordCLM m j').continuous.measurable
  have e : (ncoord s β Y Z j t) = ((fun v : EuclideanSpace ℝ (Fin 1) => v 0) ∘
      fun ω => (WithLp.toLp 2 (fun a => ncoord s β Y Z (![j] a) (![t] a) ω) : EuclideanSpace ℝ (Fin 1))) := by
    funext ω; simp
  rw [e]
  exact this

include hd hs0 hsd hβ in
theorem Z_cov (mf : ModeField d s β β₀ m P Z Y) (j j' : NonzeroLattice d) {t r : ℝ}
    (ht : 0 ≤ t) (hr : 0 ≤ r) :
    ∫ ω, NegSobolev.fourierCoeff (Z t ω) j * NegSobolev.fourierCoeff (Z r ω) j' ∂P =
      if j = j' then varMode d s β j.1 * Real.exp (-(lamMode d s β j.1) * |t - r|) +
        deltaVar d s β β₀ j.1 * Real.exp (-(lamMode d s β j.1) * (t + r)) else 0 := by
  set e : NonzeroLattice d → ℝ → ℝ := fun j t => Real.exp (-(lamMode d s β j.1) * t) with he
  have hZ : ∀ j t ω, NegSobolev.fourierCoeff (Z t ω) j =
      ncoord s β Y Z j t ω + e j t * NegSobolev.fourierCoeff (Y ω) j := by
    intro j t ω; simp only [ncoord, he]; ring
  have hmG : ∀ j {t : ℝ}, 0 ≤ t → MemLp (ncoord s β Y Z j t) 2 P := fun j t ht =>
    memLp2_ncoord hd hs0 hsd hβ mf j ht
  have hmY := memLp2_fcY mf
  have hcross : ∀ j j' {t : ℝ}, 0 ≤ t →
      ∫ ω, ncoord s β Y Z j t ω * NegSobolev.fourierCoeff (Y ω) j' ∂P = 0 := by
    intro j j' t ht
    have := (indep_ncoord_fcY hd hs0 hsd hβ mf j j' ht).integral_mul_eq_mul_integral
      (hmG j ht).aestronglyMeasurable (hmY j').aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, mean_fcY mf j', mul_zero]
  have hint2 : ∀ {f g : Ω → ℝ}, MemLp f 2 P → MemLp g 2 P → Integrable (fun ω => f ω * g ω) P :=
    fun hf hg => hf.integrable_mul hg
  have e1 : ∀ ω, NegSobolev.fourierCoeff (Z t ω) j * NegSobolev.fourierCoeff (Z r ω) j' =
      ncoord s β Y Z j t ω * ncoord s β Y Z j' r ω +
      e j' r * (ncoord s β Y Z j t ω * NegSobolev.fourierCoeff (Y ω) j') +
      e j t * (ncoord s β Y Z j' r ω * NegSobolev.fourierCoeff (Y ω) j) +
      (e j t * e j' r) * (NegSobolev.fourierCoeff (Y ω) j * NegSobolev.fourierCoeff (Y ω) j') := by
    intro ω
    rw [hZ j t ω, hZ j' r ω]; ring
  simp_rw [e1]
  have iGG : Integrable (fun ω => ncoord s β Y Z j t ω * ncoord s β Y Z j' r ω) P :=
    hint2 (hmG j ht) (hmG j' hr)
  have iGY : Integrable (fun ω => ncoord s β Y Z j t ω * NegSobolev.fourierCoeff (Y ω) j') P :=
    hint2 (hmG j ht) (hmY j')
  have iGY' : Integrable (fun ω => ncoord s β Y Z j' r ω * NegSobolev.fourierCoeff (Y ω) j) P :=
    hint2 (hmG j' hr) (hmY j)
  have iYY : Integrable (fun ω => NegSobolev.fourierCoeff (Y ω) j * NegSobolev.fourierCoeff (Y ω) j') P :=
    hint2 (hmY j) (hmY j')
  have hsplit : ∀ (A B C D : Ω → ℝ), Integrable A P → Integrable B P → Integrable C P → Integrable D P →
      ∫ ω, (A ω + B ω + C ω + D ω) ∂P = ∫ ω, A ω ∂P + ∫ ω, B ω ∂P + ∫ ω, C ω ∂P + ∫ ω, D ω ∂P := by
    intro A B C D hA hB hC hD
    have h1 : Integrable (fun ω => A ω + B ω) P := hA.add hB
    have h2 : Integrable (fun ω => A ω + B ω + C ω) P := h1.add hC
    rw [integral_add (f := fun ω => A ω + B ω + C ω) (g := D) h2 hD,
      integral_add (f := fun ω => A ω + B ω) (g := C) h1 hC,
      integral_add (f := A) (g := B) hA hB]
  rw [hsplit _ _ _ _ iGG (iGY.const_mul (e j' r)) (iGY'.const_mul (e j t)) (iYY.const_mul (e j t * e j' r)),
    integral_const_mul, integral_const_mul, integral_const_mul, hcross j j' ht, hcross j' j hr, mf.covY,
    noise_cov hd hs0 hsd hβ mf j j' ht hr]
  by_cases h : j = j'
  · subst h
    simp only [ite_true, mul_zero, add_zero]
    unfold deltaVar ouK
    simp only [he]
    have : Real.exp (-(lamMode d s β j.1) * (t + r)) =
        Real.exp (-(lamMode d s β j.1) * t) * Real.exp (-(lamMode d s β j.1) * r) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    ring
  · simp [h]

end Noise

end Qch

end HRS
