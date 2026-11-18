import HRS.MC.E718B1

/-!
# Row 7.18 (packet e718b), file 2: quadratic forms in an orthonormal family
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.E718B

section
open Matrix

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : H → Ω → ℝ}

lemma IsIsonormal.aemeasurable_W (hW : IsIsonormal P W) (u : H) (hu : u ≠ 0) : AEMeasurable (W u) P := by
  have h1 := hW.aemeasurable_vec (n := 1) (fun _ => u) ⟨0, hu⟩
  have h2 : Continuous fun x : EuclideanSpace ℝ (Fin 1) => x.ofLp 0 := by fun_prop
  exact h2.measurable.comp_aemeasurable h1

lemma orthonormal_ne_zero {m : ℕ} {f : Fin m → H} (hf : Orthonormal ℝ f) (i : Fin m) : f i ≠ 0 :=
  hf.ne_zero i

/-- The vector `(W f_i)_i` of an orthonormal family is a standard Gaussian vector. -/
lemma IsIsonormal.law_pi (hW : IsIsonormal P W) {m : ℕ} (hm : 0 < m) (f : Fin m → H) (hf : Orthonormal ℝ f) :
    P.map (fun ω (i : Fin m) => W (f i) ω) = Measure.pi (fun _ : Fin m => gaussianReal 0 1) := by
  have hX := hW.aemeasurable_vec f ⟨⟨0, hm⟩, hf.ne_zero _⟩
  have hgram : (Matrix.of fun i j : Fin m => inner ℝ (f i) (f j)) = 1 := by
    ext i j
    rw [Matrix.of_apply, orthonormal_iff_ite.1 hf i j]
    simp [Matrix.one_apply]
  have h1 := hW m f
  unfold HRS.law at h1
  rw [hgram, multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian] at h1
  have hm' : Measurable (fun x : EuclideanSpace ℝ (Fin m) => x.ofLp) := by fun_prop
  have h2 : P.map (fun ω (i : Fin m) => W (f i) ω) =
      (P.map (fun ω => (WithLp.toLp 2 fun i : Fin m => W (f i) ω : EuclideanSpace ℝ (Fin m)))).map
        (fun x : EuclideanSpace ℝ (Fin m) => x.ofLp) := by
    rw [AEMeasurable.map_map_of_aemeasurable hm'.aemeasurable hX]; rfl
  rw [h2, h1, Measure.map_map hm' (by fun_prop)]
  exact Measure.map_id

lemma IsIsonormal.aemeasurable_vecf (hW : IsIsonormal P W) {m : ℕ} (f : Fin m → H)
    (hf : Orthonormal ℝ f) : AEMeasurable (fun ω (i : Fin m) => W (f i) ω) P :=
  aemeasurable_pi_iff.2 fun i => hW.aemeasurable_W _ (hf.ne_zero i)

/-- The centred quadratic polynomial `∑ c_kl (z_k z_l - δ_kl)` on `ℝ^m`. -/
def qpoly {m : ℕ} (c : Fin m → Fin m → ℝ) (z : Fin m → ℝ) : ℝ :=
  ∑ k, ∑ l, c k l * (z k * z l - if k = l then 1 else 0)

/-- `½ ∑ c_kl (W f_k W f_l - δ_kl)`. -/
def Phi (W : H → Ω → ℝ) {m : ℕ} (f : Fin m → H) (c : Fin m → Fin m → ℝ) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ k, ∑ l, c k l * (W (f k) ω * W (f l) ω - if k = l then 1 else 0)

lemma Phi_eq {m : ℕ} (f : Fin m → H) (c : Fin m → Fin m → ℝ) (ω : Ω) :
    Phi W f c ω = (1 / 2) * qpoly c (fun i => W (f i) ω) := rfl

lemma qpoly_eq {m : ℕ} (c : Fin m → Fin m → ℝ) (z : Fin m → ℝ) :
    qpoly c z = z ⬝ᵥ ((Matrix.of c) *ᵥ z) - (Matrix.of c).trace := by
  unfold qpoly
  simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, dotProduct, Matrix.mulVec]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

lemma pi_memLp_prod {m : ℕ} (k l : Fin m) :
    MemLp (fun z : Fin m → ℝ => z k * z l) 2 (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
  have hm : AEStronglyMeasurable (fun z : Fin m → ℝ => z k * z l)
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by fun_prop
  rw [memLp_two_iff_integrable_sq hm]
  have hi : ∀ k : Fin m, Integrable (fun y : Fin m → ℝ => y k ^ 4)
      (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := fun k =>
    HRS.pi_integrable_eval m (fun x => x ^ 4) (by fun_prop) (HRS.gauss_integrable_pow 4) k
  refine Integrable.mono' (((hi k).add (hi l)).const_mul (1/2))
    (hm.pow 2) (Filter.Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [sq_nonneg (z k ^ 2 - z l ^ 2)]

lemma pi_memLp_qpoly {m : ℕ} (c : Fin m → Fin m → ℝ) :
    MemLp (qpoly c) 2 (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
  have : qpoly c = ∑ k, ∑ l, fun z : Fin m → ℝ => c k l * (z k * z l - if k = l then 1 else 0) := by
    ext z; simp [qpoly]
  rw [this]
  refine memLp_finsetSum' _ fun k _ => memLp_finsetSum' _ fun l _ => ?_
  exact ((pi_memLp_prod k l).sub (memLp_const _)).const_mul _

/-- Variance of the quadratic form in an orthonormal family. -/
lemma IsIsonormal.Phi_memLp_integral (hW : IsIsonormal P W) {m : ℕ} (hm : 0 < m) (f : Fin m → H)
    (hf : Orthonormal ℝ f) (c : Fin m → Fin m → ℝ) (hc : ∀ k l, c k l = c l k) :
    MemLp (Phi W f c) 2 P ∧ ∫ ω, Phi W f c ω ^ 2 ∂P = (1 / 2) * ∑ k, ∑ l, c k l ^ 2 := by
  have hZ := hW.aemeasurable_vecf f hf
  have hlaw := hW.law_pi hm f hf
  have hg : MemLp (fun z => (1 / 2) * qpoly c z) 2 (Measure.pi (fun _ : Fin m => gaussianReal 0 1)) :=
    (pi_memLp_qpoly c).const_mul _
  have hfun : Phi W f c = (fun z => (1 / 2) * qpoly c z) ∘ (fun ω (i : Fin m) => W (f i) ω) := rfl
  constructor
  · rw [hfun]
    rw [← hlaw] at hg
    exact (memLp_map_measure_iff hg.aestronglyMeasurable hZ).1 hg
  · have hcont : Continuous fun z : Fin m → ℝ => ((1 / 2) * qpoly c z) ^ 2 := by
      unfold qpoly; fun_prop
    have e1 : ∫ ω, Phi W f c ω ^ 2 ∂P =
        ∫ z, ((1 / 2) * qpoly c z) ^ 2 ∂(Measure.pi (fun _ : Fin m => gaussianReal 0 1)) := by
      rw [← hlaw, integral_map hZ hcont.aestronglyMeasurable]
      rfl
    rw [e1]
    have hH : (Matrix.of c).IsHermitian := by
      ext i j
      simp [Matrix.conjTranspose_apply, hc i j]
    simp_rw [mul_pow, qpoly_eq]
    rw [integral_const_mul, HRS.quad_L2 m _ hH, HRS.vGauss_eq]
    simp only [Matrix.of_apply]
    ring

section Alg
open Finset

lemma sum4_comm {m : ℕ} (L : ℕ) (F : ℕ → ℕ → Fin m → Fin m → ℝ) :
    ∑ i ∈ range L, ∑ j ∈ range L, ∑ k, ∑ l, F i j k l =
      ∑ k, ∑ l, ∑ i ∈ range L, ∑ j ∈ range L, F i j k l := by
  calc ∑ i ∈ range L, ∑ j ∈ range L, ∑ k, ∑ l, F i j k l
      = ∑ i ∈ range L, ∑ k, ∑ j ∈ range L, ∑ l, F i j k l :=
        sum_congr rfl fun i _ => sum_comm
    _ = ∑ k, ∑ i ∈ range L, ∑ j ∈ range L, ∑ l, F i j k l := sum_comm
    _ = ∑ k, ∑ i ∈ range L, ∑ l, ∑ j ∈ range L, F i j k l :=
        sum_congr rfl fun k _ => sum_congr rfl fun i _ => sum_comm
    _ = ∑ k, ∑ l, ∑ i ∈ range L, ∑ j ∈ range L, F i j k l :=
        sum_congr rfl fun k _ => sum_comm

lemma alg_quad (L m : ℕ) (a : ℕ → ℕ → ℝ) (α : ℕ → Fin m → ℝ) (X : Fin m → ℝ) (Y : ℕ → ℝ)
    (hY : ∀ i < L, Y i = ∑ k, α i k * X k)
    (hG : ∀ i < L, ∀ j < L, ∑ k, α i k * α j k = if i = j then 1 else 0) :
    ∑ i ∈ range L, ∑ j ∈ range L, a i j * (Y i * Y j - if i = j then 1 else 0) =
      ∑ k, ∑ l, (∑ i ∈ range L, ∑ j ∈ range L, a i j * α i k * α j l) *
        (X k * X l - if k = l then 1 else 0) := by
  have h1 : ∑ i ∈ range L, ∑ j ∈ range L, a i j * (Y i * Y j) =
      ∑ k, ∑ l, (∑ i ∈ range L, ∑ j ∈ range L, a i j * α i k * α j l) * (X k * X l) := by
    have : ∀ i ∈ range L, ∀ j ∈ range L, a i j * (Y i * Y j) =
        ∑ k, ∑ l, a i j * α i k * α j l * (X k * X l) := by
      intro i hi j hj
      rw [hY i (mem_range.1 hi), hY j (mem_range.1 hj), sum_mul_sum, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun l _ => by ring
    rw [sum_congr rfl fun i hi => sum_congr rfl (this i hi)]
    rw [sum4_comm L (fun i j k l => a i j * α i k * α j l * (X k * X l))]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    simp_rw [sum_mul]
  have h2 : ∑ i ∈ range L, ∑ j ∈ range L, a i j * (if i = j then (1:ℝ) else 0) =
      ∑ k, ∑ l, (∑ i ∈ range L, ∑ j ∈ range L, a i j * α i k * α j l) * (if k = l then (1:ℝ) else 0) := by
    have e1 : ∑ k : Fin m, ∑ l : Fin m, (∑ i ∈ range L, ∑ j ∈ range L, a i j * α i k * α j l) *
        (if k = l then (1:ℝ) else 0) =
        ∑ k : Fin m, ∑ i ∈ range L, ∑ j ∈ range L, a i j * α i k * α j k := by
      refine sum_congr rfl fun k _ => ?_
      simp [mul_ite]
    rw [e1]
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun i hi => ?_
    conv_rhs => rw [sum_comm]
    refine sum_congr rfl fun j hj => ?_
    have := hG i (mem_range.1 hi) j (mem_range.1 hj)
    calc a i j * (if i = j then (1:ℝ) else 0) = a i j * ∑ k, α i k * α j k := by rw [this]
      _ = _ := by rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  simp_rw [mul_sub, sum_sub_distrib]
  rw [h1, h2]

end Alg

/-- Representation of a section as a quadratic form in the orthonormal family `f`. -/
lemma IsIsonormal.rep (hW : IsIsonormal P W) {m : ℕ} (f : Fin m → H) (hf : Orthonormal ℝ f) (L : ℕ)
    (g : ℕ → H) (hg : Orthonormal ℝ g)
    (hspan : ∀ i < L, g i = ∑ k, inner ℝ (f k) (g i) • f k) (a : ℕ → ℕ → ℝ) :
    (fun ω => (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        a i j * (W (g i) ω * W (g j) ω - if i = j then 1 else 0)) =ᵐ[P]
      Phi W f (fun k l => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
        a i j * inner ℝ (f k) (g i) * inner ℝ (f l) (g j)) := by
  have hae : ∀ i : ℕ, ∀ᵐ ω ∂P, i < L → W (g i) ω = ∑ k, inner ℝ (f k) (g i) * W (f k) ω := by
    intro i
    by_cases hi : i < L
    · filter_upwards [hW.comb_ae f (fun k => inner ℝ (f k) (g i)) (g i) (hspan i hi) (hg.ne_zero i)]
        with ω hω _ using hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hi
  filter_upwards [ae_all_iff.2 hae] with ω hω
  have hG : ∀ i < L, ∀ j < L, ∑ k, inner ℝ (f k) (g i) * inner ℝ (f k) (g j) =
      if i = j then 1 else 0 := by
    intro i hi j hj
    have h1 : inner ℝ (g i) (g j) = ∑ k, inner ℝ (f k) (g i) * inner ℝ (f k) (g j) := by
      conv_lhs => rw [hspan i hi]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [real_inner_smul_left]
    rw [← h1, orthonormal_iff_ite.1 hg i j]
  unfold Phi
  congr 1
  exact alg_quad L m a (fun i k => inner ℝ (f k) (g i)) (fun k => W (f k) ω) (fun i => W (g i) ω)
    (fun i hi => hω i hi) hG

end

end HRS.MC.E718B
