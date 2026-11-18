import HRS.MC.SEdgeB8bAux5
import HRS.MC.SEdgeB8a

/-!
# Packet B8b, helper file 6: the finite-dimensional Wick identity for the truncations
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

open HRS HRS.Sec7 HRS.Q08

section Stage

variable {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}

theorem b8b_sum4 {ι κ μ ν : Type*} (s : Finset ι) (t : Finset κ) (u : Finset μ) (v : Finset ν)
    (f : ι → κ → μ → ν → ℝ) :
    ∑ i ∈ s, ∑ j ∈ t, ∑ b ∈ u, ∑ c ∈ v, f i j b c = ∑ b ∈ u, ∑ c ∈ v, ∑ i ∈ s, ∑ j ∈ t, f i j b c := by
  calc ∑ i ∈ s, ∑ j ∈ t, ∑ b ∈ u, ∑ c ∈ v, f i j b c
      = ∑ i ∈ s, ∑ b ∈ u, ∑ j ∈ t, ∑ c ∈ v, f i j b c :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ b ∈ u, ∑ i ∈ s, ∑ j ∈ t, ∑ c ∈ v, f i j b c := Finset.sum_comm
    _ = ∑ b ∈ u, ∑ i ∈ s, ∑ c ∈ v, ∑ j ∈ t, f i j b c :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun b _ => Finset.sum_comm

/-- `G_i G_j` is square integrable for `i, j < L` -/
theorem b8b_GG_memLp (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hGm : ∀ i, Measurable (G i)) (S : ℕ → ℕ → ℝ)
    (hSpsd : ∀ n, (Matrix.of fun i j : Fin n => S i j).PosSemidef)
    (hlaw : ∀ n, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω :
        EuclideanSpace ℝ (Fin n))) = multivariateGaussian 0 (Matrix.of fun i j : Fin n => S i j))
    {L i j : ℕ} (hi : i < L) (hj : j < L) : MemLp (fun ω => G i ω * G j ω) 2 P := by
  have hV : Measurable (fun ω => (WithLp.toLp 2 fun k : Fin L => G k ω : EuclideanSpace ℝ (Fin L))) := by
    fun_prop
  have h1 := q08c_ch_pair_int (hSpsd L) (Pi.single ⟨i, hi⟩ 1) (Pi.single ⟨j, hj⟩ 1)
  rw [← hlaw L] at h1
  have h2 := (integrable_map_measure (by
    exact (((q08c_ch_lin_meas _).pow_const 2).mul ((q08c_ch_lin_meas _).pow_const 2)).aestronglyMeasurable)
    hV.aemeasurable).1 h1
  refine (memLp_two_iff_integrable_sq (f := fun ω => G i ω * G j ω)
    ((hGm i).mul (hGm j)).aestronglyMeasurable).2 ?_
  refine h2.congr (Eventually.of_forall fun ω => ?_)
  simp [q08c_ch_lin, Pi.single_apply, mul_pow]

/-- `T_{b,i} = ∑_{k<L} α_{b k} S_{k i}` -/
def b8b_T (α : Fin p → ℕ → ℝ) (S : ℕ → ℕ → ℝ) (L : ℕ) (b : Fin p) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range L, α b k * S k i

/-- the truncated Hilbert-Schmidt pairing `∑_{i,j<L} H_ij T_{b i} T_{c j}` -/
def b8b_Theta (α : Fin p → ℕ → ℝ) (S H : ℕ → ℕ → ℝ) (L : ℕ) (b c : Fin p) : ℝ :=
  ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * b8b_T α S L b i * b8b_T α S L c j

/-- the truncated chaos `Q_L` -/
def b8b_qL (S H : ℕ → ℕ → ℝ) (G : ℕ → Ω → ℝ) (L : ℕ) (ω : Ω) : ℝ :=
  (1 / 2) * ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, H i j * (G i ω * G j ω - S i j)

theorem b8b_cont_F {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 2 ψ) (b c : Fin p) :
    Continuous (fun z => iteratedFDeriv ℝ 2 ψ z ![stdVec b, stdVec c]) :=
  (hψ.1.continuous_iteratedFDeriv (le_refl 2)).eval_const _

theorem b8b_stage (P : Measure Ω) [IsProbabilityMeasure P] (G : ℕ → Ω → ℝ)
    (hGm : ∀ i, Measurable (G i)) (S : ℕ → ℕ → ℝ)
    (hSpsd : ∀ n, (Matrix.of fun i j : Fin n => S i j).PosSemidef)
    (hlaw : ∀ n, law P (fun ω => (WithLp.toLp 2 fun i : Fin n => G i ω :
        EuclideanSpace ℝ (Fin n))) = multivariateGaussian 0 (Matrix.of fun i j : Fin n => S i j))
    (α : Fin p → ℕ → ℝ) (H : ℕ → ℕ → ℝ) (L : ℕ) {ψ : EuclideanSpace ℝ (Fin p) → ℝ}
    (hψ : MemCb 2 ψ) :
    ∫ ω, b8b_qL S H G L ω * ψ (b8b_XL α G L ω) ∂P =
      (1 / 2) * ∑ b, ∑ c, b8b_Theta α S H L b c *
        ∫ ω, iteratedFDeriv ℝ 2 ψ (b8b_XL α G L ω) ![stdVec b, stdVec c] ∂P := by
  set V : Ω → EuclideanSpace ℝ (Fin L) := fun ω => WithLp.toLp 2 fun i : Fin L => G i ω with hV
  have hVm : Measurable V := by rw [hV]; fun_prop
  set Φ : EuclideanSpace ℝ (Fin L) → EuclideanSpace ℝ (Fin p) :=
    fun g => WithLp.toLp 2 fun b => ∑ k : Fin L, α b k * g.ofLp k with hΦ
  have hΦc : Continuous Φ := by rw [hΦ]; fun_prop
  have hXV : ∀ ω, b8b_XL α G L ω = Φ (V ω) := by
    intro ω
    simp only [b8b_XL, hΦ, hV]
    congr 1
    ext b
    exact (Fin.sum_univ_eq_sum_range (fun k => α b k * G k ω) L).symm
  have hXm : Measurable (b8b_XL α G L) := by
    have : b8b_XL α G L = fun ω => Φ (V ω) := funext hXV
    rw [this]; exact hΦc.measurable.comp hVm
  have hψc : Continuous ψ := hψ.1.continuous
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, |ψ x| ≤ M := by
    obtain ⟨M, hM⟩ := hψ.2 0 (Nat.zero_le _)
    exact ⟨M, fun x => by
      have := hM ⟨x, rfl⟩
      simpa using this⟩
  have hmap : ∀ f : EuclideanSpace ℝ (Fin L) → ℝ, Continuous f →
      ∫ g, f g ∂(multivariateGaussian 0 (Matrix.of fun i j : Fin L => S i j)) =
        ∫ ω, f (V ω) ∂P := by
    intro f hf
    rw [← hlaw L]
    exact integral_map hVm.aemeasurable hf.aestronglyMeasurable
  have key : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range L,
      ∫ ω, (G i ω * G j ω - S i j) * ψ (b8b_XL α G L ω) ∂P =
        ∑ b, ∑ c, b8b_T α S L b i * b8b_T α S L c j *
          ∫ ω, iteratedFDeriv ℝ 2 ψ (b8b_XL α G L ω) ![stdVec b, stdVec c] ∂P := by
    intro i hi j hj
    have hi' : i < L := Finset.mem_range.1 hi
    have hj' : j < L := Finset.mem_range.1 hj
    have h8 := HRS.MC.SEdge.B8a.sed_B8a_gauss_ibp2_proof (Matrix.of fun i j : Fin L => S i j)
      (hSpsd L) (fun b (k : Fin L) => α b k) ⟨i, hi'⟩ ⟨j, hj'⟩ hψ
    have c1 : Continuous fun g : EuclideanSpace ℝ (Fin L) =>
        (g.ofLp ⟨i, hi'⟩ * g.ofLp ⟨j, hj'⟩ - (Matrix.of fun i j : Fin L => S i j) ⟨i, hi'⟩ ⟨j, hj'⟩) *
          ψ (WithLp.toLp 2 fun b => ∑ k, (fun b (k : Fin L) => α b k) b k * g.ofLp k) := by
      have : Continuous fun g : EuclideanSpace ℝ (Fin L) =>
          ψ (WithLp.toLp 2 fun b => ∑ k, (fun b (k : Fin L) => α b k) b k * g.ofLp k) :=
        hψc.comp hΦc
      refine Continuous.mul ?_ this
      fun_prop
    rw [hmap _ c1] at h8
    have e1 : ∫ ω, (G i ω * G j ω - S i j) * ψ (b8b_XL α G L ω) ∂P = ∫ ω,
        ((V ω).ofLp ⟨i, hi'⟩ * (V ω).ofLp ⟨j, hj'⟩ -
          (Matrix.of fun i j : Fin L => S i j) ⟨i, hi'⟩ ⟨j, hj'⟩) *
          ψ (WithLp.toLp 2 fun b => ∑ k, (fun b (k : Fin L) => α b k) b k * (V ω).ofLp k) ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hV, Matrix.of_apply, hXV, hΦ]
    have hI : ∀ b c, ∫ g : EuclideanSpace ℝ (Fin L), (iteratedFDeriv ℝ 2 ψ
        (WithLp.toLp 2 fun a => ∑ k : Fin L, α a (k : ℕ) * g.ofLp k)) ![stdVec b, stdVec c]
        ∂(multivariateGaussian 0 (Matrix.of fun i j : Fin L => S i j)) =
        ∫ ω, iteratedFDeriv ℝ 2 ψ (b8b_XL α G L ω) ![stdVec b, stdVec c] ∂P := by
      intro b c
      have := hmap (fun g => iteratedFDeriv ℝ 2 ψ (Φ g) ![stdVec b, stdVec c])
        ((b8b_cont_F hψ b c).comp hΦc)
      refine this.trans (integral_congr_ae (Eventually.of_forall fun ω => ?_))
      simp only [hXV]
    rw [e1, h8]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hI b c]
    simp only [b8b_T, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun k => α b k * S k i) L,
      Fin.sum_univ_eq_sum_range (fun l => α c l * S l j) L]
  have hint : ∀ i ∈ Finset.range L, ∀ j ∈ Finset.range L,
      Integrable (fun ω => (G i ω * G j ω - S i j) * ψ (b8b_XL α G L ω)) P := by
    intro i hi j hj
    have hmem := b8b_GG_memLp P G hGm S hSpsd hlaw (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)
    have h1 : Integrable (fun ω => G i ω * G j ω - S i j) P :=
      (hmem.integrable one_le_two).sub (integrable_const _)
    exact h1.mul_bdd (hψc.measurable.comp hXm).aestronglyMeasurable
      (Eventually.of_forall fun ω => by simpa [Real.norm_eq_abs] using hM _)
  have step1 : ∀ ω, b8b_qL S H G L ω * ψ (b8b_XL α G L ω) = (1 / 2) * ∑ i ∈ Finset.range L,
      ∑ j ∈ Finset.range L, H i j * ((G i ω * G j ω - S i j) * ψ (b8b_XL α G L ω)) := by
    intro ω
    unfold b8b_qL
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [step1]
  rw [integral_const_mul]
  congr 1
  rw [integral_finset_sum _ fun i hi => integrable_finset_sum _ fun j hj =>
    (hint i hi j hj).const_mul _]
  have step2 : ∀ i ∈ Finset.range L, ∫ ω, ∑ j ∈ Finset.range L,
      H i j * ((G i ω * G j ω - S i j) * ψ (b8b_XL α G L ω)) ∂P =
      ∑ j ∈ Finset.range L, H i j * ∑ b, ∑ c, b8b_T α S L b i * b8b_T α S L c j *
        ∫ ω, iteratedFDeriv ℝ 2 ψ (b8b_XL α G L ω) ![stdVec b, stdVec c] ∂P := by
    intro i hi
    rw [integral_finset_sum _ fun j hj => (hint i hi j hj).const_mul _]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [integral_const_mul, key i hi j hj]
  rw [Finset.sum_congr rfl step2]
  simp_rw [Finset.mul_sum]
  rw [b8b_sum4]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  unfold b8b_Theta
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end Stage

end HRS.MC.SEdge.B8b
