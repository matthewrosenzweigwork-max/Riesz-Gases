import Mathlib
import HRS.Sections.Q41Aux12
import HRS.Energy.StaticLimitGauss

/-!
# Packet Q41, helper 13: smooth test functions against the mode process
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal Matrix RealInnerProductSpace

namespace HRS.Q41

open HRS

/-- A linear image of a centred Gaussian vector. -/
lemma q41_linear_image_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (W : Ω → EuclideanSpace ℝ κ) (hW : AEMeasurable W P) (R : Matrix κ κ ℝ) (hR : R.PosSemidef)
    (hlaw : P.map W = multivariateGaussian 0 R) (L : Matrix ι κ ℝ) :
    P.map (fun ω => (WithLp.toLp 2 (L *ᵥ (W ω).ofLp) : EuclideanSpace ℝ ι)) =
      multivariateGaussian 0 (L * R * Lᵀ) := by
  classical
  have hLR : (L * R * Lᵀ).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hR.mul_mul_conjTranspose_same L
  have hm : Measurable (fun w : EuclideanSpace ℝ κ => (WithLp.toLp 2 (L *ᵥ w.ofLp) : EuclideanSpace ℝ ι)) := by
    fun_prop
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_multivariateGaussian hLR]
  have hmap : P.map (fun ω => (WithLp.toLp 2 (L *ᵥ (W ω).ofLp) : EuclideanSpace ℝ ι)) =
      (P.map W).map (fun w : EuclideanSpace ℝ κ => (WithLp.toLp 2 (L *ᵥ w.ofLp) : EuclideanSpace ℝ ι)) :=
    (AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hW).symm
  rw [hmap, hlaw, charFun_apply, integral_map hm.aemeasurable (by fun_prop)]
  set t' : EuclideanSpace ℝ κ := WithLp.toLp 2 (Lᵀ *ᵥ t.ofLp) with ht'
  have hip : ∀ w : EuclideanSpace ℝ κ,
      ⟪(WithLp.toLp 2 (L *ᵥ w.ofLp) : EuclideanSpace ℝ ι), t⟫ = ⟪w, t'⟫ := by
    intro w
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, ht']
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]
  simp_rw [hip]
  rw [← charFun_apply, charFun_multivariateGaussian hR]
  congr 2
  · simp
  · simp only [ht']
    have e : t.ofLp ⬝ᵥ ((L * R * Lᵀ) *ᵥ t.ofLp) = (Lᵀ *ᵥ t.ofLp) ⬝ᵥ ((R * Lᵀ) *ᵥ t.ofLp) := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
    rw [e, Matrix.mulVec_mulVec]

variable {d : ℕ}

lemma q41_summable_eval {m : ℝ} (F : NegSobolev d m) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Summable fun k : NonzeroLattice d => NegSobolev.fourierCoeff F k * Torus.funRealCoeff φ k := by
  have h1 := (NegSobolev.coord_sq F).1
  have h2 : Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) ^ 2 := by
    refine (HRS.StaticLimitAux.summable_weighted_smooth m hφ).congr fun k => ?_
    rw [mul_pow, Torus.jp_rpow_sq]
  refine Summable.of_norm_bounded (g := fun k => (NegSobolev.coord F k ^ 2 +
    (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) ^ 2)) (h1.add h2) fun k => ?_
  have : NegSobolev.fourierCoeff F k * Torus.funRealCoeff φ k =
      NegSobolev.coord F k * (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) := by
    unfold NegSobolev.fourierCoeff; ring
  rw [this, Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|NegSobolev.coord F k| - |Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k|),
    sq_abs (NegSobolev.coord F k), sq_abs (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k),
    abs_nonneg (NegSobolev.coord F k), abs_nonneg (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k)]

lemma q41_eval_tendsto {m : ℝ} (e : ℕ ≃ NonzeroLattice d) (F : NegSobolev d m)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      NegSobolev.fourierCoeff F (e i) * Torus.funRealCoeff φ (e i)) atTop
      (𝓝 (NegSobolev.eval F φ)) := by
  have h := (q41_summable_eval F hφ).hasSum
  have h' := (e.hasSum_iff (f := fun k : NonzeroLattice d =>
    NegSobolev.fourierCoeff F k * Torus.funRealCoeff φ k)).2 h
  exact h'.tendsto_sum_nat

variable {r : ℝ → ℝ → NonzeroLattice d → NonzeroLattice d → ℝ}

lemma q41_exists_equiv (hd : 1 ≤ d) : Nonempty (ℕ ≃ NonzeroLattice d) := by
  haveI : Infinite (NonzeroLattice d) := by
    refine Infinite.of_injective (fun n : ℕ => (⟨Pi.single ⟨0, by omega⟩ ((n : ℤ) + 1), by
      intro h
      have := congrFun h ⟨0, by omega⟩
      simp at this
      omega⟩ : NonzeroLattice d)) ?_
    intro a b hab
    have := congrFun (congrArg Subtype.val hab) ⟨0, by omega⟩
    simp at this
    exact_mod_cast this
  exact nonempty_equiv_of_countable

/-- **Smooth test functions.**  If the smooth-test covariance `κ` is the limit of the truncated
mode sums, the process of `q41_modes_process` is a stationary Gaussian field against smooth tests. -/
theorem q41_smooth_process (hd : 1 ≤ d) {m : ℝ} (hm : (d : ℝ) + 2 < 2 * m)
    (hr : ModeKernel d r)
    (κ : ℝ → ℝ → (Torus d → ℝ) → (Torus d → ℝ) → ℝ)
    (hκ : ∀ (e : ℕ ≃ NonzeroLattice d) (φ ψ : Torus d → ℝ), Torus.IsSmooth φ → Torus.IsSmooth ψ →
      ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
        Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
          Torus.funRealCoeff φ (e i) * Torus.funRealCoeff ψ (e j) * r t s (e i) (e j)) atTop
          (𝓝 (κ t s φ ψ))) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Z : ℝ → Ω → NegSobolev d m), (∀ t, Measurable (Z t)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0)) ∧
      ∀ (p : ℕ) (τ : Fin p → ℝ) (φ : Fin p → Torus d → ℝ), (∀ a, 0 ≤ τ a) →
        (∀ a, Torus.IsSmooth (φ a)) →
        P.map (fun ω => (WithLp.toLp 2 (fun a => NegSobolev.eval (Z (τ a) ω) (φ a)) :
          EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a b => κ (τ a) (τ b) (φ a) (φ b)) := by
  classical
  obtain ⟨Ω, mΩ, P, hP, Z, hZm, hZc, hfdd⟩ := q41_modes_process hd hm hr
  obtain ⟨e⟩ := q41_exists_equiv hd
  refine ⟨Ω, mΩ, P, hP, Z, hZm, hZc, ?_⟩
  intro p τ φ hτ hφ
  -- coordinates of the mode vector
  have hcoef : ∀ (t : ℝ) (k : NonzeroLattice d), Measurable fun ω => NegSobolev.fourierCoeff (Z t ω) k :=
    fun t k => (q41_continuous_fourierCoeff m k).measurable.comp (hZm t)
  set W : (n : ℕ) → Ω → EuclideanSpace ℝ (Fin p × Fin n) := fun n ω =>
    WithLp.toLp 2 (fun x => NegSobolev.fourierCoeff (Z (τ x.1) ω) (e x.2)) with hW
  set R : (n : ℕ) → Matrix (Fin p × Fin n) (Fin p × Fin n) ℝ := fun n =>
    Matrix.of fun x y => r (τ x.1) (τ y.1) (e x.2) (e y.2) with hR
  have hWlaw : ∀ n, P.map (W n) = multivariateGaussian 0 (R n) := fun n =>
    hfdd (Fin p × Fin n) (fun x => τ x.1) (fun x => e x.2) (fun x => hτ x.1)
  have hRpsd : ∀ n, (R n).PosSemidef := fun n =>
    hr.psd (Fin p × Fin n) (fun x => τ x.1) (fun x => e x.2) (fun x => hτ x.1)
  have hWm : ∀ n, Measurable (W n) := fun n =>
    (PiLp.continuous_toLp 2 (fun _ : Fin p × Fin n => ℝ)).measurable.comp
      (measurable_pi_iff.2 fun x => hcoef (τ x.1) (e x.2))
  set L : (n : ℕ) → Matrix (Fin p) (Fin p × Fin n) ℝ := fun n a x =>
    if a = x.1 then Torus.funRealCoeff (φ a) (e x.2) else 0 with hL
  set V : ℕ → Ω → EuclideanSpace ℝ (Fin p) := fun n ω =>
    WithLp.toLp 2 (L n *ᵥ (W n ω).ofLp) with hV
  have hVlaw : ∀ n, P.map (V n) = multivariateGaussian 0 (L n * R n * (L n)ᵀ) := fun n =>
    q41_linear_image_law P (W n) (hWm n).aemeasurable (R n) (hRpsd n) (hWlaw n) (L n)
  have hVcomp : ∀ n ω a, (V n ω).ofLp a = ∑ i ∈ Finset.range n,
      NegSobolev.fourierCoeff (Z (τ a) ω) (e i) * Torus.funRealCoeff (φ a) (e i) := by
    intro n ω a
    simp only [hV, hL, hW, WithLp.ofLp_toLp, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun i _ => by simp [Ne.symm hx])
      (by simp)]
    simp only [if_true]
    rw [← Fin.sum_univ_eq_sum_range (fun i => NegSobolev.fourierCoeff (Z (τ a) ω) (e i) *
      Torus.funRealCoeff (φ a) (e i)) n]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hS : ∀ n a b, (L n * R n * (L n)ᵀ) a b = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      Torus.funRealCoeff (φ a) (e i) * Torus.funRealCoeff (φ b) (e j) *
        r (τ a) (τ b) (e i) (e j) := by
    intro n a b
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type]
    simp only [hL, hR, Matrix.of_apply, mul_ite, ite_mul, zero_mul, mul_zero, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [Finset.sum_eq_single b (fun x _ hx => Finset.sum_eq_zero fun j _ => by simp [Ne.symm hx])
      (by simp)]
    simp only [if_true]
    have hin : ∀ j : Fin n, (∑ x_2 : Fin p, ∑ x_3 : Fin n, if a = x_2 then
        Torus.funRealCoeff (φ a) (e ↑x_3) * r (τ x_2) (τ b) (e ↑x_3) (e ↑j) else 0) =
        ∑ x_3 : Fin n, Torus.funRealCoeff (φ a) (e ↑x_3) * r (τ a) (τ b) (e ↑x_3) (e ↑j) := by
      intro j
      rw [Finset.sum_eq_single a (fun x _ hx => Finset.sum_eq_zero fun i _ => by simp [Ne.symm hx])
        (by simp)]
      simp
    simp_rw [hin]
    rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ Finset.range n, Torus.funRealCoeff (φ a) (e i) *
      Torus.funRealCoeff (φ b) (e j) * r (τ a) (τ b) (e i) (e j)) n]
    simp_rw [← Fin.sum_univ_eq_sum_range (fun j => Torus.funRealCoeff (φ a) _ *
      Torus.funRealCoeff (φ b) (e j) * r (τ a) (τ b) _ (e j)) n]
    simp_rw [Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => by ring
  have hVm : ∀ n, Measurable (V n) := fun n =>
    (by fun_prop : Measurable fun w : EuclideanSpace ℝ (Fin p × Fin n) =>
      (WithLp.toLp 2 (L n *ᵥ w.ofLp) : EuclideanSpace ℝ (Fin p))).comp (hWm n)
  have hlim : ∀ ω, Tendsto (fun n => V n ω) atTop
      (𝓝 (WithLp.toLp 2 (fun a => NegSobolev.eval (Z (τ a) ω) (φ a)) : EuclideanSpace ℝ (Fin p))) := by
    intro ω
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).tendsto _ |>.comp ?_
    refine tendsto_pi_nhds.2 fun a => ?_
    have := q41_eval_tendsto e (Z (τ a) ω) (hφ a)
    show Tendsto (fun n => (V n ω).ofLp a) atTop _
    exact this.congr fun n => (hVcomp n ω a).symm
  have hVim : Measurable (fun ω => (WithLp.toLp 2 (fun a => NegSobolev.eval (Z (τ a) ω) (φ a)) :
      EuclideanSpace ℝ (Fin p))) :=
    measurable_of_tendsto_metrizable hVm (tendsto_pi_nhds.2 hlim)
  refine q41_gauss_limit P V _ (fun n => (hVm n).aemeasurable) hVim.aemeasurable
    (fun n => L n * R n * (L n)ᵀ) _ hVlaw ?_ (Eventually.of_forall hlim) ?_
  · intro n
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using (hRpsd n).mul_mul_conjTranspose_same (L n)
  · intro a b
    simp only [hS, Matrix.of_apply]
    exact hκ e (φ a) (φ b) (hφ a) (hφ b) (τ a) (τ b) (hτ a) (hτ b)

end HRS.Q41
