import HRS.MC.QRPChaosAux1

/-!
# Packet CHAOS-LP (aux 2): decoupled Gaussian bilinear forms

`‖uᵀ A v‖_{L^p} ≤ K ‖A‖_HS (‖id‖_{L^p(N(0,1))})²` for independent centred Gaussian vectors `u, v`
with covariance operator bound `K`, no diagonalisation needed.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.QRPChaos

variable {ι : Type} [Fintype ι]

lemma qpc_pow_eLpNorm {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) μ ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := p.toNNReal)
    (by simpa using hp) hf
  have e : ((p.toNNReal : ℝ≥0) : ℝ) = p := Real.coe_toNNReal _ hp.le
  rw [e] at h
  simpa [ENNReal.ofReal] using h

/-- Fubini for `L^p` norms on a product. -/
lemma qpc_prod_pow {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [SFinite μ] [SFinite ν] (F : α × β → ℝ) (hF : Measurable F) {p : ℝ}
    (hp : 0 < p) :
    eLpNorm F (ENNReal.ofReal p) (μ.prod ν) ^ p =
      ∫⁻ a, eLpNorm (fun b => F (a, b)) (ENNReal.ofReal p) ν ^ p ∂μ := by
  rw [qpc_pow_eLpNorm hF.aestronglyMeasurable hp, lintegral_prod _ (by fun_prop)]
  refine lintegral_congr fun a => ?_
  exact (qpc_pow_eLpNorm (f := fun b => F (a, b))
    (hF.comp measurable_prodMk_left).aestronglyMeasurable hp).symm

/-- A linear functional of a centred Gaussian vector with covariance bound `K`. -/
lemma qpc_lin {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {X : Ω' → ι → ℝ}
    (hX : HasGaussianLaw X P) (h0 : ∀ i, ∫ ω, X ω i ∂P = 0) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ a : ι → ℝ, ∫ ω, (∑ i, a i * X ω i) ^ 2 ∂P ≤ K * ∑ i, a i ^ 2)
    (w : ι → ℝ) (p : ℝ) :
    eLpNorm (fun x : ι → ℝ => ∑ i, w i * x i) (ENNReal.ofReal p) (P.map X) ≤
      ENNReal.ofReal (Real.sqrt K * Real.sqrt (∑ i, w i ^ 2)) * qpcG p := by
  have hint : ∀ i, Integrable (fun ω => X ω i) P := fun i => (hX.eval i).integrable
  have hmeas : Measurable (fun x : ι → ℝ => ∑ i, w i * x i) := by fun_prop
  rw [eLpNorm_map_measure hmeas.aestronglyMeasurable hX.aemeasurable]
  have hG : HasGaussianLaw (fun ω => ∑ i, w i * X ω i) P := by
    have := hX.map_fun (∑ i, w i • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))
    simpa using this
  have hz : ∫ ω, (∑ i, w i * X ω i) ∂P = 0 := by
    rw [integral_finset_sum _ (fun i _ => (hint i).const_mul _)]
    simp [integral_const_mul, h0]
  have hs : 0 ≤ Real.sqrt K * Real.sqrt (∑ i, w i ^ 2) := by positivity
  have hsq : (Real.sqrt K * Real.sqrt (∑ i, w i ^ 2)) ^ 2 = K * ∑ i, w i ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  exact qpc_scalar hG hz hs (by rw [hsq]; exact hK w) p

/-- Minkowski in `L^{p/2}`: the `L^p` norm of the Euclidean norm of a finite family. -/
lemma qpc_l2norm {α : Type*} [MeasurableSpace α] {μ : Measure α} (g : ι → α → ℝ)
    (hg : ∀ j, Measurable (g j)) {p : ℝ} (hp : 2 ≤ p) (B : ι → ℝ≥0∞)
    (hB : ∀ j, eLpNorm (g j) (ENNReal.ofReal p) μ ≤ B j) :
    eLpNorm (fun a => Real.sqrt (∑ j, g j a ^ 2)) (ENNReal.ofReal p) μ ^ (2 : ℝ) ≤
      ∑ j, B j ^ (2 : ℝ) := by
  have hs : Measurable (fun a => Real.sqrt (∑ j, g j a ^ 2)) := by fun_prop
  have h1 := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal (p / 2))
    (fun a => Real.sqrt (∑ j, g j a ^ 2)) hs.aestronglyMeasurable (q := 2) (by norm_num)
  have e2 : ENNReal.ofReal (p / 2) * ENNReal.ofReal 2 = ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_mul (by linarith)]; congr 1; ring
  rw [e2] at h1
  rw [← h1]
  have e3 : (fun a => ‖Real.sqrt (∑ j, g j a ^ 2)‖ ^ (2 : ℝ)) = fun a => ∑ j, ‖g j a‖ ^ (2 : ℝ) := by
    funext a
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt
      (Finset.sum_nonneg fun j _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  rw [e3]
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (p / 2) := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  calc eLpNorm (fun a => ∑ j, ‖g j a‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) μ
      = eLpNorm (∑ j, fun a => ‖g j a‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) μ := by
        congr 1; funext a; simp
    _ ≤ ∑ j, eLpNorm (fun a => ‖g j a‖ ^ (2 : ℝ)) (ENNReal.ofReal (p / 2)) μ :=
        eLpNorm_sum_le hp1
    _ ≤ ∑ j, B j ^ (2 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h2 := eLpNorm_norm_rpow (μ := μ) (p := ENNReal.ofReal (p / 2)) (g j)
          (hg j).aestronglyMeasurable (q := 2) (by norm_num)
        rw [e2] at h2
        rw [h2]
        exact ENNReal.rpow_le_rpow (hB j) (by norm_num)

/-- Decoupled Gaussian bilinear form: `‖uᵀAv‖_p ≤ K ‖A‖_HS G_p²` for independent centred Gaussian
vectors `u, v` with covariance operator bound `K`. -/
lemma qpc_decoupled {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P]
    {U V : Ω' → ι → ℝ} (hU : HasGaussianLaw U P) (hV : HasGaussianLaw V P)
    (hind : IndepFun U V P) (hU0 : ∀ i, ∫ ω, U ω i ∂P = 0) (hV0 : ∀ i, ∫ ω, V ω i ∂P = 0)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKU : ∀ a : ι → ℝ, ∫ ω, (∑ i, a i * U ω i) ^ 2 ∂P ≤ K * ∑ i, a i ^ 2)
    (hKV : ∀ a : ι → ℝ, ∫ ω, (∑ i, a i * V ω i) ^ 2 ∂P ≤ K * ∑ i, a i ^ 2)
    (A : ι → ι → ℝ) {p : ℝ} (hp : 2 ≤ p) :
    eLpNorm (fun ω => ∑ i, ∑ j, A i j * (U ω i * V ω j)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (K * Real.sqrt (∑ i, ∑ j, A i j ^ 2)) * qpcG p ^ 2 := by
  have hp0 : 0 < p := by linarith
  set G := qpcG p with hGdef
  set F : (ι → ℝ) × (ι → ℝ) → ℝ := fun z => ∑ i, ∑ j, A i j * (z.1 i * z.2 j) with hFdef
  have hFm : Measurable F := by fun_prop
  -- Step 1: pass to the product of the laws
  have hmap : P.map (fun ω => (U ω, V ω)) = (P.map U).prod (P.map V) :=
    (indepFun_iff_map_prod_eq_prod_map_map hU.aemeasurable hV.aemeasurable).1 hind
  have h1 : eLpNorm (fun ω => ∑ i, ∑ j, A i j * (U ω i * V ω j)) (ENNReal.ofReal p) P =
      eLpNorm F (ENNReal.ofReal p) ((P.map U).prod (P.map V)) := by
    rw [← hmap, eLpNorm_map_measure hFm.aestronglyMeasurable (hU.aemeasurable.prodMk hV.aemeasurable)]
    rfl
  rw [h1]
  -- Step 2: Fubini
  -- the coefficient vector
  let wA : (ι → ℝ) → ι → ℝ := fun a j => ∑ i, A i j * a i
  have hwm : ∀ j, Measurable (fun a : ι → ℝ => wA a j) := fun j => by simp only [wA]; fun_prop
  let s0 : (ι → ℝ) → ℝ := fun a => Real.sqrt (∑ j, wA a j ^ 2)
  have hs0m : Measurable s0 := by simp only [s0]; fun_prop
  -- Step 3: conditional bound
  have h3 : ∀ a : ι → ℝ, eLpNorm (fun b => F (a, b)) (ENNReal.ofReal p) (P.map V) ≤
      ENNReal.ofReal (Real.sqrt K) * ENNReal.ofReal (s0 a) * G := by
    intro a
    have e : (fun b : ι → ℝ => F (a, b)) = fun b => ∑ j, wA a j * b j := by
      funext b
      simp only [hFdef, wA]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e]
    have := qpc_lin hV hV0 hK0 hKV (wA a) p
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at this
    exact this
  -- Step 5: the `L^p` norm of `s0`
  set HS : ℝ := Real.sqrt (∑ i, ∑ j, A i j ^ 2) with hHS
  have hHSsq : HS ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
    rw [hHS, Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hHS0 : 0 ≤ HS := Real.sqrt_nonneg _
  have h5 : eLpNorm s0 (ENNReal.ofReal p) (P.map U) ≤
      ENNReal.ofReal (Real.sqrt K * HS) * G := by
    have hcol : ∀ j, eLpNorm (fun a : ι → ℝ => wA a j) (ENNReal.ofReal p) (P.map U) ≤
        ENNReal.ofReal (Real.sqrt K * Real.sqrt (∑ i, A i j ^ 2)) * G := fun j =>
      qpc_lin hU hU0 hK0 hKU (fun i => A i j) p
    have h6 := qpc_l2norm (μ := P.map U) (fun j a => wA a j) hwm hp
      (fun j => ENNReal.ofReal (Real.sqrt K * Real.sqrt (∑ i, A i j ^ 2)) * G) hcol
    have hreal : ∑ j, (Real.sqrt K * Real.sqrt (∑ i, A i j ^ 2)) ^ 2 = (Real.sqrt K * HS) ^ 2 := by
      have hc : ∀ j, 0 ≤ ∑ i, A i j ^ 2 := fun j => Finset.sum_nonneg fun i _ => sq_nonneg _
      simp only [mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt (hc _)]
      rw [← Finset.mul_sum, hHSsq, Finset.sum_comm]
    have hkey : ∑ j, ENNReal.ofReal (Real.sqrt K * Real.sqrt (∑ i, A i j ^ 2)) ^ 2 =
        ENNReal.ofReal (Real.sqrt K * HS) ^ 2 := by
      simp only [← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity), hreal,
        ← ENNReal.ofReal_pow (mul_nonneg (Real.sqrt_nonneg _) hHS0)]
    have hrhs : ∑ j, (ENNReal.ofReal (Real.sqrt K * Real.sqrt (∑ i, A i j ^ 2)) * G) ^ (2 : ℝ) =
        (ENNReal.ofReal (Real.sqrt K * HS) * G) ^ (2 : ℝ) := by
      simp only [ENNReal.rpow_two, mul_pow, ← Finset.sum_mul, hkey]
    exact (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).1 (h6.trans hrhs.le)
  -- Step 6: assemble
  have hmain : eLpNorm F (ENNReal.ofReal p) ((P.map U).prod (P.map V)) ^ p ≤
      (ENNReal.ofReal (K * HS) * G ^ 2) ^ p := by
    rw [qpc_prod_pow _ _ F hFm hp0]
    have hpt : ∀ a : ι → ℝ, eLpNorm (fun b => F (a, b)) (ENNReal.ofReal p) (P.map V) ^ p ≤
        (ENNReal.ofReal (Real.sqrt K) * G) ^ p * ‖s0 a‖ₑ ^ p := by
      intro a
      refine (ENNReal.rpow_le_rpow (h3 a) hp0.le).trans (le_of_eq ?_)
      rw [mul_right_comm, ENNReal.mul_rpow_of_nonneg _ _ hp0.le, Real.enorm_of_nonneg (Real.sqrt_nonneg _)]
    calc ∫⁻ a, eLpNorm (fun b => F (a, b)) (ENNReal.ofReal p) (P.map V) ^ p ∂(P.map U)
        ≤ ∫⁻ a, (ENNReal.ofReal (Real.sqrt K) * G) ^ p * ‖s0 a‖ₑ ^ p ∂(P.map U) :=
          lintegral_mono hpt
      _ = (ENNReal.ofReal (Real.sqrt K) * G) ^ p *
            eLpNorm s0 (ENNReal.ofReal p) (P.map U) ^ p := by
          have hGfin : G ≠ ∞ := (qpcG_lt_top p).ne
          rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0.le
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGfin)),
            qpc_pow_eLpNorm hs0m.aestronglyMeasurable hp0]
      _ ≤ (ENNReal.ofReal (Real.sqrt K) * G) ^ p * (ENNReal.ofReal (Real.sqrt K * HS) * G) ^ p := by
          gcongr
      _ = (ENNReal.ofReal (K * HS) * G ^ 2) ^ p := by
          rw [← ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
          congr 1
          have : ENNReal.ofReal (K * HS) = ENNReal.ofReal (Real.sqrt K) * ENNReal.ofReal (Real.sqrt K) *
              ENNReal.ofReal HS := by
            rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_mul (by positivity),
              Real.mul_self_sqrt hK0]
          rw [this, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
          ring
  exact (ENNReal.rpow_le_rpow_iff hp0).1 hmain

end HRS.MC.QRPChaos

end
