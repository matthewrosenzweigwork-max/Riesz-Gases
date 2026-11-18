import HRS.MS.Fp81S21WickB317
import HRS.MS.S21G2_K11bA

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

private theorem fp81s21_wickCrossPair_finite
    {d m : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (K : ℝ)
    (hL : ‖L‖ ≤ K)
    (hJoint : ∀ n (f : Fin n → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω i => L (f i) ω))
    (𝒢 : Submodule ℝ (Ω → ℝ))
    (h𝒢 : HRS.MC.QRSpec.Wick.QrpwG4 P 𝒢)
    (hLg : ∀ f : Lp ℝ 2 μ, (fun ω => L f ω) ∈ 𝒢)
    (X Y : Ω → ℝ) (hX : X ∈ 𝒢) (hY : Y ∈ 𝒢)
    (u v : Lp ℝ 2 μ)
    (hXcov : ∀ f : Lp ℝ 2 μ,
      (∫ ω, L f ω * X ω ∂P) = ∫ x, f x * u x ∂μ)
    (hYcov : ∀ f : Lp ℝ 2 μ,
      (∫ ω, L f ω * Y ω ∂P) = ∫ x, f x * v x ∂μ)
    (factors : Fin m → Euc d → ℝ)
    (hfactors : ∀ i, MemLp (factors i) 2 μ)
    (c : Fin m → Fin m → ℝ)
    (hk : MemLp (fp81s21_wickG_finite_rank_kernel factors c) 2 (μ.prod μ)) :
    (∫ ω, fp81s21_wickG_operator L K hL hJoint
      (hk.toLp (fp81s21_wickG_finite_rank_kernel factors c)) ω * X ω * Y ω ∂P) =
      (1 / 2 : ℝ) * ∫ z,
        fp81s21_wickG_finite_rank_kernel factors c z *
          (u z.1 * v z.2 + v z.1 * u z.2) ∂μ.prod μ := by
  classical
  let a : Fin m → Fin m → ℝ := fp81s21_wickB23_symmCoeff c
  let z : Fin m → Ω → ℝ := fun i ω => L ((hfactors i).toLp (factors i)) ω
  have ha : ∀ i j, a i j = a j i := by
    intro i j
    simp [a, fp81s21_wickB23_symmCoeff]
    ring
  have hz : ∀ i, z i ∈ 𝒢 := fun i => hLg ((hfactors i).toLp (factors i))
  have hbound := fp81s21_wickG_finite_rank_bound L K hL hJoint factors hfactors c
  have hW : MemLp (fp81s21_wickG_finite_rank_polynomial L factors hfactors c) 2 P := hbound.2.1
  have hAgree := fp81s21_wickB316_finite_rank_agreement L K hL hJoint factors hfactors c hk hW
  have hpolySym := fp81s21_wickB3_polynomial_symmCoeff L factors hfactors c
  have hWick := HRS.MS.R26T3.r26t3_finite_wick_pair P 𝒢 h𝒢 m z hz X Y hX hY a ha
  have hWick' : (∫ ω,
      fp81s21_wickG_finite_rank_polynomial L factors hfactors c ω * X ω * Y ω ∂P) =
      ∑ i, ∑ j, a i j *
        (∫ ω, z i ω * X ω ∂P) * (∫ ω, z j ω * Y ω ∂P) := by
    rw [← hpolySym]
    convert hWick using 1
  have hXY : MemLp (fun ω => X ω * Y ω) 2 P :=
    HRS.MC.QRSpec.Wick.qrpw_memLp2_mul (h𝒢 X hX).1 (h𝒢 Y hY).1
  have hleft :
      (∫ ω, fp81s21_wickG_operator L K hL hJoint
          (hk.toLp (fp81s21_wickG_finite_rank_kernel factors c)) ω *
          X ω * Y ω ∂P) =
        ∫ ω, fp81s21_wickG_finite_rank_polynomial L factors hfactors c ω *
          X ω * Y ω ∂P := by
    rw [show fp81s21_wickG_operator L K hL hJoint
        (hk.toLp (fp81s21_wickG_finite_rank_kernel factors c)) =
      hW.toLp (fp81s21_wickG_finite_rank_polynomial L factors hfactors c) from hAgree]
    apply integral_congr_ae
    filter_upwards [hW.coeFn_toLp] with ω hw
    rw [hw]
  have hcovX : ∀ i, (∫ ω, z i ω * X ω ∂P) = ∫ x, factors i x * u x ∂μ := by
    intro i
    calc
      _ = ∫ ω, L ((hfactors i).toLp (factors i)) ω * X ω ∂P := by rfl
      _ = ∫ x, ((hfactors i).toLp (factors i)) x * u x ∂μ :=
        hXcov ((hfactors i).toLp (factors i))
      _ = _ := integral_congr_ae <| by
        filter_upwards [(hfactors i).coeFn_toLp] with x hx
        rw [hx]
  have hcovY : ∀ i, (∫ ω, z i ω * Y ω ∂P) = ∫ x, factors i x * v x ∂μ := by
    intro i
    calc
      _ = ∫ ω, L ((hfactors i).toLp (factors i)) ω * Y ω ∂P := by rfl
      _ = ∫ x, ((hfactors i).toLp (factors i)) x * v x ∂μ :=
        hYcov ((hfactors i).toLp (factors i))
      _ = _ := integral_congr_ae <| by
        filter_upwards [(hfactors i).coeFn_toLp] with x hx
        rw [hx]
  let T : Euc d × Euc d → ℝ := fun z => u z.1 * v z.2 + v z.1 * u z.2
  have huLp : MemLp (fun x : Euc d => u x) 2 μ := Lp.memLp u
  have hvLp : MemLp (fun x : Euc d => v x) 2 μ := Lp.memLp v
  let A : Fin m → ℝ := fun i => ∫ x, factors i x * u x ∂μ
  let B : Fin m → ℝ := fun i => ∫ x, factors i x * v x ∂μ
  let C : Fin m → ℝ := fun i => ∫ x, factors i x * v x ∂μ
  let D : Fin m → ℝ := fun i => ∫ x, factors i x * u x ∂μ
  have hA : ∀ i, Integrable (fun x => factors i x * u x) μ :=
    fun i => (hfactors i).integrable_mul huLp
  have hB : ∀ i, Integrable (fun x => factors i x * v x) μ :=
    fun i => (hfactors i).integrable_mul hvLp
  have hCD : ∀ i j, Integrable
      (fun z : Euc d × Euc d =>
        (factors i z.1 * v z.1) * (factors j z.2 * u z.2)) (μ.prod μ) :=
    fun i j => (hB i).mul_prod (hA j)
  have hAB : ∀ i j, Integrable
      (fun z : Euc d × Euc d =>
        (factors i z.1 * u z.1) * (factors j z.2 * v z.2)) (μ.prod μ) :=
    fun i j => (hA i).mul_prod (hB j)
  have hTerm : ∀ i j, Integrable
      (fun z : Euc d × Euc d => c i j *
        ((factors i z.1 * u z.1) * (factors j z.2 * v z.2) +
          (factors i z.1 * v z.1) * (factors j z.2 * u z.2))) (μ.prod μ) := by
    intro i j
    exact ((hAB i j).add (hCD i j)).const_mul (c i j)
  have hTermInt : ∀ i j,
      (∫ z : Euc d × Euc d, c i j *
        ((factors i z.1 * u z.1) * (factors j z.2 * v z.2) +
          (factors i z.1 * v z.1) * (factors j z.2 * u z.2)) ∂(μ.prod μ)) =
        c i j * (A i * B j + C i * D j) := by
    intro i j
    have hdecomp : (fun z : Euc d × Euc d => c i j *
        ((factors i z.1 * u z.1) * (factors j z.2 * v z.2) +
          (factors i z.1 * v z.1) * (factors j z.2 * u z.2))) =
        (fun z => c i j * ((factors i z.1 * u z.1) * (factors j z.2 * v z.2)) +
          c i j * ((factors i z.1 * v z.1) * (factors j z.2 * u z.2))) := by
      funext z
      ring
    have hprod₁ :
        (∫ z : Euc d × Euc d,
          (factors i z.1 * u z.1) * (factors j z.2 * v z.2) ∂μ.prod μ) =
          A i * B j := by
      simpa only [A, B] using
        (integral_prod_mul (fun x : Euc d => factors i x * u x)
          (fun y : Euc d => factors j y * v y) (μ := μ) (ν := μ))
    have hprod₂ :
        (∫ z : Euc d × Euc d,
          (factors i z.1 * v z.1) * (factors j z.2 * u z.2) ∂μ.prod μ) =
          C i * D j := by
      simpa only [C, D] using
        (integral_prod_mul (fun x : Euc d => factors i x * v x)
          (fun y : Euc d => factors j y * u y) (μ := μ) (ν := μ))
    rw [hdecomp, integral_add ((hAB i j).const_mul (c i j))
      ((hCD i j).const_mul (c i j)), integral_const_mul, integral_const_mul,
      hprod₁, hprod₂]
    ring
  have hsum :
      (∫ z, fp81s21_wickG_finite_rank_kernel factors c z * T z ∂μ.prod μ) =
        ∑ i, ∑ j, c i j * (A i * B j + C i * D j) := by
    have hpoint : ∀ z : Euc d × Euc d,
        fp81s21_wickG_finite_rank_kernel factors c z * T z =
          ∑ i, ∑ j, c i j *
            ((factors i z.1 * u z.1) * (factors j z.2 * v z.2) +
              (factors i z.1 * v z.1) * (factors j z.2 * u z.2)) := by
      intro z
      simp [fp81s21_wickG_finite_rank_kernel, r2FiniteRankKernel, T,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hTerm i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_finsetSum _ (fun j _ => hTerm i j)]
    exact Finset.sum_congr rfl fun j _ => hTermInt i j
  have hswap :
      (∑ i, ∑ j, c i j * (C i * D j)) =
        ∑ i, ∑ j, c j i * (A i * B j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    dsimp [A, B, C, D]
    ring
  have hcoeff :
      (1 / 2 : ℝ) * (∑ i, ∑ j, c i j * (A i * B j + C i * D j)) =
        ∑ i, ∑ j, a i j * (A i * B j) := by
    have hsymmSum :
        (∑ i, ∑ j, ((c i j + c j i) / 2) * (A i * B j)) =
          (1 / 2 : ℝ) *
            ((∑ i, ∑ j, c i j * (A i * B j)) +
              (∑ i, ∑ j, c j i * (A i * B j))) := by
      rw [mul_add]
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    calc
      _ = (1 / 2 : ℝ) *
          ((∑ i, ∑ j, c i j * (A i * B j)) +
            (∑ i, ∑ j, c i j * (C i * D j))) := by
              congr 1
              simp_rw [mul_add, Finset.sum_add_distrib]
      _ = (1 / 2 : ℝ) *
          ((∑ i, ∑ j, c i j * (A i * B j)) +
            (∑ i, ∑ j, c j i * (A i * B j))) := by rw [hswap]
      _ = _ := by rw [← hsymmSum]; simp [a, fp81s21_wickB23_symmCoeff]
  rw [hsum]
  have hresult :
      (∑ i, ∑ j, a i j *
        (∫ x, factors i x * u x ∂μ) * (∫ x, factors j x * v x ∂μ)) =
        (1 / 2 : ℝ) * (∑ i, ∑ j, c i j * (A i * B j + C i * D j)) := by
    calc
      _ = ∑ i, ∑ j, a i j * (A i * B j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [A, B]
        ring
      _ = _ := hcoeff.symm
  rw [hleft, hWick']
  simp_rw [hcovX, hcovY]
  exact hresult

/-- The full Wick operator pairs against two variables through the symmetrized
product of their covariance representatives. -/
theorem fp81s21_wick_operator_mixed_pair
    {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (K : ℝ)
    (hL : ‖L‖ ≤ K)
    (hJoint : ∀ n (f : Fin n → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω i => L (f i) ω))
    (𝒢 : Submodule ℝ (Ω → ℝ))
    (h𝒢 : HRS.MC.QRSpec.Wick.QrpwG4 P 𝒢)
    (hLg : ∀ f : Lp ℝ 2 μ, (fun ω => L f ω) ∈ 𝒢)
    (X Y : Ω → ℝ) (hX : X ∈ 𝒢) (hY : Y ∈ 𝒢)
    (u v : Lp ℝ 2 μ)
    (hXcov : ∀ f : Lp ℝ 2 μ,
      (∫ ω, L f ω * X ω ∂P) = ∫ x, f x * u x ∂μ)
    (hYcov : ∀ f : Lp ℝ 2 μ,
      (∫ ω, L f ω * Y ω ∂P) = ∫ x, f x * v x ∂μ)
    (k : Lp ℝ 2 (μ.prod μ)) :
    Integrable (fun ω => fp81s21_wickG_operator L K hL hJoint k ω * X ω * Y ω) P ∧
    (∫ ω, fp81s21_wickG_operator L K hL hJoint k ω * X ω * Y ω ∂P) =
      (1 / 2 : ℝ) * ∫ z,
        k z * (u z.1 * v z.2 + v z.1 * u z.2) ∂μ.prod μ := by
  classical
  let hXY : MemLp (fun ω => X ω * Y ω) 2 P :=
    HRS.MC.QRSpec.Wick.qrpw_memLp2_mul (h𝒢 X hX).1 (h𝒢 Y hY).1
  let XY : Lp ℝ 2 P := hXY.toLp (fun ω => X ω * Y ω)
  let T : Euc d × Euc d → ℝ := fun z => u z.1 * v z.2 + v z.1 * u z.2
  have huLp : MemLp (fun x : Euc d => u x) 2 μ := Lp.memLp u
  have hvLp : MemLp (fun x : Euc d => v x) 2 μ := Lp.memLp v
  have hT1 := HRS.MS.R26T3.s21g2_k11b_tensor_memLp huLp hvLp
  have hT2 := HRS.MS.R26T3.s21g2_k11b_tensor_memLp hvLp huLp
  have hT : MemLp T 2 (μ.prod μ) := by
    dsimp [T]
    convert hT1.1.add hT2.1 using 1 <;> ext z <;> ring
  let TLp : Lp ℝ 2 (μ.prod μ) := hT.toLp T
  let F : Lp ℝ 2 (μ.prod μ) →L[ℝ] ℝ :=
    (innerSL ℝ XY).comp (fp81s21_wickG_operator L K hL hJoint)
  let G : Lp ℝ 2 (μ.prod μ) →L[ℝ] ℝ :=
    (1 / 2 : ℝ) • (innerSL ℝ TLp)
  let Sym := fp81s21_wickB32_symmetricSubmodule μ
  have hFsym : ∀ x, F x = F (fp81s21_wickB23_symmetrize μ x) := by
    intro x
    simp only [F, ContinuousLinearMap.comp_apply]
    rw [fp81s21_wickB311_operator_symmetrize]
  have hTLpswap : fp81s21_wickB23_swapLp μ TLp = TLp := by
    apply Lp.ext
    let hmp := Measure.measurePreserving_swap (μ := μ) (ν := μ)
    have hTcomp := hmp.quasiMeasurePreserving.ae_eq_comp hT.coeFn_toLp
    filter_upwards [fp81s21_wickB23_swapLp_ae μ TLp, hT.coeFn_toLp, hTcomp]
      with z hswap hTz hTzswap
    calc
      _ = TLp z.swap := hswap
      _ = T z.swap := by simpa only [Function.comp_apply] using hTzswap
      _ = T z := by
        change T z.swap = T z
        simp [T, Prod.swap, mul_comm]
        ring
      _ = TLp z := hTz.symm
  have hPairInt (q : Lp ℝ 2 (μ.prod μ)) :
      (∫ ω, fp81s21_wickG_operator L K hL hJoint q ω * X ω * Y ω ∂P) =
        inner ℝ XY (fp81s21_wickG_operator L K hL hJoint q) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hXY.coeFn_toLp] with ω hxy
    rw [hxy]
    rw [Real.inner_apply]
    ring
  have hTInner (q : Lp ℝ 2 (μ.prod μ)) :
      inner ℝ TLp q = ∫ z, q z * T z ∂μ.prod μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with z ht
    rw [ht]
    rw [Real.inner_apply]
    ring
  have hpairSwap (x : Lp ℝ 2 (μ.prod μ)) :
      inner ℝ TLp (fp81s21_wickB23_swapLp μ x) = inner ℝ TLp x := by
    calc
      _ = inner ℝ (fp81s21_wickB23_swapLp μ TLp)
          (fp81s21_wickB23_swapLp μ x) := by rw [hTLpswap]
      _ = _ := (fp81s21_wickB23_swapLp μ).inner_map_map TLp x
  have hGsym : ∀ x, G x = G (fp81s21_wickB23_symmetrize μ x) := by
    intro x
    change (1 / 2 : ℝ) * inner ℝ TLp x =
      (1 / 2 : ℝ) * inner ℝ TLp (fp81s21_wickB23_symmetrize μ x)
    rw [fp81s21_wickB23_symmetrize_apply, inner_smul_right, inner_add_right, hpairSwap]
    ring
  have hEq : ∀ y : Sym, F (y : Lp ℝ 2 (μ.prod μ)) = G (y : Lp ℝ 2 (μ.prod μ)) := by
    apply isClosed_property fp81s21_wickB310_dense
      (isClosed_eq
        (F.comp (Submodule.subtypeL Sym)).continuous
        (G.comp (Submodule.subtypeL Sym)).continuous)
    intro x
    change F (x : Lp ℝ 2 (μ.prod μ)) = G (x : Lp ℝ 2 (μ.prod μ))
    let r := fp81s21_wickB38_choose μ x
    rw [r.eq_class]
    change inner ℝ XY (fp81s21_wickG_operator L K hL hJoint
        (r.hk.toLp (fp81s21_wickG_finite_rank_kernel r.u r.c))) =
      (1 / 2 : ℝ) * inner ℝ TLp
        (r.hk.toLp (fp81s21_wickG_finite_rank_kernel r.u r.c))
    rw [← hPairInt, hTInner]
    calc
      _ = (1 / 2 : ℝ) * ∫ z,
          fp81s21_wickG_finite_rank_kernel r.u r.c z * T z ∂μ.prod μ :=
        fp81s21_wickCrossPair_finite μ P L K hL hJoint 𝒢 h𝒢 hLg X Y hX hY u v
          hXcov hYcov r.u r.hu r.c r.hk
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [r.hk.coeFn_toLp] with z hz
        rw [hz]
  have hSymm (x : Lp ℝ 2 (μ.prod μ)) :
      fp81s21_wickB23_symmetrize μ x ∈ Sym := by
    change fp81s21_wickB23_symmetrize μ (fp81s21_wickB23_symmetrize μ x) -
      fp81s21_wickB23_symmetrize μ x = 0
    rw [fp81s21_wickB23_symmetrize_idempotent, sub_self]
  have hWXY : Integrable
      (fun ω => fp81s21_wickG_operator L K hL hJoint k ω * (X ω * Y ω)) P :=
    (Lp.memLp (fp81s21_wickG_operator L K hL hJoint k)).integrable_mul hXY
  refine ⟨hWXY.congr (Filter.Eventually.of_forall fun ω => by ring), ?_⟩
  have hsymm := hEq ⟨fp81s21_wickB23_symmetrize μ k, hSymm k⟩
  calc
    _ = F k := hPairInt k
    _ = F (fp81s21_wickB23_symmetrize μ k) := hFsym k
    _ = G (fp81s21_wickB23_symmetrize μ k) := hsymm
    _ = G k := (hGsym k).symm
    _ = _ := by
      change (1 / 2 : ℝ) * inner ℝ TLp k = _
      rw [hTInner]

#print axioms fp81s21_wick_operator_mixed_pair

end HRS.Fp81.S21
end
