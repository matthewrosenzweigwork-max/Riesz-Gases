import HRS.MS.Fp81V01Insert
import HRS.MS.ProClosureS111PhysicalIntervals
import HRS.MS.ProClosureS111SourceContractions

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 64000

namespace HRS.Fp81.V01

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111T HRS.MC.E213T

variable {d r : ℕ}
variable {s a β γ T u c B Pw : ℝ}
variable {ρ : Euc d → ℝ}
variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : r26t6_WeightedChart d r Pw}

local notation "X" => R2X d T
local notation "P2" => projTensor X 2
local notation "P3" => projTensor X 3

private def fp81v01_evalP3 (M : X [×3]→L[ℝ] ℝ) : P3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ M).comp (projTensor X 3).subtypeL

private def fp81v01_pathObs (t : Set.Icc (0 : ℝ) T) (φ : Euc d → ℝ) :
    X →L[ℝ] ℝ := by
  let ev : X →L[ℝ] OscDual d (wholeSpaceIndex d : ℝ) := ContinuousMap.evalCLM ℝ t
  exact ((ContinuousLinearMap.apply ℝ ℝ
      (OscSpace.ofFun (wholeSpaceIndex d : ℝ) φ)).comp
    (OscDual.toDual (d := d) (m := (wholeSpaceIndex d : ℝ))).toContinuousLinearEquiv.toContinuousLinearMap).comp ev

private theorem fp81v01_pathObs_apply (t : Set.Icc (0 : ℝ) T) (φ : Euc d → ℝ)
    (hφ : MemOsc (wholeSpaceIndex d : ℝ) φ) (w : X) :
    fp81v01_pathObs t φ w = OscDual.eval (OscPath.at' w t) φ := by
  change (OscDual.toDual (OscPath.at' w t)) (OscSpace.ofFun (wholeSpaceIndex d : ℝ) φ) = _
  exact OscDual.toDual_ofFun (OscPath.at' w t) φ hφ

private def fp81v01_trilin (ell : Fin 3 → X →L[ℝ] ℝ) : X [×3]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ 3 ℝ).compContinuousLinearMap ell

private theorem fp81v01_trilin_apply (ell : Fin 3 → X →L[ℝ] ℝ) (x : Fin 3 → X) :
    fp81v01_trilin ell x = ell 0 (x 0) * ell 1 (x 1) * ell 2 (x 2) := by
  simp [fp81v01_trilin, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebraFin_apply, List.ofFn_succ, mul_assoc]

private def fp81v01_mk2 (l₁ l₂ : X →L[ℝ] ℝ) : X [×2]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l₁, l₂]

private theorem fp81v01_mk2_apply (l₁ l₂ : X →L[ℝ] ℝ) (x : Fin 2 → X) :
    fp81v01_mk2 l₁ l₂ x = l₁ (x 0) * l₂ (x 1) := by
  simp [fp81v01_mk2, Fin.prod_univ_two]

private theorem fp81v01_trilin_domDomCongr (ell : Fin 3 → X →L[ℝ] ℝ)
    (σ : Equiv.Perm (Fin 3)) :
    (fp81v01_trilin ell).domDomCongr σ = fp81v01_trilin (fun j => ell (σ.symm j)) := by
  ext x
  rw [ContinuousMultilinearMap.domDomCongr_apply]
  have hprod : ∀ L : Fin 3 → X →L[ℝ] ℝ, ∀ y : Fin 3 → X,
      fp81v01_trilin L y = ∏ i, L i (y i) := by
    intro L y
    rw [fp81v01_trilin_apply, Fin.prod_univ_three]
  rw [hprod, hprod]
  exact (Equiv.prod_comp σ (fun j => ell (σ.symm j) (x j))) ▸ by
    refine Finset.prod_congr rfl fun i _ => ?_
    simp

private theorem fp81v01_lastSlot_trilin (ell : Fin 3 → X →L[ℝ] ℝ) (g : X) :
    HRS.lastSlot (fp81v01_trilin ell) g =
      (ell 2 g) • fp81v01_mk2 (ell 0) (ell 1) := by
  ext x
  simp only [HRS.lastSlot, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousLinearMap.apply_apply, smul_apply, smul_eq_mul,
    fp81v01_mk2_apply, continuousMultilinearCurryRightEquiv_apply', fp81v01_trilin_apply]
  have h0 : (Fin.snoc x g : Fin 3 → X) 0 = x 0 := rfl
  have h1 : (Fin.snoc x g : Fin 3 → X) 1 = x 1 := rfl
  have h2 : (Fin.snoc x g : Fin 3 → X) 2 = g := rfl
  rw [h0, h1, h2]
  ring

private theorem fp81v01_PairInsert_product_eval (j : Fin 3) (Q : P2) (y : X)
    (ell : Fin 3 → X →L[ℝ] ℝ) :
    (((PairInsert j Q y : P3) : TensorDual X 3)
      (fp81v01_trilin ell)) =
      (Q : TensorDual X 2)
        (fp81v01_mk2 (ell j) (ell (j + 1))) * ell (j + 2) y := by
  let σ : Equiv.Perm (Fin 3) :=
    if j = 0 then Equiv.refl (Fin 3)
    else if j = 1 then Equiv.swap 0 1 * Equiv.swap 0 2
    else Equiv.swap 1 2 * Equiv.swap 0 2
  have hσ0 : σ.symm 0 = j := by
    fin_cases j <;> decide
  have hσ1 : σ.symm 1 = j + 1 := by
    fin_cases j <;> decide
  have hσ2 : σ.symm 2 = j + 2 := by
    fin_cases j <;> decide
  change (permTensor X σ (tensorCons (Q : TensorDual X 2) y))
      (fp81v01_trilin ell) = _
  rw [permTensor_apply, tensorCons_apply,
    fp81v01_trilin_domDomCongr,
    fp81v01_lastSlot_trilin]
  rw [hσ0, hσ1, hσ2, fp81v01_mk2]
  simp only [ContinuousLinearMap.map_smul, smul_eq_mul]
  ring

private theorem fp81v01_PairInsert_integral_eval (P : Measure Ω) (j : Fin 3)
    {Q : Ω → P2} {x : Ω → X}
    (hI : Integrable (fun w => PairInsert j (Q w) (x w)) P)
    (M : X [×3]→L[ℝ] ℝ) :
    (((∫ w, PairInsert j (Q w) (x w) ∂P : P3) : TensorDual X 3) M) =
      ∫ w, ((PairInsert j (Q w) (x w) : P3) : TensorDual X 3) M ∂P := by
  let L : P3 →L[ℝ] ℝ := fp81v01_evalP3 M
  change L (∫ w, PairInsert j (Q w) (x w) ∂P) = _
  exact (L.integral_comp_comm hI).symm

/-- The physical random sources have exactly the three evaluation fields
required by `PhysicalCubicSources`. The time contractions use product-time
integrability and retain the a.e. sample and a.e. time conclusions of their
certificates. -/
theorem physical_evaluations
    (P : Measure Ω) [IsProbabilityMeasure P]
    (O : r26t6_IntervalOperators E (r26t6_thermalCoeff d s a β ρ) T u c B)
    (qL qQ : ℝ × Ω → r26t6_Coeff) (Z : Ω → X)
    (RL RQ : ℝ → ℝ)
    (hL : HRS.MS.ProClosureS111.RandomIntervalControl P O qL RL)
    (hQ : HRS.MS.ProClosureS111.RandomIntervalControl P O qQ RQ)
    (hZ : MemLp Z 4 P)
    (hcontract : r26t6_SourceContractions P s a β γ ρ T u Z
      (fun t w f => inner ℝ (qQ (t, w)) (E.encode f))
      (fun t w f => inner ℝ (qL (t, w)) (E.encode f)))
    (I K : P3)
    (hI : r26t6_InitialCoordinates d s a β γ ρ T u I)
    (S : CubicSources d T u K)
    (hSI : S.initial = I)
    (hSD : S.drift = D P O qQ Z)
    (hSJ : S.covariance = J P O qL Z) :
    ∃ S' : PhysicalCubicSources d s a β γ ρ T u K,
      S'.toCubicSources = S := by
  let C : WholeCoeff d := r26t6_thermalCoeff d s a β ρ
  refine ⟨
    { toCubicSources := S
      initial_eval := ?_
      drift_eval := ?_
      covariance_eval := ?_ }, rfl⟩
  · intro tau phi hphi M hM
    rw [hSI]
    apply hI tau phi hphi M
    intro w
    simpa [r26t6_obs] using hM w
  · intro tau phi hphi chi hchi M hM Cfield v hv
    let ell : Fin 3 → X →L[ℝ] ℝ := fun i =>
      fp81v01_pathObs (tau i) (phi i)
    let b : ℝ → Ω → (Euc d → ℝ) → ℝ :=
      fun t w f => inner ℝ (qQ (t, w)) (E.encode f)
    have hell (i : Fin 3) (x : X) :
        ell i x = OscDual.eval (OscPath.at' x (tau i)) (phi i) := by
      exact fp81v01_pathObs_apply (tau i) (phi i) (hphi i).2 x
    have hMell : ∀ z : Fin 3 → X, M z = ∏ i, ell i (z i) := by
      intro z
      rw [hM z]
      rw [Fin.prod_univ_three]
      rw [← hell 0 (z 0), ← hell 1 (z 1), ← hell 2 (z 2)]
      rw [Fin.prod_univ_three]
    have hMtr : M = fp81v01_trilin ell := by
      ext w
      rw [hMell w, fp81v01_trilin_apply, Fin.prod_univ_three]
    have hD_eval :
        (((D P O qQ Z v : P3) : TensorDual X 3) M) =
          ∑ i : Fin 3,
            ∫ w, ((Insert i (r26t6_randomDrift O qQ v w) (Z w) (Z w) : P3) :
              TensorDual X 3) M ∂P := by
      let L : P3 →L[ℝ] ℝ := fp81v01_evalP3 M
      change L (∑ i : Fin 3,
        ∫ w, Insert i (r26t6_randomDrift O qQ v w) (Z w) (Z w) ∂P) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact Insert_integral_eval P i
        (Insert_integrable P (hQ.moments v hv).1 hZ hZ i) M
    have hpiece : ∀ i : Fin 3,
        (∫ w, ((Insert i (r26t6_randomDrift O qQ v w) (Z w) (Z w) : P3) :
          TensorDual X 3) M ∂P) =
        -(∫ r in Set.Icc (0 : ℝ) (min v (u + tau i)),
          ∫ x, ∫ y, commutatorKernel d s
            (gradient (propagatorW C r (u + tau i) (phi i))) x y *
              chi (i + 1) r x * chi (i + 2) r y) := by
      intro i
      let U : Set ℝ := Set.Icc (0 : ℝ) (u + tau i)
      let V : Set ℝ := Set.Icc (0 : ℝ) (min v (u + tau i))
      let F : ℝ × Ω → ℝ := fun p =>
        b p.1 p.2 (propagatorW C p.1 (u + tau i) (phi i)) *
          r26t6_obs (Z p.2) (tau (i + 1)) (phi (i + 1)) *
          r26t6_obs (Z p.2) (tau (i + 2)) (phi (i + 2))
      have hsub : V ⊆ U := by
        intro r hr
        exact ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
      have hle : volume.restrict V ≤ volume.restrict U :=
        Measure.restrict_mono hsub le_rfl
      have hc := hcontract.drift tau phi hphi chi hchi i
      have hF : Integrable F ((volume.restrict U).prod P) := by
        simpa [F, U, b, C, r26t6_thermalCoeff, r26t6_obs] using hc.1
      have hFshort : Integrable F ((volume.restrict V).prod P) :=
        hF.mono_measure (Measure.prod_mono hle le_rfl)
      have hEq : ∀ᵐ r ∂volume.restrict U,
          (∫ w, F (r, w) ∂P) =
            -∫ x, ∫ y, commutatorKernel d s
              (gradient (propagatorW C r (u + tau i) (phi i))) x y *
                chi (i + 1) r x * chi (i + 2) r y := by
        simpa [F, U, b, C, r26t6_thermalCoeff, r26t6_obs] using hc.2
      have hEqshort := hEq.filter_mono (ae_mono hle)
      have hcoord : ∀ᵐ w ∂P,
          ell i (r26t6_randomDrift O qQ v w) =
            ∫ r in V, b r w (propagatorW C r (u + tau i) (phi i)) := by
        filter_upwards [hQ.coordinates] with w hw
        have h := ((hw v hv).1 (tau i) (phi i) (hphi i)).2
        rw [← hell i (r26t6_randomDrift O qQ v w)] at h
        simpa [V, b, C, r26t6_thermalCoeff, r26t6_coefficientField] using h
      have hsample :
          (fun w => ((Insert i (r26t6_randomDrift O qQ v w) (Z w) (Z w) : P3) :
            TensorDual X 3) M) =ᵐ[P] fun w => ∫ r in V, F (r, w) := by
        filter_upwards [hcoord] with w hw
        rw [Insert_product_eval i _ _ _ ell M hMell]
        rw [hw]
        dsimp [F, U, V, b]
        calc
          (∫ r in Set.Icc (0 : ℝ) (min v (u + tau i)),
              inner ℝ (qQ (r, w))
                (E.encode (propagatorW C r (u + tau i) (phi i)))) *
              ell (i + 1) (Z w) * ell (i + 2) (Z w)
              = ∫ r in Set.Icc (0 : ℝ) (min v (u + tau i)),
                  inner ℝ (qQ (r, w))
                    (E.encode (propagatorW C r (u + tau i) (phi i))) *
                    (ell (i + 1) (Z w) * ell (i + 2) (Z w)) := by
                  calc
                    _ = (∫ r in Set.Icc (0 : ℝ) (min v (u + tau i)),
                          inner ℝ (qQ (r, w))
                            (E.encode (propagatorW C r (u + tau i) (phi i)))) *
                          (ell (i + 1) (Z w) * ell (i + 2) (Z w)) := by ring
                    _ = _ := by rw [← integral_mul_const]
          _ = ∫ r in Set.Icc (0 : ℝ) (min v (u + tau i)), F (r, w) := by
                apply integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
                dsimp [F, b]
                rw [hell (i + 1) (Z w), hell (i + 2) (Z w)]
                simp only [r26t6_obs]
                ring
      calc
        (∫ w, ((Insert i (r26t6_randomDrift O qQ v w) (Z w) (Z w) : P3) :
            TensorDual X 3) M ∂P)
            = ∫ w, ∫ r in V, F (r, w) ∂volume ∂P := integral_congr_ae hsample
        _ = ∫ r in V, ∫ w, F (r, w) ∂P ∂volume :=
              (integral_integral_swap (f := fun r w => F (r, w)) hFshort).symm
        _ = -(∫ r in V, ∫ x, ∫ y, commutatorKernel d s
              (gradient (propagatorW C r (u + tau i) (phi i))) x y *
                chi (i + 1) r x * chi (i + 2) r y) := by
              rw [integral_congr_ae hEqshort, integral_neg]
    rw [hSD, hD_eval]
    calc
      (∑ i : Fin 3,
          ∫ w, ((Insert i (r26t6_randomDrift O qQ v w) (Z w) (Z w) : P3) :
            TensorDual X 3) M ∂P) =
        ∑ i : Fin 3,
          -(∫ r in Set.Icc (0 : ℝ) (min v (u + tau i)),
            ∫ x, ∫ y, commutatorKernel d s
              (gradient (propagatorW C r (u + tau i) (phi i))) x y *
                chi (i + 1) r x * chi (i + 2) r y) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpiece i
      _ = -∑ i : Fin 3,
          ∫ r in Set.Icc (0 : ℝ) (min v (u + tau i)),
            ∫ x, ∫ y, commutatorKernel d s
              (gradient (propagatorW C r (u + tau i) (phi i))) x y *
                chi (i + 1) r x * chi (i + 2) r y := by
          rw [Finset.sum_neg_distrib]
  · intro tau phi hphi chi hchi M hM Cfield v hv
    let ell : Fin 3 → X →L[ℝ] ℝ := fun i =>
      fp81v01_pathObs (tau i) (phi i)
    let z : ℝ → Ω → (Euc d → ℝ) → ℝ :=
      fun t w f => inner ℝ (qL (t, w)) (E.encode f)
    have hell (i : Fin 3) (x : X) :
        ell i x = OscDual.eval (OscPath.at' x (tau i)) (phi i) := by
      exact fp81v01_pathObs_apply (tau i) (phi i) (hphi i).2 x
    have hMell : ∀ z : Fin 3 → X, M z = ∏ i, ell i (z i) := by
      intro z
      rw [hM z]
      rw [Fin.prod_univ_three]
      rw [← hell 0 (z 0), ← hell 1 (z 1), ← hell 2 (z 2)]
      rw [Fin.prod_univ_three]
    have hMtr : M = fp81v01_trilin ell := by
      ext w
      rw [hMell w, fp81v01_trilin_apply, Fin.prod_univ_three]
    let M2 (i : Fin 3) := fp81v01_mk2 (ell i) (ell (i + 1))
    have hJ_eval :
        (((J P O qL Z v : P3) : TensorDual X 3) M) =
          ∑ i : Fin 3,
            ∫ w, ((PairInsert i (r26t6_randomCovariance O qL v w) (Z w) : P3) :
              TensorDual X 3) M ∂P := by
      let L : P3 →L[ℝ] ℝ := fp81v01_evalP3 M
      change L (∑ i : Fin 3,
        ∫ w, PairInsert i (r26t6_randomCovariance O qL v w) (Z w) ∂P) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simpa [L, fp81v01_evalP3] using
        fp81v01_PairInsert_integral_eval P i
          (PairInsert_integrable P (hL.moments v hv).2
            (hZ.mono_exponent (by norm_num)) i) M
    have hpiece : ∀ i : Fin 3,
        (∫ w, ((PairInsert i (r26t6_randomCovariance O qL v w) (Z w) : P3) :
          TensorDual X 3) M ∂P) =
        (2 / β) * ∫ r in Set.Icc (0 : ℝ)
        (min v (min (u + tau i) (u + tau (i + 1)))),
          ∫ x, inner ℝ
            (gradient (propagatorW C r (u + tau i) (phi i)) x)
            (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x) *
              chi (i + 2) r x := by
      intro i
      let U : Set ℝ := Set.Icc (0 : ℝ) (min (u + tau i) (u + tau (i + 1)))
      let V : Set ℝ := Set.Icc (0 : ℝ) (min v (min (u + tau i) (u + tau (i + 1))))
      let F : ℝ × Ω → ℝ := fun p =>
        z p.1 p.2 (fun x => inner ℝ
          (gradient (propagatorW C p.1 (u + tau i) (phi i)) x)
          (gradient (propagatorW C p.1 (u + tau (i + 1)) (phi (i + 1))) x)) *
          r26t6_obs (Z p.2) (tau (i + 2)) (phi (i + 2))
      have hsub : V ⊆ U := by
        intro r hr
        exact ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
      have hle : volume.restrict V ≤ volume.restrict U :=
        Measure.restrict_mono hsub le_rfl
      have hc := hcontract.covariance tau phi hphi chi hchi i
      have hF : Integrable F ((volume.restrict U).prod P) := by
        simpa [F, U, z, C, r26t6_thermalCoeff, r26t6_obs] using hc.1
      have hFshort : Integrable F ((volume.restrict V).prod P) :=
        hF.mono_measure (Measure.prod_mono hle le_rfl)
      have hEq : ∀ᵐ r ∂volume.restrict U,
          (∫ w, F (r, w) ∂P) =
            ∫ x, inner ℝ
              (gradient (propagatorW C r (u + tau i) (phi i)) x)
              (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x) *
                chi (i + 2) r x := by
        simpa [F, U, z, C, r26t6_thermalCoeff, r26t6_obs] using hc.2
      have hEqshort := hEq.filter_mono (ae_mono hle)
      have hcoord : ∀ᵐ w ∂P,
          ((r26t6_randomCovariance O qL v w : P2) : TensorDual X 2) (M2 i) =
            (2 * C.ν) * ∫ r in V,
              z r w (fun x => inner ℝ
                (gradient (propagatorW C r (u + tau i) (phi i)) x)
                (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x)) := by
        filter_upwards [hL.coordinates] with w hw
        have h := ((hw v hv).2) (tau i) (tau (i + 1))
          (phi i) (phi (i + 1)) (hphi i) (hphi (i + 1))
        have hshift := h.2 (ell i) (ell (i + 1))
          (fun x => hell i x) (fun x => hell (i + 1) x)
        simpa [V, M2, z, C, r26t6_coefficientField, fp81v01_mk2] using hshift
      have hsample :
          (fun w => ((PairInsert i (r26t6_randomCovariance O qL v w) (Z w) : P3) :
            TensorDual X 3) M) =ᵐ[P] fun w => (2 * C.ν) * ∫ r in V, F (r, w) := by
        filter_upwards [hcoord] with w hw
        rw [hMtr, fp81v01_PairInsert_product_eval]
        rw [hw]
        dsimp [F, V, z]
        calc
          ((2 * C.ν) * ∫ r in V,
              inner ℝ (qL (r, w)) (E.encode (fun x => inner ℝ
                (gradient (propagatorW C r (u + tau i) (phi i)) x)
                (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x)))) *
              ell (i + 2) (Z w) =
            (2 * C.ν) * ((∫ r in V,
              inner ℝ (qL (r, w)) (E.encode (fun x => inner ℝ
                (gradient (propagatorW C r (u + tau i) (phi i)) x)
                (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x)))) *
              ell (i + 2) (Z w)) := by ring
          _ = (2 * C.ν) * ∫ r in V,
                inner ℝ (qL (r, w)) (E.encode (fun x => inner ℝ
                  (gradient (propagatorW C r (u + tau i) (phi i)) x)
                  (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x))) *
                  ell (i + 2) (Z w) := by rw [← integral_mul_const]
          _ = (2 * C.ν) * ∫ r in V, F (r, w) := by
                congr 2
                funext r
                dsimp [F, z]
                rw [hell (i + 2) (Z w)]
                rfl
      calc
        (∫ w, ((PairInsert i (r26t6_randomCovariance O qL v w) (Z w) : P3) :
            TensorDual X 3) M ∂P) =
          ∫ w, (2 * C.ν) * ∫ r in V, F (r, w) ∂volume ∂P := integral_congr_ae hsample
        _ = (2 * C.ν) * ∫ w, ∫ r in V, F (r, w) ∂volume ∂P := by
              rw [integral_const_mul]
        _ = (2 * C.ν) * ∫ r in V, ∫ w, F (r, w) ∂P ∂volume := by
              rw [(integral_integral_swap (f := fun r w => F (r, w)) hFshort).symm]
        _ = (2 * C.ν) * ∫ r in V, ∫ x, inner ℝ
              (gradient (propagatorW C r (u + tau i) (phi i)) x)
              (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x) *
                chi (i + 2) r x := by
              rw [integral_congr_ae hEqshort]
        _ = (2 / β) * ∫ r in V, ∫ x, inner ℝ
              (gradient (propagatorW C r (u + tau i) (phi i)) x)
              (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x) *
                chi (i + 2) r x := by
              have hfac : (2 * C.ν) = (2 / β) := by
                simpa [C, r26t6_thermalCoeff, quadraticGradientDyn, WholeDyn.coeff,
                  div_eq_mul_inv]
              rw [hfac]
    rw [hSJ, hJ_eval]
    calc
      (∑ i : Fin 3,
          ∫ w, ((PairInsert i (r26t6_randomCovariance O qL v w) (Z w) : P3) :
            TensorDual X 3) M ∂P) =
        ∑ i : Fin 3, (2 / β) * ∫ r in Set.Icc (0 : ℝ)
        (min v (min (u + tau i) (u + tau (i + 1)))),
          ∫ x, inner ℝ
            (gradient (propagatorW C r (u + tau i) (phi i)) x)
            (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x) *
              chi (i + 2) r x := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hpiece i
      _ = (2 / β) * ∑ i : Fin 3,
          ∫ r in Set.Icc (0 : ℝ) (min v (min (u + tau i) (u + tau (i + 1)))),
            ∫ x, inner ℝ
              (gradient (propagatorW C r (u + tau i) (phi i)) x)
              (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x) *
                chi (i + 2) r x := by
          rw [Finset.mul_sum]

/- Axiom audit for this module's exported theorem. -/
#print axioms physical_evaluations

end HRS.Fp81.V01
end
