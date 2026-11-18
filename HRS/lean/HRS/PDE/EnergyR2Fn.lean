import HRS.PDE.Toolbox
import HRS.PDE.EnergyR3

/-!
# Function-level bookkeeping for the regime-R2 estimates

Lipschitz constants and `C^{1,1}` bounds on the torus from `cbNorm` bounds, and trigonometric
polynomials as smooth functions.  All lemmas are in the namespace `HRS.PDE.R2Aux`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

/-- `mk` of the centred representative is the point itself. -/
theorem mk_centeredRep (z : Torus d) : Torus.mk (Torus.centeredRep z) = z := by
  have h := Torus.mk_rep z
  funext i
  have hi : ((Torus.rep z i : ℝ) : UnitAddCircle) = z i := congrFun h i
  show (((Torus.centeredRep z) i : ℝ) : UnitAddCircle) = z i
  simp only [Torus.centeredRep]
  by_cases hc : Torus.rep z i ≤ 1 / 2
  · simp only [hc, ite_true]; exact hi
  · simp only [hc, ite_false]
    rw [AddCircle.coe_sub, hi]
    have : (((1 : ℝ) : UnitAddCircle)) = 0 := AddCircle.coe_period 1
    rw [this, sub_zero]

theorem mk_sub (u v : Euc d) : Torus.mk (u - v) = Torus.mk u - Torus.mk v := by
  funext i
  show (((u - v) i : ℝ) : UnitAddCircle) = _
  simp [Torus.mk]

/-- A Lipschitz function of the lift is `IsLipschitz` for `tdist`. -/
theorem isLipschitz_of_lipschitzWith {a : Torus d → ℝ} {K : ℝ≥0}
    (ha : LipschitzWith K (Torus.lift a)) : Torus.IsLipschitz (K : ℝ) a := by
  intro x y
  set c := Torus.centeredRep (x - y) with hc
  have h1 : Torus.mk (Torus.rep x - c) = y := by
    rw [mk_sub, Torus.mk_rep, hc, mk_centeredRep]; abel
  have h2 := ha.dist_le_mul (Torus.rep x) (Torus.rep x - c)
  have e1 : Torus.lift a (Torus.rep x) = a x := by simp [Torus.lift, Torus.mk_rep]
  have e2 : Torus.lift a (Torus.rep x - c) = a y := by simp [Torus.lift, h1]
  rw [e1, e2, Real.dist_eq, dist_eq_norm] at h2
  have e3 : Torus.rep x - (Torus.rep x - c) = c := by abel
  rw [e3] at h2
  exact h2

/-- Differentiable lift with bounded derivative: Lipschitz. -/
theorem lipschitzWith_lift_of_bound {φ : Torus d → ℝ} (hφ : Differentiable ℝ (Torus.lift φ))
    (L : ℝ) (h : ∀ y, ‖fderiv ℝ (Torus.lift φ) y‖ ≤ L) :
    LipschitzWith (Real.toNNReal L) (Torus.lift φ) := by
  refine lipschitzWith_of_nnnorm_fderiv_le hφ fun y => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  exact (h y).trans (le_max_left _ _)

theorem norm_fderiv_le_cbNorm {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) (y : Euc d) :
    ‖fderiv ℝ (Torus.lift φ) y‖ ≤ Torus.cbNorm 1 φ := by
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ 1 (Torus.lift φ) x‖) :=
    Torus.bddAbove_norm_iteratedFDeriv_lift 1 φ (by exact_mod_cast hφ)
  have h1 : ‖fderiv ℝ (Torus.lift φ) y‖ ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift φ) x‖ := by
    rw [← norm_iteratedFDeriv_one]
    exact le_ciSup hbdd y
  refine h1.trans ?_
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num))

theorem cbNorm_nonneg' (k : ℕ) (φ : Torus d → ℝ) : 0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

theorem differentiable_lift_of_isCk {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) :
    Differentiable ℝ (Torus.lift φ) :=
  (show ContDiff ℝ 1 (Torus.lift φ) from hφ).differentiable one_ne_zero

/-- `C¹` with `cbNorm 1 ≤ B` implies Lipschitz with constant `B`. -/
theorem isLipschitz_of_cbNorm {φ : Torus d → ℝ} (hφ : Torus.IsCk 1 φ) :
    Torus.IsLipschitz (Torus.cbNorm 1 φ) φ := by
  have h := lipschitzWith_lift_of_bound (differentiable_lift_of_isCk hφ) _
    (norm_fderiv_le_cbNorm hφ)
  have := isLipschitz_of_lipschitzWith h
  rwa [Real.coe_toNNReal _ (cbNorm_nonneg' 1 φ)] at this

theorem abs_le_cbNorm {φ : Torus d → ℝ} {k : ℕ} (hφ : Torus.IsCk k φ) (x : Torus d) :
    |φ x| ≤ Torus.cbNorm k φ := by
  have hcont : Continuous φ := continuous_of_lift' hφ.continuous
  have h1 := norm_le_supNorm hcont x
  have h2 := supNorm_le_cbNorm k hφ
  rw [Real.norm_eq_abs] at h1
  linarith


/-- Evaluation at `e_j` as a continuous linear map on `(ℝ^d)*`. -/
def evalSingle (d : ℕ) (j : Fin d) : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ))

theorem norm_evalSingle_le (j : Fin d) : ‖evalSingle d j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  have := f.le_opNorm (EuclideanSpace.single j (1 : ℝ))
  simpa [evalSingle, PiLp.norm_single] using this

/-- Regularity and size of a partial derivative: `‖∂_jφ‖_{C^k} ≤ ‖φ‖_{C^{k+1}}`. -/
theorem partialDeriv_cbNorm (k : ℕ) (j : Fin d) (φ : Torus d → ℝ)
    (hφ : Torus.IsCk ((k + 1 : ℕ) : WithTop ℕ∞) φ) :
    Torus.IsCk (k : WithTop ℕ∞) (Torus.partialDeriv j φ) ∧
      Torus.cbNorm k (Torus.partialDeriv j φ) ≤ Torus.cbNorm (k + 1) φ := by
  have hφ' : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Torus.lift φ) := hφ
  have h1 : Torus.IsCk 1 φ := hφ.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k))
  have hlift : Torus.lift (Torus.partialDeriv j φ) =
      fun y => evalSingle d j (fderiv ℝ (Torus.lift φ) y) := by
    rw [lift_partialDeriv j φ h1]; rfl
  refine ⟨?_, ?_⟩
  · unfold Torus.IsCk
    rw [hlift]
    exact (evalSingle d j).contDiff.comp (hφ'.fderiv_right (by exact_mod_cast le_rfl))
  · unfold Torus.cbNorm
    rw [Finset.sum_range_succ' _ (k + 1)]
    have hnn : 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift φ) x‖ :=
      Real.iSup_nonneg fun _ => norm_nonneg _
    refine le_add_of_le_of_nonneg (Finset.sum_le_sum fun i hi => ?_) hnn
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hb := Torus.bddAbove_norm_iteratedFDeriv_lift (i + 1) φ
      (hφ'.of_le (by exact_mod_cast Nat.succ_le_succ hik))
    refine ciSup_le fun x => ?_
    rw [hlift]
    have hfd : ContDiff ℝ (i : WithTop ℕ∞) (fderiv ℝ (Torus.lift φ)) :=
      hφ'.fderiv_right (by exact_mod_cast Nat.succ_le_succ hik)
    have e : (fun y => evalSingle d j (fderiv ℝ (Torus.lift φ) y)) =
        (evalSingle d j) ∘ (fderiv ℝ (Torus.lift φ)) := rfl
    rw [e]
    calc _ ≤ ‖evalSingle d j‖ * ‖iteratedFDeriv ℝ i (fderiv ℝ (Torus.lift φ)) x‖ :=
          (evalSingle d j).norm_iteratedFDeriv_comp_left hfd.contDiffAt le_rfl
      _ ≤ 1 * ‖iteratedFDeriv ℝ (i + 1) (Torus.lift φ) x‖ := by
          rw [norm_iteratedFDeriv_fderiv]
          exact mul_le_mul_of_nonneg_right (norm_evalSingle_le j) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact le_ciSup hb x


/-- `C²` with `cbNorm 2 ≤ B` gives `C^{1,1}` with constant `B`. -/
theorem isC11_of_cbNorm {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    IsC11 (Torus.cbNorm 2 φ) φ := by
  have hφ' : ContDiff ℝ 2 (Torus.lift φ) := hφ
  refine ⟨hφ.of_le (by norm_num), ?_⟩
  have hfd : ContDiff ℝ 1 (fderiv ℝ (Torus.lift φ)) := hφ'.fderiv_right (by norm_num)
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ 2 (Torus.lift φ) x‖) :=
    Torus.bddAbove_norm_iteratedFDeriv_lift 2 φ hφ'
  refine lipschitzWith_of_nnnorm_fderiv_le (hfd.differentiable one_ne_zero) fun y => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
  refine le_trans ?_ (le_max_left _ _)
  have h1 : ‖fderiv ℝ (fderiv ℝ (Torus.lift φ)) y‖ ≤
      ⨆ x : Euc d, ‖iteratedFDeriv ℝ 2 (Torus.lift φ) x‖ := by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact le_ciSup hbdd y
  refine h1.trans ?_
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num))

/-- Lipschitz bound for a partial derivative of a `C²` function. -/
theorem isLipschitz_partialDeriv {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) (j : Fin d) :
    Torus.IsLipschitz (Torus.cbNorm 2 φ) (Torus.partialDeriv j φ) := by
  obtain ⟨h1, h2⟩ := partialDeriv_cbNorm 1 j φ (by simpa using hφ)
  have h1' : Torus.IsCk 1 (Torus.partialDeriv j φ) := by simpa using h1
  have := isLipschitz_of_cbNorm h1'
  intro x y
  refine (this x y).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa using h2

theorem c01Norm_le {a : Torus d → ℝ} {L A : ℝ} (hL : Torus.IsLipschitz L a)
    (hA : ∀ x, |a x| ≤ A) : Torus.c01Norm a ≤ A + |L| * Real.sqrt d := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have h1 : Torus.supNorm a ≤ A := by
    refine Real.iSup_le (fun x => ?_) hA0
    simpa using hA x
  have h2 : Torus.holderSeminorm 1 a ≤ |L| * Real.sqrt d := by
    refine Real.iSup_le (fun p => ?_) (by positivity)
    have hp : 0 < ‖p.1.1 - p.1.2‖ := norm_pos_iff.2 (sub_ne_zero.2 p.2)
    rw [Real.rpow_one, div_le_iff₀ hp]
    calc |a p.1.1 - a p.1.2| ≤ L * Torus.tdist p.1.1 p.1.2 := hL _ _
      _ ≤ |L| * Torus.tdist p.1.1 p.1.2 :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
      _ ≤ |L| * (Real.sqrt d * ‖p.1.1 - p.1.2‖) :=
          mul_le_mul_of_nonneg_left (ProdAux.tdist_le _ _) (abs_nonneg _)
      _ = _ := by ring
  unfold Torus.c01Norm
  linarith


/-! ### Trigonometric polynomials as smooth functions -/

theorem isRealCoeff_multiDerivCoeff {F : Coeff d} (hF : IsRealCoeff F) (α : Fin d → ℕ) :
    IsRealCoeff (multiDerivCoeff α F) := by
  intro k
  rw [multiDerivCoeff_apply, multiDerivCoeff_apply, map_mul, hF k, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]
  congr 1
  have : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I * (((-k) i : ℤ) : ℂ) := by
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat,
      Pi.neg_apply, Int.cast_neg]
    ring
  rw [← this]

theorem summable_norm_of_trig {n : ℕ} {c : Coeff d} (hc : IsTrigPoly n c) :
    Summable fun k => ‖c k‖ :=
  summable_of_ne_finset_zero (s := boxFin d n) fun k hk => by
    rw [eq_zero_of_isTrigPoly hc hk]; simp

theorem coeffOf_toFun_trig {n : ℕ} {c : Coeff d} (hr : IsRealCoeff c) (hc : IsTrigPoly n c) :
    coeffOf (toFun c) = c :=
  coeffOf_toFun c hr (summable_norm_of_trig hc)

theorem isCk_toFun_trig {n : ℕ} {c : Coeff d} (hr : IsRealCoeff c) (hc : IsTrigPoly n c)
    (j : ℕ) : Torus.IsCk (j : WithTop ℕ∞) (toFun c) := by
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) j ((d : ℝ) / 2 + j + 1) (by linarith)
  exact (hC c (memHs_of_isTrigPolyE hc _) hr).1

theorem continuous_toFun_trig {n : ℕ} {c : Coeff d} (hr : IsRealCoeff c) (hc : IsTrigPoly n c) :
    Continuous (toFun c) :=
  continuous_of_lift' (isCk_toFun_trig hr hc 0).continuous

theorem memLp_of_continuous_real {g : Torus d → ℝ} (hg : Continuous g) : MemLp g 2 volume :=
  hg.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem memSobolev_toFun_trig {n : ℕ} {c : Coeff d} (hr : IsRealCoeff c) (hc : IsTrigPoly n c)
    (σ : ℝ) : MemSobolev σ (toFun c) := by
  refine memSobolev_of_memHs σ _ (memLp_of_continuous_real (continuous_toFun_trig hr hc)) ?_
  rw [coeffOf_toFun_trig hr hc]
  exact memHs_of_isTrigPolyE hc σ

theorem l2NormSq_eq_hsNormSq {g : Torus d → ℝ} (hg : Continuous g) :
    l2NormSq g = hsNormSq 0 (coeffOf g) := by
  have hm : MemLp (fun x => (g x : ℂ)) 2 volume :=
    memLp_two_of_continuous (Complex.continuous_ofReal.comp hg)
  obtain ⟨-, h2⟩ := hsNormSq_zero_coeffOfC _ hm
  have : coeffOfC (fun x => (g x : ℂ)) = coeffOf g := rfl
  rw [this] at h2
  rw [h2]
  unfold l2NormSq
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [Complex.norm_real]

end HRS.PDE.R2Aux
