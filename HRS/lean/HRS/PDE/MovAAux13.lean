import HRS.PDE.MovAAux12

/-!
# MOVA Aux13: continuity of the pieces and the centred identity.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_continuous_of_components {F : Torus d → Euc d}
    (h : ∀ j, Continuous fun x => (F x).ofLp j) : Continuous F := by
  have e : F = fun x => WithLp.toLp 2 (fun j => (F x).ofLp j) := by
    funext x; ext j; simp
  rw [e]
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)

theorem mova_continuous_grad {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) : Continuous (Torus.grad f) :=
  mova_continuous_of_components fun j => by
    simp only [mova_grad_apply]
    exact mova_continuous_partialDeriv hf j

theorem mova_continuous_uReg (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hpos : ∀ x, 0 < ρ x) (hV : Torus.IsCk 2 D.V) : Continuous (movT_uReg D M ρ) :=
  mova_continuous_of_components fun j =>
    mova_continuous_of_isCk (mova_wc_isCk_one D M hρ hpos hV j)

theorem mova_continuous_gradGReg (D : DynData d) (M : ℝ) :
    Continuous (Torus.grad (b15c_gReg d D.s M)) :=
  mova_continuous_grad (mova_gReg_isCk D 1 M)

/-- `c₁` is continuous. -/
theorem mova_continuous_c1 (D : DynData d) (M : ℝ) {ρ : Torus d → ℝ} (hρ : Torus.IsCk 2 ρ)
    (hdens : IsProbDensity ρ) (hpos : ∀ x, 0 < ρ x) (hV : Torus.IsCk 2 D.V) :
    Continuous fun x => ∫ y, commKernel (Torus.grad (b15c_gReg d D.s M)) (movT_uReg D M ρ) x y
      ∂(withDensityReal ρ) := by
  have e : (fun x => ∫ y, commKernel (Torus.grad (b15c_gReg d D.s M)) (movT_uReg D M ρ) x y
      ∂(withDensityReal ρ)) = fun x =>
      inner ℝ (movT_uReg D M ρ x) (Torus.grad (convFun (b15c_gReg d D.s M) ρ) x) -
        convFun (b15c_gReg d D.s M)
          (fun y => ∑ j, Torus.partialDeriv j (fun z => ρ z * mova_wc D M ρ j z) y) x :=
    funext fun x => mova_c1_eq D M hρ hdens hpos hV x
  rw [e]
  have hc1 : Torus.IsCk 1 (convFun (b15c_gReg d D.s M) ρ) :=
    mova_isCk_one_convFun (mova_integrable_gReg D M) (mova_isCk_one_of_two hρ)
  exact ((mova_continuous_uReg D M hρ hpos hV).inner (mova_continuous_grad hc1)).sub
    (PDE.MFAux.continuous_convFun (mova_integrable_gReg D M) (mova_continuous_divRW D M hρ hpos hV))

theorem mova_continuous_commReg (D : DynData d) (N : ℕ) (M : ℝ) {ρ : Torus d → ℝ}
    (hρ : Torus.IsCk 2 ρ) (hdens : IsProbDensity ρ) (hpos : ∀ x, 0 < ρ x) (hV : Torus.IsCk 2 D.V) :
    Continuous fun X : Config d N => movT_commReg D N M ρ X := by
  have hw := mova_continuous_uReg D M hρ hpos hV
  have hG := mova_continuous_gradGReg D M
  have hh : Continuous fun p : Torus d × Torus d => commKernel (Torus.grad (b15c_gReg d D.s M))
      (movT_uReg D M ρ) p.1 p.2 := by
    have e : (fun p : Torus d × Torus d => commKernel (Torus.grad (b15c_gReg d D.s M))
        (movT_uReg D M ρ) p.1 p.2) = fun p => inner ℝ (movT_uReg D M ρ p.1)
          (Torus.grad (b15c_gReg d D.s M) (p.1 - p.2)) - inner ℝ (movT_uReg D M ρ p.2)
          (Torus.grad (b15c_gReg d D.s M) (p.1 - p.2)) := funext fun p => mova_commKernel_eq _ _ _ _
    rw [e]
    exact ((hw.comp continuous_fst).inner (hG.comp (continuous_fst.sub continuous_snd))).sub
      ((hw.comp continuous_snd).inner (hG.comp (continuous_fst.sub continuous_snd)))
  unfold movT_commReg modulatedEnergy
  have hc1 := mova_continuous_c1 D M hρ hdens hpos hV
  refine ((continuous_const.mul (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    hh.comp ((continuous_apply i).prodMk (continuous_apply j)))).sub
    (continuous_const.mul (continuous_finsetSum _ fun i _ => hc1.comp (continuous_apply i)))).add
    continuous_const

theorem mova_continuous_k (D : DynData d) (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hdens : IsProbDensity (ρ r)) (hpos : ∀ x, 0 < ρ r x)
    (hV : Torus.IsCk 2 D.V) (hκ : 0 < D.invβ) (hρtc : Continuous (ρt r)) :
    Continuous (mova_k D M ρ ρt r) := by
  have e : mova_k D M ρ ρt r = fun x => mova_Delta D M ρ ρt r x / ρ r x +
      D.invβ⁻¹ * convFun (b15c_gReg d D.s M) (mova_Delta D M ρ ρt r) x :=
    funext fun x => mova_k_eq D M hρ hdens hpos hV hκ hρtc x
  rw [e]
  have hDc : Continuous (mova_Delta D M ρ ρt r) :=
    (mova_continuous_divRW D M hρ hpos hV).sub hρtc
  exact (hDc.div (mova_continuous_of_isCk hρ) fun x => (hpos x).ne').add
    (continuous_const.mul (PDE.MFAux.continuous_convFun (mova_integrable_gReg D M) hDc))

theorem mova_continuous_phit (D : DynData d) (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hρ : Torus.IsCk 2 (ρ r)) (hpos : ∀ x, 0 < ρ r x) (hρtc : Continuous (ρt r)) :
    Continuous (movT_phit D M ρ ρt r) := by
  unfold movT_phit
  exact (continuous_const.mul (PDE.MFAux.continuous_convFun (mova_integrable_gReg D M) hρtc)).add
    (hρtc.div (mova_continuous_of_isCk hρ) fun x => (hpos x).ne')

end HRS
