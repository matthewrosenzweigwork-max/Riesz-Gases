import HRS.Commutator.Torus.NRSTAux14

/-!
# NRS-T, part 15: the mollified transport field `w_n = F_n * w` and `IsFracDeriv`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ}

lemma fcoef_fj (n : ℕ) (k : Lattice d) : Torus.fcoef (fj d n) k = ((fejCoef n k : ℝ) : ℂ) := by
  rw [fcoef_eq_coeffOf]
  have := HRS.PDE.MFThermalExist.coeffOf_fejer (d := d) (n + 1) (Nat.succ_pos n) k
  have e0 : KernelGrad.coeffOf (HRS.PDE.MFThermalExist.fejer (n + 1)) k =
      HRS.PDE.coeffOf (HRS.PDE.MFThermalExist.fejer (n + 1)) k := rfl
  rw [show (fj d n) = HRS.PDE.MFThermalExist.fejer (n + 1) from rfl, e0, this]
  unfold fejCoef
  push_cast
  rfl

lemma integrable_comp_proj {w : Torus d → Euc d} (hw : Integrable w) (j : Fin d) :
    Integrable (fun x => w x j) :=
  (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp hw

lemma mollV_apply_int {w : Torus d → Euc d} (hw : Integrable w) (n : ℕ) (x : Torus d) (j : Fin d) :
    mollV n w x j = HRS.convFun (fj d n) (fun y => w y j) x := by
  unfold mollV
  have := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integral_comp_comm (integrable_moll_of_integrable hw n x)
  rw [convFun_eq_sub]
  simpa using this.symm

lemma fcoef_mollV {w : Torus d → Euc d} (hw : Integrable w) (n : ℕ) (j : Fin d) (k : Lattice d) :
    Torus.fcoef (fun x => mollV n w x j) k = ((fejCoef n k : ℝ) : ℂ) * Torus.fcoef (fun x => w x j) k := by
  have e : (fun x => mollV n w x j) = HRS.convFun (fj d n) (fun y => w y j) :=
    funext fun x => mollV_apply_int hw n x j
  rw [e]
  have := text_fcoef_conv (fj_integrable n) (integrable_comp_proj hw j) k
  rw [show HRS.convFun (fj d n) (fun y => w y j) = textConv (fj d n) (fun y => w y j) from rfl, this,
    fcoef_fj]

lemma fcoef_vOf_Vn {v : Torus d → Euc d} (n : ℕ) (j : Fin d) (k : Lattice d) :
    Torus.fcoef (fun x => vOf (Vn n v) x j) k = ((fejCoef n k : ℝ) : ℂ) * Torus.fcoef (fun x => v x j) k := by
  rw [fcoef_eq_coeffOf]
  have : (fun x => vOf (Vn n v) x j) = fun x => (ev (Vn n v j) x).re := rfl
  rw [this, coeffOf_re_ev _ (Vn_real n j)]
  simp [Vn]

/-- Transport of `IsFracDeriv` to the mollified pair. -/
lemma isFracDeriv_moll {v w : Torus d → Euc d} {a : ℝ} (hw : Integrable w)
    (h : IsFracDeriv a v w) (n : ℕ) : IsFracDeriv a (vOf (Vn n v)) (mollV n w) := by
  intro j k
  rw [fcoef_mollV hw n j k, fcoef_vOf_Vn, h j k]
  push_cast
  ring

end HRS.Commutator.TorusNote.NRST
