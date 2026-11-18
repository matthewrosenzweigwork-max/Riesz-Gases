import HRS.MS.S111X2Aux13
import HRS.MS.S111X2Aux12

/-!
# S11.1 X2, packet E03 (part 3): the response form as a bounded bilinear form on `L²(μ)` classes

`s111x2_susc_eq_inner`: `C_θ(u,v) = ⟨P [u], R_θ P [v]⟩` with `R_θ` the continuous linear resolvent `s111x2_Rm`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {K : H →L[ℝ] H} {Mg : ℝ} (hK : PosOp K Mg) {θ : ℝ} (hθ : 0 ≤ θ)

/-- The resolvent as a continuous linear map. -/
def s111x2_Rm : H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := s111x2_Res hK hθ
      map_add' := s111x2_Res_add hK hθ
      map_smul' := fun c x => s111x2_Res_smul hK hθ c x } 1
    (fun x => by simpa using (s111x2_Res_bounds hK hθ x).2.2)

theorem s111x2_Rm_apply (x : H) : s111x2_Rm hK hθ x = s111x2_Res hK hθ x := rfl

end Hilbert

section MeasurePart

variable {d : ℕ} {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}

theorem s111x2_toLp_neg {f : Euc d → ℝ} (hf : MemLp f 2 ν) :
    s111x2_toLp ν (fun x => -f x) = -s111x2_toLp ν f := by
  apply Lp.ext
  have hn : MemLp (fun x => -f x) 2 ν := hf.neg
  filter_upwards [s111x2_toLp_ae hn, s111x2_toLp_ae hf, Lp.coeFn_neg (s111x2_toLp ν f)]
    with x h1 h2 h3
  rw [h1, h3, Pi.neg_apply, h2]

theorem s111x2_cl_eq_Pc {f : Euc d → ℝ} (hf : MemLp f 2 ν) :
    s111x2_cl hf = Pc ν (s111x2_toLp ν f) := by
  apply Lp.ext
  have hint : Integrable (s111x2_toLp ν f) ν := (Lp.memLp _).integrable (by norm_num)
  have hmean : inner ℝ (one2 ν) (s111x2_toLp ν f) = HRS.Whole.pair ν f := by
    rw [inner_one2]
    exact integral_congr_ae (s111x2_toLp_ae hf)
  filter_upwards [s111x2_cl_ae hf, Lp.coeFn_sub (s111x2_toLp ν f) (inner ℝ (one2 ν) (s111x2_toLp ν f) • one2 ν),
    Lp.coeFn_smul (inner ℝ (one2 ν) (s111x2_toLp ν f)) (one2 ν), one2_ae (ν := ν), s111x2_toLp_ae hf]
    with x h1 h2 h3 h4 h5
  rw [Pc_apply, h2, Pi.sub_apply, h3, Pi.smul_apply, h4, h5, hmean, smul_eq_mul, mul_one] at *
  rw [← h1]
  simp [HRS.Whole.projMean]

variable {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} {Mg : ℝ} (hK : KRep g ν K Mg) {θ : ℝ} (hθ : 0 ≤ θ)

theorem s111x2_susc_eq_inner {u v : Euc d → ℝ} (hu : MemLp u 2 ν) (hv : MemLp v 2 ν) :
    HRS.Whole.susceptibilityCov g ν θ u v =
      inner ℝ (Pc ν (s111x2_toLp ν u)) (s111x2_Rm hK.posOp hθ (Pc ν (s111x2_toLp ν v))) := by
  rw [s111x2_susc_eq hK hθ hu hv, s111x2_Rm_apply, s111x2_cl_eq_Pc hu, s111x2_cl_eq_Pc hv]

end MeasurePart

end HRS.MS.S111X2
