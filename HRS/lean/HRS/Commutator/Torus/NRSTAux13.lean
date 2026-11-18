import HRS.Commutator.Torus.NRSTAux12

/-!
# NRS-T, part 13: the mollified field `v_n = F_n * v` as a real trigonometric polynomial field
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ}

/-- The trigonometric polynomial field of Fejér means of the components of `v`. -/
def Vn (n : ℕ) (v : Torus d → Euc d) : Fin d → TPA d := fun j => trigOf n (fun x => v x j)

lemma Vn_real {v : Torus d → Euc d} (n : ℕ) (j : Fin d) (x : Torus d) :
    (ev (Vn n v j) x).im = 0 :=
  ev_real_of_symm _ (trigOf_symm n _) x

lemma convFun_eq_sub (g h : Torus d → ℝ) (x : Torus d) :
    HRS.convFun g h x = ∫ z, g z * h (x - z) := by
  unfold HRS.convFun
  rw [← integral_sub_left_eq_self (fun y => g (x - y) * h y) volume x]
  simp

lemma vOf_Vn {v : Torus d → Euc d} (hv : Continuous v) (n : ℕ) :
    vOf (Vn n v) = mollV n v := by
  funext x
  ext j
  have hc : Continuous fun y => v y j :=
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hv
  have := ev_trigOf n hc x
  have h2 : (ev (Vn n v j) x).re = HRS.convFun (fj d n) (fun y => v y j) x := by
    have := congrArg Complex.re (ev_trigOf n hc x)
    simpa [Vn] using this
  show (ev (Vn n v j) x).re = mollV n v x j
  rw [h2, mollV_apply hv, convFun_eq_sub]

lemma vOf_Vn_lip {v : Torus d → Euc d} (hv : Continuous v) {L : ℝ} (hL : 0 ≤ L)
    (hlip : IsLipschitzVF L v) (n : ℕ) : IsLipschitzVF L (vOf (Vn n v)) := by
  rw [vOf_Vn hv]
  exact mollV_lip hv hL hlip n

lemma vOf_Vn_tendsto {v : Torus d → Euc d} (hv : Continuous v) (x : Torus d) :
    Tendsto (fun n => vOf (Vn n v) x) atTop (𝓝 (v x)) := by
  have hcomp : ∀ j : Fin d, Tendsto (fun n => (vOf (Vn n v) x) j) atTop (𝓝 (v x j)) := by
    intro j
    have hc : Continuous fun y => v y j :=
      (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hv
    have hT := HRS.PDE.MFThermalExist.fejer_tendsto_uniformly (fun y => v y j) hc
    have h1 : Tendsto (fun N : ℕ => HRS.convFun (HRS.PDE.MFThermalExist.fejer N) (fun y => v y j) x)
        atTop (𝓝 (v x j)) := hT.tendsto_at x
    have h2 := h1.comp (tendsto_add_atTop_nat 1)
    have e : ∀ n, (vOf (Vn n v) x) j = HRS.convFun (HRS.PDE.MFThermalExist.fejer (n + 1))
        (fun y => v y j) x := by
      intro n
      have := congrArg Complex.re (ev_trigOf n hc x)
      simpa [vOf, Vn] using this
    simpa [e, Function.comp_def] using h2
  have : Tendsto (fun n => WithLp.toLp 2 (fun j => (vOf (Vn n v) x) j)) atTop
      (𝓝 (WithLp.toLp 2 (fun j => v x j))) :=
    ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).tendsto _).comp (tendsto_pi_nhds.2 hcomp)
  simpa using this

end HRS.Commutator.TorusNote.NRST
