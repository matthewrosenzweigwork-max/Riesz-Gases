import HRS.Main.A8PAux37
import HRS.Main.Headline

/-!
# Packet A8P, part 38: reindexing of the statistics vector along `ι ≃ Fin q`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-- The coordinate relabelling `EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ ι`, `(V w) i = w (e i)`. -/
def a8pV (e : ι ≃ Fin q) : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ ι :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e.symm).toContinuousLinearEquiv.toContinuousLinearMap

theorem a8pV_apply (e : ι ≃ Fin q) (w : EuclideanSpace ℝ (Fin q)) (i : ι) : a8pV e w i = w (e i) := by
  simp [a8pV, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem a8pV_norm (e : ι ≃ Fin q) (w : EuclideanSpace ℝ (Fin q)) : ‖a8pV e w‖ = ‖w‖ := by
  simp [a8pV]

theorem a8pV_opNorm_le (e : ι ≃ Fin q) : ‖a8pV e‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp [a8pV_norm]

theorem a8pV_inner (e : ι ≃ Fin q) (y : EuclideanSpace ℝ (Fin q)) (x : EuclideanSpace ℝ ι) :
    inner ℝ (a8pV e y) x = inner ℝ y (WithLp.toLp 2 fun j => x (e.symm j) : EuclideanSpace ℝ (Fin q)) := by
  simp only [PiLp.inner_apply, a8pV_apply, RCLike.inner_apply, conj_trivial]
  rw [← Equiv.sum_comp e (fun j => x.ofLp (e.symm j) * y.ofLp j)]
  simp


theorem a8p_fluctStat_reindex {Ω : Type*} {N : ℕ} (e : ι ≃ Fin q) (σ : ℝ) (X : ℝ≥0 → Ω → Config d N)
    (ρ : ℝ → Torus d → ℝ) (ts : ι → ℝ) (φ : ι → Torus d → ℝ) (ω : Ω) :
    fluctStat σ X ρ ts φ ω =
      a8pV e (fluctStat σ X ρ (fun j => ts (e.symm j)) (fun j => φ (e.symm j)) ω) := by
  ext i
  simp [fluctStat, a8pV_apply]

theorem a8p_surrogateCov_reindex (e : ι ≃ Fin q) (D : DynData d) (ρ : ℝ → Torus d → ℝ) (qq : ℝ)
    (ts : ι → ℝ) (φ : ι → Torus d → ℝ) :
    surrogateCov D ρ qq ts φ =
      (surrogateCov D ρ qq (fun j => ts (e.symm j)) (fun j => φ (e.symm j))).submatrix e e := by
  ext a b
  simp [surrogateCov]

theorem a8p_gauss_reindex (e : ι ≃ Fin q) (Sq : Matrix (Fin q) (Fin q) ℝ) (hS : Sq.PosSemidef) :
    multivariateGaussian 0 (Sq.submatrix e e) = (multivariateGaussian 0 Sq).map (a8pV e) := by
  have hS' : (Sq.submatrix e e).PosSemidef := hS.submatrix e
  refine Measure.ext_of_charFun (funext fun x => ?_)
  rw [charFun_multivariateGaussian hS']
  rw [charFun_apply, integral_map (a8pV e).continuous.aemeasurable (by fun_prop)]
  have h1 : ∀ y : EuclideanSpace ℝ (Fin q), Complex.exp (↑(inner ℝ (a8pV e y) x) * Complex.I) =
      Complex.exp (↑(inner ℝ y (WithLp.toLp 2 fun j => x (e.symm j) : EuclideanSpace ℝ (Fin q))) *
        Complex.I) := fun y => by rw [a8pV_inner]
  simp only [h1]
  rw [← charFun_apply, charFun_multivariateGaussian hS]
  congr 1
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub, inner_zero_left]
  congr 2
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply]
  congr 1
  rw [← Equiv.sum_comp e (fun j => x.ofLp (e.symm j) * ∑ l, Sq j l * x.ofLp (e.symm l))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e (fun l => Sq (e i) l * x.ofLp (e.symm l))]
  simp

theorem a8p_stat_law_reindex {Ω : Type*} {mΩ : MeasurableSpace Ω} {N : ℕ} (e : ι ≃ Fin q)
    (P : Measure Ω) (σ : ℝ) (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ) (ts : ι → ℝ)
    (φ : ι → Torus d → ℝ)
    (hmeas : Measurable (fluctStat σ X ρ (fun j => ts (e.symm j)) (fun j => φ (e.symm j)))) :
    fluctStatLaw P σ X ρ ts φ =
      (fluctStatLaw P σ X ρ (fun j => ts (e.symm j)) (fun j => φ (e.symm j))).map (a8pV e) := by
  unfold fluctStatLaw law
  rw [Measure.map_map (a8pV e).continuous.measurable hmeas]
  congr 1
  funext ω
  exact a8p_fluctStat_reindex e σ X ρ ts φ ω

theorem a8p_surr_law_reindex {Ω : Type*} {mΩ : MeasurableSpace Ω} (e : ι ≃ Fin q)
    (P : Measure Ω) [IsProbabilityMeasure P] (D : DynData d) (ρ : ℝ → Torus d → ℝ) (A qq : ℝ) (ts : ι → ℝ)
    (φ : ι → Torus d → ℝ) (η : Ω → (Torus d → ℝ) → ℝ) (hη : ∀ ψ : Torus d → ℝ, Measurable fun ω => η ω ψ)
    (hpsd : (surrogateCov D ρ qq (fun j => ts (e.symm j)) (fun j => φ (e.symm j))).PosSemidef) :
    surrogateStatLaw D ρ A qq ts φ P η =
      (surrogateStatLaw D ρ A qq (fun j => ts (e.symm j)) (fun j => φ (e.symm j)) P η).map (a8pV e) := by
  unfold surrogateStatLaw
  have hm : Measurable (fun ω => (WithLp.toLp 2 fun a : Fin q => A * η ω
      (propagator D ρ 0 (ts (e.symm a)) (φ (e.symm a))) : EuclideanSpace ℝ (Fin q))) :=
    a8p_vec_meas _ fun a => measurable_const.mul (hη _)
  have hV : Measurable (a8pV e) := (a8pV e).continuous.measurable
  haveI : IsProbabilityMeasure (law P (fun ω => (WithLp.toLp 2 fun a : Fin q => A * η ω
      (propagator D ρ 0 (ts (e.symm a)) (φ (e.symm a))) : EuclideanSpace ℝ (Fin q)))) :=
    inferInstanceAs (IsProbabilityMeasure (P.map _))
  have hconv := Measure.map_conv_addMonoidHom
    (μ := law P (fun ω => (WithLp.toLp 2 fun a : Fin q => A * η ω
      (propagator D ρ 0 (ts (e.symm a)) (φ (e.symm a))) : EuclideanSpace ℝ (Fin q))))
    (ν := multivariateGaussian 0 (surrogateCov D ρ qq (fun j => ts (e.symm j)) (fun j => φ (e.symm j))))
    (a8pV e).toLinearMap.toAddMonoidHom hV
  have h1 : law P (fun ω => (WithLp.toLp 2 fun a : ι => A * η ω (propagator D ρ 0 (ts a) (φ a)) :
      EuclideanSpace ℝ ι)) = (law P (fun ω => (WithLp.toLp 2 fun a : Fin q => A * η ω
      (propagator D ρ 0 (ts (e.symm a)) (φ (e.symm a))) : EuclideanSpace ℝ (Fin q)))).map (a8pV e) := by
    unfold law
    rw [Measure.map_map hV hm]
    congr 1
    funext ω
    ext i
    simp [a8pV_apply]
  rw [a8p_surrogateCov_reindex e D ρ qq ts φ, a8p_gauss_reindex e _ hpsd, h1]
  exact hconv.symm

end HRS.Main.A8P
