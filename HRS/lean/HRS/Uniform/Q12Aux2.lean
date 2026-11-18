import HRS.Energy.Coercivity
import HRS.PDE.Fourier
import HRS.PDE.Classical
import HRS.PDE.EnergyR2Fn
import HRS.Uniform.Q12Aux1

/-!
# Q12, part 2: the heat equation `∂_t P_t ψ = P_t (Δψ/4π²)` for the periodic heat mollifier
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.CoercAux

namespace HRS.Uniform.Q12

variable {d : ℕ}

/-- `(4π²)⁻¹ Δψ`, the generator of the semigroup `heatP d t` (kernel `e^{-t|k|²}`). -/
def heatGen (ψ : Torus d → ℝ) : Torus d → ℝ := fun y => (4 * Real.pi ^ 2)⁻¹ * Torus.laplacian ψ y

lemma q12_continuous_of_isCk {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) : Continuous ψ :=
  Torus.continuous_of_continuous_lift (show ContDiff ℝ 2 (Torus.lift ψ) from hψ).continuous

lemma q12_continuous_laplacian {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    Continuous (Torus.laplacian ψ) := by
  have : Torus.laplacian ψ = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j ψ) x :=
    funext (PDE.laplacian_eq_sum ψ hψ)
  rw [this]
  exact continuous_finsetSum _ fun j _ =>
    PDE.continuous_partialDeriv j _ (PDE.isCk_one_partialDeriv j ψ hψ)

lemma q12_continuous_heatGen {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    Continuous (heatGen ψ) :=
  continuous_const.mul (q12_continuous_laplacian hψ)

lemma q12_fcoef_laplacian {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (k : Lattice d) :
    Torus.fcoef (Torus.laplacian ψ) k =
      -((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ) * Torus.fcoef ψ k := by
  have := congrFun (PDE.coeffOf_laplacian ψ hψ) k
  rw [PDE.coeffOf_eq_fcoef, PDE.laplaceCoeff] at this
  rw [this, PDE.coeffOf_eq_fcoef]

lemma q12_fcoef_heatGen {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (k : Lattice d) :
    Torus.fcoef (heatGen ψ) k = -((Lattice.enorm k ^ 2 : ℝ) : ℂ) * Torus.fcoef ψ k := by
  have h1 : Torus.fcoef (heatGen ψ) k = ((4 * Real.pi ^ 2)⁻¹ : ℝ) * Torus.fcoef (Torus.laplacian ψ) k := by
    unfold Torus.fcoef heatGen
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    push_cast
    ring
  rw [h1, q12_fcoef_laplacian hψ]
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

lemma q12_sq_exp_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    a * Real.exp (-(t / 2) * a) ≤ (4 / t) * Real.exp (-(t / 4) * a) := by
  set z : ℝ := (t / 4) * a with hz
  have hz0 : 0 ≤ z := by positivity
  have h1 : z ≤ Real.exp z := by linarith [Real.add_one_le_exp z]
  have h2 : z * Real.exp (-z) ≤ 1 := by
    have : Real.exp (-z) * Real.exp z = 1 := by rw [← Real.exp_add]; simp
    calc z * Real.exp (-z) ≤ Real.exp z * Real.exp (-z) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = 1 := by rw [mul_comm]; exact this
  have e1 : Real.exp (-(t / 2) * a) = Real.exp (-z) * Real.exp (-z) := by
    rw [← Real.exp_add]; congr 1; rw [hz]; ring
  have e2 : Real.exp (-(t / 4) * a) = Real.exp (-z) := by congr 1; rw [hz]; ring
  rw [e1, e2]
  have e3 : a = (4 / t) * z := by rw [hz]; field_simp
  have h3 : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
  have h4 : 0 ≤ 4 / t := by positivity
  calc a * (Real.exp (-z) * Real.exp (-z)) = (4 / t) * (z * Real.exp (-z)) * Real.exp (-z) := by
        rw [e3]; ring
    _ ≤ (4 / t) * 1 * Real.exp (-z) := by gcongr
    _ = _ := by ring

/-- The heat equation: `∂_τ (P_τ ψ)(x) = (P_τ (Δψ/4π²))(x)` for `τ > 0`, `ψ ∈ C²`. -/
lemma q12_hasDerivAt_heatP {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (x : Torus d) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt (fun τ => heatP d τ ψ x) (heatP d t (heatGen ψ) x) t := by
  have hc := q12_continuous_of_isCk hψ
  have hcD := q12_continuous_heatGen hψ
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound hc
  set c : Lattice d → ℝ := fun k => (Torus.mode k x * Torus.fcoef ψ k).re with hcdef
  have hcb : ∀ k, |c k| ≤ M := fun k => by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_mode, one_mul]
    exact fcoef_norm_le hM k
  set g : Lattice d → ℝ → ℝ := fun k τ => Real.exp (-τ * Lattice.enorm k ^ 2) * c k with hg
  set g' : Lattice d → ℝ → ℝ := fun k τ =>
    -(Lattice.enorm k ^ 2) * (Real.exp (-τ * Lattice.enorm k ^ 2) * c k) with hg'
  set u : Lattice d → ℝ := fun k => (4 / t) * M * Real.exp (-(t / 4) * Lattice.enorm k ^ 2) with hu
  have hus : Summable u := (summable_gauss_lattice d (t / 4) (by positivity)).mul_left ((4 / t) * M)
  have hderiv : ∀ k τ, HasDerivAt (g k) (g' k τ) τ := by
    intro k τ
    have h1 : HasDerivAt (fun τ : ℝ => -τ * Lattice.enorm k ^ 2) (-(Lattice.enorm k ^ 2)) τ := by
      simpa using ((hasDerivAt_id τ).neg.mul_const (Lattice.enorm k ^ 2))
    have h2 := (h1.exp).mul_const (c k)
    refine h2.congr_deriv ?_
    simp only [hg']
    ring
  have hbound : ∀ k τ, τ ∈ Ioi (t / 2) → ‖g' k τ‖ ≤ u k := by
    intro k τ hτ
    have hτ' : t / 2 < τ := hτ
    simp only [hg', hu, Real.norm_eq_abs]
    have he : 0 ≤ Lattice.enorm k ^ 2 := sq_nonneg _
    rw [abs_mul, abs_neg, abs_of_nonneg he, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : Real.exp (-τ * Lattice.enorm k ^ 2) ≤ Real.exp (-(t / 2) * Lattice.enorm k ^ 2) := by
      apply Real.exp_le_exp.2
      nlinarith
    have h2 := q12_sq_exp_le he ht
    calc Lattice.enorm k ^ 2 * (Real.exp (-τ * Lattice.enorm k ^ 2) * |c k|)
        ≤ Lattice.enorm k ^ 2 * (Real.exp (-(t / 2) * Lattice.enorm k ^ 2) * M) := by
          gcongr
          exact hcb k
      _ = (Lattice.enorm k ^ 2 * Real.exp (-(t / 2) * Lattice.enorm k ^ 2)) * M := by ring
      _ ≤ ((4 / t) * Real.exp (-(t / 4) * Lattice.enorm k ^ 2)) * M := by gcongr
      _ = _ := by ring
  have hg0 : Summable fun k => g k t := by
    refine Summable.of_norm_bounded ((summable_gauss_lattice d t ht).mul_right M) fun k => ?_
    simp only [hg, Real.norm_eq_abs]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    gcongr
    exact hcb k
  have hmain := hasDerivAt_tsum_of_isPreconnected hus (isOpen_Ioi (a := t / 2))
    (isPreconnected_Ioi) (fun k τ _ => hderiv k τ) hbound (y₀ := t) (by
      show t / 2 < t; linarith) hg0 (y := t) (by show t / 2 < t; linarith)
  have hev : (fun τ => heatP d τ ψ x) =ᶠ[𝓝 t] fun τ => ∑' k, g k τ := by
    filter_upwards [Ioi_mem_nhds (show (0:ℝ) < t from ht)] with τ hτ
    rw [heatP_series hc hτ]
  refine (hmain.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [heatP_series hcD ht]
  refine tsum_congr fun k => ?_
  simp only [hg']
  rw [q12_fcoef_heatGen hψ k]
  have : (Torus.mode k x * (-((Lattice.enorm k ^ 2 : ℝ) : ℂ) * Torus.fcoef ψ k)).re =
      -(Lattice.enorm k ^ 2) * c k := by
    have : Torus.mode k x * (-((Lattice.enorm k ^ 2 : ℝ) : ℂ) * Torus.fcoef ψ k) =
        ((-(Lattice.enorm k ^ 2) : ℝ) : ℂ) * (Torus.mode k x * Torus.fcoef ψ k) := by
      push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [this]
  ring

end HRS.Uniform.Q12
