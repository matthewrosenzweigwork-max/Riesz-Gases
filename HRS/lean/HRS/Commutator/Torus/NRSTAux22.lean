import HRS.Commutator.Torus.NRSTAux21

/-!
# NRS-T, part 22: cut-off lifts `u_N = φ(·/N) · u` of a trigonometric polynomial are Schwartz functions
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_mode_eq (k : Lattice d) (y : 𝔼) :
    Torus.mode k (Torus.mk y) = leibt_e (Lattice.toEuc k) y := by
  rw [Torus.mode_mk]
  unfold leibt_e
  rw [← Torus.dot_eq_inner]

lemma nrstr_e_temperate (a : 𝔼) : (fun y : 𝔼 => leibt_e a y).HasTemperateGrowth := by
  have h1 : (fun y : 𝔼 => 2 * Real.pi * ⟪a, y⟫).HasTemperateGrowth := by
    have : (fun y : 𝔼 => ⟪a, y⟫).HasTemperateGrowth := ((innerSL ℝ a)).hasTemperateGrowth
    exact (Function.HasTemperateGrowth.const (2 * Real.pi)).mul this
  have h2 := Complex.hasTemperateGrowth_exp_mul_I.comp h1
  exact h2

/-- The lift of a trigonometric polynomial to `ℝ^d`. -/
def nrstr_u (f : NRST.TPA d) (y : 𝔼) : ℂ := NRST.ev f (Torus.mk y)

lemma nrstr_u_eq (f : NRST.TPA d) (y : 𝔼) :
    nrstr_u f y = ∑ k ∈ f.coeff.support, f.coeff k * leibt_e (Lattice.toEuc k) y := by
  unfold nrstr_u
  rw [NRST.ev_apply_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [nrstr_mode_eq]

lemma nrstr_u_temperate (f : NRST.TPA d) : (nrstr_u f).HasTemperateGrowth := by
  have : nrstr_u f = fun y => ∑ k ∈ f.coeff.support, f.coeff k * leibt_e (Lattice.toEuc k) y :=
    funext (nrstr_u_eq f)
  rw [this]
  refine Function.HasTemperateGrowth.sum (fun k _ => ?_)
  exact (Function.HasTemperateGrowth.const (f.coeff k)).mul (nrstr_e_temperate _)

/-- The dilated cutoff `y ↦ φ(y/N)` as a Schwartz function. -/
def nrstr_phiN (N : ℝ) (hN : 0 < N) : SchwartzMap 𝔼 ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 N⁻¹ (inv_ne_zero hN.ne'))) (nrstr_phi (d := d))

lemma nrstr_phiN_apply (N : ℝ) (hN : 0 < N) (y : 𝔼) : nrstr_phiN N hN y = nrstr_phi (d := d) (N⁻¹ • y) := by
  simp [nrstr_phiN]

/-- The cut-off lift `u_N(y) = u(y) φ(y/N)` as a Schwartz function. -/
def nrstr_W (f : NRST.TPA d) (N : ℝ) (hN : 0 < N) : SchwartzMap 𝔼 ℂ :=
  SchwartzMap.smulLeftCLM ℂ (nrstr_u f) (nrstr_phiN N hN)

lemma nrstr_W_apply (f : NRST.TPA d) (N : ℝ) (hN : 0 < N) (y : 𝔼) :
    nrstr_W f N hN y = nrstr_u f y * nrstr_phi (d := d) (N⁻¹ • y) := by
  unfold nrstr_W
  rw [SchwartzMap.smulLeftCLM_apply_apply (nrstr_u_temperate f), smul_eq_mul, nrstr_phiN_apply]

lemma nrstr_W_hasSum (f : NRST.TPA d) (N : ℝ) (hN : 0 < N) (y : 𝔼) :
    HasSum (fun k : Lattice d => f.coeff k * (leibt_e (Lattice.toEuc k) y * nrstr_phi (d := d) (N⁻¹ • y)))
      (nrstr_W f N hN y) := by
  classical
  have e : nrstr_W f N hN y = ∑ k ∈ f.coeff.support,
      f.coeff k * (leibt_e (Lattice.toEuc k) y * nrstr_phi (d := d) (N⁻¹ • y)) := by
    rw [nrstr_W_apply, nrstr_u_eq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  refine hasSum_sum_of_ne_finset_zero (fun k hk => ?_)
  have : f.coeff k = 0 := by simpa using hk
  simp [this]

end HRS.Commutator.TorusNote
