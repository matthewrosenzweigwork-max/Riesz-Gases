import HRS.MC.SEdgeS16aAux2

/-!
# S16a, Aux3: identification of the finite-dimensional marginals of the Gaussian `G`

For a finite set `S` of Fourier indices, enumerated as `e : Fin p ≃ S`, the vector
`W(y) = (F̂(e a))_a ∈ ℝ^p` of an element `y ∈ E_m` is a continuous linear image of `y`.  Under the centred
Gaussian `G` of the statement its law is `multivariateGaussian 0 C`, with `C_ab = ∫ e_{e a} R e_{e b}`
(`sed_Cmat` at the Haar background), because `eval y e_k = F̂(k)` and `hG` prescribes the covariances.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.S16a

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {m : ℝ}

/-- The enumeration of a finite set of frequencies. -/
def s16a_e (S : Finset (NonzeroLattice d)) (a : Fin S.card) : NonzeroLattice d :=
  (S.equivFin.symm a).1

theorem s16a_e_mem (S : Finset (NonzeroLattice d)) (a : Fin S.card) : s16a_e S a ∈ S :=
  (S.equivFin.symm a).2

theorem s16a_sum_eq (S : Finset (NonzeroLattice d)) {M : Type*} [AddCommMonoid M]
    (g : NonzeroLattice d → M) : ∑ k ∈ S, g k = ∑ a : Fin S.card, g (s16a_e S a) := by
  rw [← Finset.sum_coe_sort S g]
  exact (Equiv.sum_comp S.equivFin.symm (fun x : S => g x.1)).symm

/-- The test functions `e_k`, `k ∈ S`. -/
def s16a_phi (S : Finset (NonzeroLattice d)) (a : Fin S.card) : Torus d → ℝ :=
  Torus.realMode (s16a_e S a)

theorem s16a_phi_smooth (S : Finset (NonzeroLattice d)) (a : Fin S.card) :
    Torus.IsSmooth (s16a_phi S a) := StaticLimitAux.isSmooth_realMode' _

/-- The unweighted Fourier coefficient as a continuous linear functional on `E_m`. -/
def s16a_cf (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m →L[ℝ] ℝ :=
  (Lattice.jp k.1 ^ m) • (negCoordCLM k)

theorem s16a_cf_apply (k : NonzeroLattice d) (y : NegSobolev d m) :
    s16a_cf m k y = NegSobolev.fourierCoeff y k := rfl

/-- The coefficient vector of an element of `E_m` on the frequencies of `S`. -/
def s16a_Wmap (m : ℝ) (S : Finset (NonzeroLattice d)) :
    NegSobolev d m →L[ℝ] EuclideanSpace ℝ (Fin S.card) :=
  ∑ a : Fin S.card, (s16a_cf m (s16a_e S a)).smulRight (EuclideanSpace.single a (1 : ℝ))

theorem s16a_Wmap_apply (S : Finset (NonzeroLattice d)) (y : NegSobolev d m) (a : Fin S.card) :
    s16a_Wmap m S y a = NegSobolev.fourierCoeff y (s16a_e S a) := by
  classical
  unfold s16a_Wmap
  simp [Pi.single_apply, s16a_cf_apply]

open Classical in
/-- The reconstruction map from coefficient vectors on `S` to `E_m`. -/
def s16a_Phi (m : ℝ) (S : Finset (NonzeroLattice d)) (z : EuclideanSpace ℝ (Fin S.card)) :
    NegSobolev d m :=
  ∑ a : Fin S.card, (show NegSobolev d m from lp.single (E := fun _ : NonzeroLattice d => ℝ) 2
    (s16a_e S a) (Lattice.jp (s16a_e S a).1 ^ (-m) * z a))

theorem s16a_continuous_Phi (m : ℝ) (S : Finset (NonzeroLattice d)) :
    Continuous (s16a_Phi (d := d) m S) := by
  classical
  unfold s16a_Phi
  refine continuous_finsetSum _ fun a _ => ?_
  have hc : Continuous (fun x : ℝ => (show NegSobolev d m from
      lp.single (E := fun _ : NonzeroLattice d => ℝ) 2 (s16a_e S a) x)) :=
    (lp.isometry_single (E := fun _ : NonzeroLattice d => ℝ) (p := 2) (s16a_e S a)).continuous
  exact hc.comp (continuous_const.mul ((EuclideanSpace.proj a).continuous))

theorem s16a_proj_eq_Phi (S : Finset (NonzeroLattice d)) (y : NegSobolev d m) :
    s16a_proj S y = s16a_Phi m S (s16a_Wmap m S y) := by
  classical
  unfold s16a_proj s16a_Phi
  rw [s16a_sum_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [s16a_Wmap_apply]
  congr 1
  unfold NegSobolev.fourierCoeff
  rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
  simp
  rfl

theorem s16a_proj_eta_eq_Phi {N : ℕ} (hm : (d : ℝ) < 2 * m) (hN : 1 ≤ N) (S : Finset (NonzeroLattice d))
    (Q : Measure (Config d N)) (hQ : ∀ (a : Fin S.card), ∫ Y, pair (empirical Y) (s16a_phi S a) ∂Q = 0)
    (X : Config d N) :
    s16a_proj S (etaE m X (volume : Measure (Torus d))) =
      s16a_Phi m S (centeredStat Q (s16a_phi S) X) := by
  classical
  unfold s16a_proj s16a_Phi
  rw [s16a_sum_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [s16a_coord_eta hm hN]
  have : (centeredStat Q (s16a_phi S) X) a = Real.sqrt N * pair (empirical X) (s16a_phi S a) := by
    unfold centeredStat
    simp [hQ a]
  rw [this]
  rfl

end HRS.MC.SEdge.S16a

end
