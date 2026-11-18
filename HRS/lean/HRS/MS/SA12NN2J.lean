import HRS.MS.SA12NN2I

/-!
# S.A.12 N2 (SA12N), part J: the commutator pairing at `s = d - 1`

For `u, v ∈ C_c`, `v ∈ C²` (symbol `m_q = κ ⟨q,ξ⟩² ‖ξ‖^{-1}` from `n3a_bridge`, `s = d-1`):
`|∫ u (x_l (g * D_q² v) - g * D_q²(x_l v))| ≤ C ‖q‖² ‖u‖₂ ‖v‖₂`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate FourierTransform

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqN1a HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT3
  HRS.MS.UniqN3a

variable {d : ℕ}

theorem sa12n_bridge_F (hd : 1 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : Euc d) (a b : Euc d → ℝ), Continuous a → HasCompactSupport a →
      ContDiff ℝ 2 b → HasCompactSupport b →
      Integrable (fun x => a x * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q b) x)
        volume ∧
      Integrable (fun ξ => (sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ : ℂ) *
        (sa12n_F a ξ * conj (sa12n_F b ξ))) volume ∧
      (∫ x, a x * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q b) x) =
        -(∫ ξ, (sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ : ℂ) *
          (sa12n_F a ξ * conj (sa12n_F b ξ))).re := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨c, hc, hbr⟩ := HRS.MS.UniqN3a.n3a_bridge hd hs0 (by linarith) (by linarith)
  refine ⟨c, hc, fun q a b ha hac hb hbc => ?_⟩
  have hLa : MemLp a 2 volume := ha.memLp_of_hasCompactSupport hac
  obtain ⟨i0, i1, e⟩ := hbr q a b hLa hb hbc
  have hmξ : ∀ ξ : Euc d, c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ ((d : ℝ) - 1 - d) =
      sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ := by
    intro ξ
    unfold sa12n_mq
    rw [show (d : ℝ) - 1 - d = -1 by ring, real_inner_comm]
    ring
  simp only [hmξ] at i1 e
  have hFa := sa12n_F_ae ha hac
  have hFb := sa12n_F_ae (a := b) hb.continuous hbc
  have hae : ∀ᵐ ξ ∂(volume : Measure (Euc d)),
      ((sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ : ℝ) : ℂ) * (fourierL2 a ξ * conj (fourierL2 b ξ)) =
        ((sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ : ℝ) : ℂ) * (sa12n_F a ξ * conj (sa12n_F b ξ)) := by
    filter_upwards [hFa, hFb] with ξ h1 h2
    rw [h1, h2]
  refine ⟨i0, i1.congr hae, ?_⟩
  have hsf : symbolForm (sa12n_mq (c * (2 * Real.pi) ^ 2) q) a b =
      (∫ ξ, (sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ : ℂ) *
        (sa12n_F a ξ * conj (sa12n_F b ξ))).re := by
    unfold symbolForm
    rw [integral_congr_ae hae]
  rw [hsf] at e
  have e2 : (∫ ξ, (sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ : ℂ) *
        (sa12n_F a ξ * conj (sa12n_F b ξ))).re =
      -∫ x, a x * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q b) x := e
  linarith [e2]

theorem sa12n_comm_pair (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : Euc d) (l : Fin d) (u v : Euc d → ℝ), Continuous u →
      HasCompactSupport u → ContDiff ℝ 2 v → HasCompactSupport v →
      |∫ x, u x * (x l * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q v) x -
          HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q (fun y => y l * v y)) x)| ≤
        C * ‖q‖ ^ 2 * (Real.sqrt (∫ x, u x ^ 2) * Real.sqrt (∫ x, v x ^ 2)) := by
  obtain ⟨c, hc, hb⟩ := sa12n_bridge_F hd
  have hκ : 0 ≤ c * (2 * Real.pi) ^ 2 := by positivity
  refine ⟨3 * (c * (2 * Real.pi) ^ 2) / (2 * Real.pi), by positivity,
    fun q l u v hu huc hv hvc => ?_⟩
  have hv1 : ContDiff ℝ 2 (fun y : Euc d => y l * v y) :=
    (EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).contDiff.mul hv
  have hv1c : HasCompactSupport (fun y : Euc d => y l * v y) := hvc.mul_left
  have hu1 := sa12n_xl_cc hu huc l
  obtain ⟨j0, k0, e0⟩ := hb q u v hu huc hv hvc
  obtain ⟨j1, k1, e1⟩ := hb q (fun x => x l * u x) v hu1.1 hu1.2 hv hvc
  obtain ⟨j2, k2, e2⟩ := hb q u (fun y => y l * v y) hu huc hv1 hv1c
  have hcore := sa12n_pair_core hd hκ q l hu huc hv.continuous hvc k1 k2 k0
  set A := ∫ ξ, (sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ : ℂ) *
    (sa12n_F (fun x => x l * u x) ξ * conj (sa12n_F v ξ)) with hA
  set B := ∫ ξ, (sa12n_mq (c * (2 * Real.pi) ^ 2) q ξ : ℂ) *
    (sa12n_F u ξ * conj (sa12n_F (fun x => x l * v x) ξ)) with hB
  have hI : ∫ x, u x * (x l * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q v) x -
          HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q (fun y => y l * v y)) x) =
      (∫ x, (x l * u x) * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1)) (qq q v) x) -
        ∫ x, u x * HRS.Whole.convFun (rieszKernel d ((d : ℝ) - 1))
          (qq q (fun y => y l * v y)) x := by
    rw [← integral_sub j1 j2]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [hI, e1, e2]
  have h1 : |-A.re - -B.re| = |(B - A).re| := by
    rw [Complex.sub_re]; congr 1; ring
  calc |(-A.re) - -B.re| = |(B - A).re| := h1
    _ ≤ ‖B - A‖ := Complex.abs_re_le_norm _
    _ ≤ _ := hcore.trans (le_of_eq (by ring))

end HRS.MH.AdjointRd.Phase2SA12Near
