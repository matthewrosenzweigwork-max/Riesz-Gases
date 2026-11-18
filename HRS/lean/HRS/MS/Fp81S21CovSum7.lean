import HRS.MS.Fp81S21CovSum6
import HRS.MS.R2InterpAux3

/-!
# S2.1(iii), packet 16c: projective covariance coordinates and symmetry

The cumulative covariance is a projective tensor by its subtype construction.
Its oscillator coordinates commute with the block tsum; the 16b weighted
bound supplies the required summability under an explicit dual-norm
AEMeasurability premise. Symmetry on oscillator coordinates then passes to
all bilinear forms by the staged finite-rank projection convergence.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas
open HRS.MS.GenPath HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL
open HRS.MS.R2WinOrb HRS.MS.FixEq HRS.MS.R2Interp

private theorem fp81s21_block_coordinate_symmetric
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    {I : Set ℝ} {k : ℕ}
    (hblock : fp81s21_WindowCovarianceBlockContract D hlin I k)
    {ta tb : ℝ} {φa φb : Euc d → ℝ}
    (hφa : IsR2DualCombo m φa) (hφb : IsR2DualCombo m φb)
    (hta : ta ∈ Icc (0 : ℝ) H) (htb : tb ∈ Icc (0 : ℝ) H)
    (l₁ l₂ : StrongDual ℝ (OscPath d m H))
    (h₁ : ∀ w, l₁ w = OscDual.eval (r2PathAt w ta) φa)
    (h₂ : ∀ w, l₂ w = OscDual.eval (r2PathAt w tb) φb) :
    ((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![l₁, l₂]) =
      ((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![l₂, l₁]) := by
  have hforward := hblock.coordinate_spec.2 ta tb φa φb l₁ l₂
    hφa hφb hta htb h₁ h₂
  have hreverse := hblock.coordinate_spec.2 tb ta φb φa l₂ l₁
    hφb hφa htb hta h₂ h₁
  rw [hforward, hreverse, min_comm]
  congr 1
  apply integral_congr_ae
  filter_upwards with v
  congr 1
  funext x
  exact real_inner_comm _ _

/-- Every continuous bilinear coordinate of the cumulative projective tensor
commutes with the block tsum. In particular this identifies every oscillator
coordinate as the sum of its packet-15 block coordinates. The coordinate tsum
is summable by the 16b weighted bound; dual-norm AEMeasurability remains
explicit in the public hypotheses. -/
theorem fp81s21_window_covariance_cumulative_coordinate_tsum
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    (hblocks : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D hlin I k)
    (hdual : AEMeasurable (fun v => dualNormE r P (z v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    {q0 u : ℝ} (M : OscPath d m H [×2]→L[ℝ] ℝ) :
    Summable (fun k : ℕ =>
      ((fp81s21_blockValue D (Ioc q0 u) k : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2) M) ∧
      ((fp81s21_window_covariance_cumulative D q0 u : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2) M =
        ∑' k : ℕ,
          ((fp81s21_blockValue D (Ioc q0 u) k : projTensor (OscPath d m H) 2) :
            TensorDual (OscPath d m H) 2) M := by
  let ev : projTensor (OscPath d m H) 2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ M).comp (projTensor (OscPath d m H) 2).subtypeL
  have hsum := fp81s21_window_covariance_blocks_tsum_weighted D hlin
    (Ioc q0 u) measurableSet_Ioc
    (fun k => hblocks (Ioc q0 u) measurableSet_Ioc k) hdual
  have hblockSummable :
      Summable (fun k : ℕ => fp81s21_blockValue D (Ioc q0 u) k) :=
    Summable.of_enorm (ne_top_of_lt hsum.2.1)
  have hcoordSummable : Summable (fun k : ℕ =>
      ((fp81s21_blockValue D (Ioc q0 u) k : projTensor (OscPath d m H) 2) :
        TensorDual (OscPath d m H) 2) M) := by
    have h := ev.summable hblockSummable
    simpa [ev] using h
  have hmap := ev.map_tsum hblockSummable
  refine ⟨hcoordSummable, ?_⟩
  change ev (∑' k : ℕ, fp81s21_blockValue D (Ioc q0 u) k) =
    ∑' k : ℕ, ev (fp81s21_blockValue D (Ioc q0 u) k)
  exact hmap

/-- The cumulative value is projective and its full bilinear tensor is
symmetric. Symmetry is first checked on every oscillator coordinate using
`fp81s21_window_covariance_cumulative_coordinate_tsum`, then extended to all
continuous bilinear forms by the finite-rank projection convergence for
`OscPath`. -/
theorem fp81s21_window_covariance_cumulative_projective_symmetric
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    (hblocks : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D hlin I k)
    (hdual : AEMeasurable (fun v => dualNormE r P (z v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    {q0 u : ℝ} :
    ((fp81s21_window_covariance_cumulative D q0 u : projTensor (OscPath d m H) 2) :
      TensorDual (OscPath d m H) 2) ∈ projTensor (OscPath d m H) 2 ∧
      Tendsto (fun L => HRS.Sec7.tensorPow 2 (s102_Pj H D.fp81s21_hH L)
        ((fp81s21_window_covariance_cumulative D q0 u : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2)) atTop
        (𝓝 ((fp81s21_window_covariance_cumulative D q0 u : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2)) ∧
      ∀ M : OscPath d m H [×2]→L[ℝ] ℝ,
        ((fp81s21_window_covariance_cumulative D q0 u : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) M =
        ((fp81s21_window_covariance_cumulative D q0 u : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) (M.domDomCongr (Equiv.swap 0 1)) := by
  let J : TensorDual (OscPath d m H) 2 :=
    fp81s21_window_covariance_cumulative D q0 u
  have hJmem : J ∈ projTensor (OscPath d m H) 2 :=
    (fp81s21_window_covariance_cumulative D q0 u : projTensor (OscPath d m H) 2).property
  refine ⟨hJmem, ?_, ?_⟩
  · exact (s102_projection_strong (d := d) m H D.fp81s21_hH).2.2 2 J hJmem
  · intro M
    have hcoordSymm : ∀ (L : ℕ) (p q : ℕ × MultiIndex d),
        J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![s102_ellp D.fp81s21_hH L p, s102_ellp D.fp81s21_hH L q]) =
        J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![s102_ellp D.fp81s21_hH L q, s102_ellp D.fp81s21_hH L p]) := by
      intro L p q
      let l₁ : StrongDual ℝ (OscPath d m H) := s102_ellp D.fp81s21_hH L p
      let l₂ : StrongDual ℝ (OscPath d m H) := s102_ellp D.fp81s21_hH L q
      let Mleft := (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![l₁, l₂]
      let Mright := (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
        ![l₂, l₁]
      have hleft := fp81s21_window_covariance_cumulative_coordinate_tsum D hlin
        hblocks hdual (q0 := q0) (u := u) Mleft
      have hright := fp81s21_window_covariance_cumulative_coordinate_tsum D hlin
        hblocks hdual (q0 := q0) (u := u) Mright
      change J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![l₁, l₂]) =
        J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
          ![l₂, l₁])
      rw [hleft.2, hright.2]
      apply tsum_congr
      intro k
      exact fp81s21_block_coordinate_symmetric D hlin
        (hblocks (Ioc q0 u) measurableSet_Ioc k)
        (s102_isDualCombo p.2) (s102_isDualCombo q.2)
        (s102_node D.fp81s21_hH L p.1).property
        (s102_node D.fp81s21_hH L q.1).property l₁ l₂
        (by intro w; exact s102_ellp_eval D.fp81s21_hH L p w)
        (by intro w; exact s102_ellp_eval D.fp81s21_hH L q w)
    have hfinite : ∀ (L : ℕ) (M : OscPath d m H [×2]→L[ℝ] ℝ),
        J (M.compContinuousLinearMap fun _ => s102_Pj H D.fp81s21_hH L) =
        J ((M.domDomCongr (Equiv.swap 0 1)).compContinuousLinearMap
          fun _ => s102_Pj H D.fp81s21_hH L) := by
      intro L M
      rw [s102_pair_expand D.fp81s21_hH L M J,
        s102_pair_expand D.fp81s21_hH L (M.domDomCongr (Equiv.swap 0 1)) J]
      let e : (Fin 2 → ℕ × MultiIndex d) ≃ (Fin 2 → ℕ × MultiIndex d) :=
        Equiv.arrowCongr (Equiv.swap 0 1) (Equiv.refl _)
      let S : Finset (Fin 2 → ℕ × MultiIndex d) :=
        Fintype.piFinset (fun _ : Fin 2 => s102_idx d L)
      have hmem : ∀ x, x ∈ S ↔ e x ∈ S := by
        intro x
        constructor
        · intro hx
          apply Fintype.mem_piFinset.mpr
          intro i
          have hi := (Fintype.mem_piFinset.mp hx) (Equiv.swap 0 1 i)
          simpa [S, e, Equiv.arrowCongr] using hi
        · intro hx
          apply Fintype.mem_piFinset.mpr
          intro i
          have hi := (Fintype.mem_piFinset.mp hx) (Equiv.swap 0 1 i)
          simpa [S, e, Equiv.arrowCongr] using hi
      apply Finset.sum_equiv e (s := S) (t := S) hmem
      intro x hx
      have hM :
          M (fun i => s102_bpath H L (x i)) =
            (M.domDomCongr (Equiv.swap 0 1))
              (fun i => s102_bpath H L (e x i)) := by
        simp [e, Equiv.arrowCongr]
      have hJ :
          J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ellp D.fp81s21_hH L (x 0), s102_ellp D.fp81s21_hH L (x 1)]) =
          J ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ellp D.fp81s21_hH L (e x 0), s102_ellp D.fp81s21_hH L (e x 1)]) := by
        simpa [e, Equiv.arrowCongr] using hcoordSymm L (x 0) (x 1)
      exact congrArg₂ (fun x y : ℝ => x * y) hM hJ
    change J M = J (M.domDomCongr (Equiv.swap 0 1))
    have ⟨_, _, hprojTensor⟩ := s102_projection_strong (d := d) m H D.fp81s21_hH
    have t1 := (ContinuousLinearMap.apply ℝ ℝ M).continuous.continuousAt.tendsto.comp
      (hprojTensor 2 J hJmem)
    let Mswap := M.domDomCongr (Equiv.swap 0 1)
    have t2 := (ContinuousLinearMap.apply ℝ ℝ Mswap).continuous.continuousAt.tendsto.comp
      (hprojTensor 2 J hJmem)
    have e : ∀ L : ℕ,
        ((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L =>
          HRS.Sec7.tensorPow 2 (s102_Pj H D.fp81s21_hH L) J) L =
        ((ContinuousLinearMap.apply ℝ ℝ Mswap) ∘ fun L =>
          HRS.Sec7.tensorPow 2 (s102_Pj H D.fp81s21_hH L) J) L := by
      intro L
      exact hfinite L M
    have t2' : Tendsto
        (((ContinuousLinearMap.apply ℝ ℝ M) ∘ fun L =>
          HRS.Sec7.tensorPow 2 (s102_Pj H D.fp81s21_hH L) J)) atTop
        (𝓝 (J (M.domDomCongr (Equiv.swap 0 1)))) := by
      refine t2.congr ?_
      intro L
      exact (e L).symm
    have heq := tendsto_nhds_unique t1 t2'
    simpa [Mswap] using heq

#print axioms fp81s21_window_covariance_cumulative_coordinate_tsum
#print axioms fp81s21_window_covariance_cumulative_projective_symmetric

end HRS.Fp81.S21

end
