import HRS.MS.Fp81S21CosRecon2
import HRS.MS.Fp81S21InitialThird
import HRS.MS.Fp81S21InitialWindow
import HRS.MS.QsfAsm10

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS (Euc cbNorm)
open HRS.Whole HRS.MS.R26T3 HRS.MS.S21 S45

/-!
`responseWindow R a x` is `windowPathOf (wholeSpaceIndex p.d) p.T a`
applied to `fun t => r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) t 0
(fun f => r26t3_a R f x)`. The window constructor takes the path at `a+t`
and falls back to zero if it is not continuous.
`fp81s21_initial_ellv R q x` is `SeqL2.ofSeq (fun j => r26t3_a R (q j) x)`.
`s21gPhi σ hT M` is `((s11p_cJ T) • s11p_J hT M).comp
(s21gTheta σ).toContinuousLinearEquiv.toContinuousLinearMap`.
`fp81s21_cosRecon_obs26 p y j` is `(1+(σ j).1^2)^(3/8)` times
`∫ v in Icc 0 p.T, r26t3_cosine p.T (σ j).1 v *
fp81s21_cosRecon_coordExt y (σ j).2 v`; the latter is the oscillator
coordinate of `y` on the interval and zero outside it.
-/

/-- Response-vector membership and coordinates, with a test-independent bound selected
before the shift. `InitialFamData` is constructed for each family from the existing
positive-coupling producer; its constant need not be uniform in the shift. -/
theorem fp81s21_respRecon_vector (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∃ Cresp : ℝ, 0 ≤ Cresp ∧ ∀ a : ℝ, 0 ≤ a → ∀ x : Euc p.d,
          Memℓp (fun j => r26t3_a R (r26t3_qwin R a j) x) 2 ∧
          (∀ j, SeqL2.coord (fp81s21_initial_ellv R (r26t3_qwin R a) x) j =
            r26t3_a R (r26t3_qwin R a j) x) ∧
          ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ ≤
            Cresp * featureSum (r26t3_J p.d) (r26t3_qwin R a) := by
  obtain ⟨δ0, hδ0, hhalf, hq⟩ := fp81s21_qwin_uniform p
  refine ⟨δ0, hδ0, hhalf, fun δ hδ hδle R hγ => ?_⟩
  have hδh : δ ≤ 1 / 2 := hδle.trans hhalf
  obtain ⟨_, _, hfamily⟩ := hq δ hδ hδle R
  obtain ⟨C, hC, hresponse⟩ := r26t3_response_smooth hδ hδh R hγ
  refine ⟨C, hC, fun a ha x => ?_⟩
  have hφ := (hfamily a ha).1
  have hφ' : IsSummableFeatureFamily (fp81s21_J1 p.d) (r26t3_qwin R a) := by
    simpa [fp81s21_J1, r26t3_J] using hφ
  obtain ⟨F⟩ := fp81s21_initialFamData_exists hδ hδh R hγ _ hφ'.1
  refine ⟨fp81s21_initial_ellv_memlp R hφ' F x,
    fun j => fp81s21_initial_ellv_coord R hφ' F x j, ?_⟩
  have hbound : ∀ j, |SeqL2.coord (fp81s21_initial_ellv R (r26t3_qwin R a) x) j| ≤
      C * cbNorm (r26t3_J p.d) (r26t3_qwin R a j) := by
    intro j
    rw [fp81s21_initial_ellv_coord R hφ' F x j]
    obtain ⟨hm, hn, -, -⟩ := hresponse (r26t3_qwin R a j) (hφ.1 j)
    have hs : |r26t3_a R (r26t3_qwin R a j) x| ≤
        cbNorm (r26t3_k p.d + 2) (r26t3_a R (r26t3_qwin R a j)) := by
      simpa [Real.norm_eq_abs] using HRS.MS.Tc5.tc5_cb_sup_le hm x
    exact hs.trans hn
  calc
    ‖fp81s21_initial_ellv R (r26t3_qwin R a) x‖ ≤
        ∑' j, C * cbNorm (r26t3_J p.d) (r26t3_qwin R a j) :=
      s45_norm_le_tsum (hφ.2.mul_left C) hbound
    _ = C * featureSum (r26t3_J p.d) (r26t3_qwin R a) := by
      rw [featureSum, ← tsum_mul_left]

#print axioms fp81s21_respRecon_vector

end HRS.Fp81.S21
end
