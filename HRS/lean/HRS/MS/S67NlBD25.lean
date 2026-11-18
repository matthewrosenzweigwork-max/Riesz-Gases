import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux3
import HRS.MS.S67NlBD13
import HRS.MS.S67NlBD14
import HRS.MS.S67NlBD18
import HRS.MS.S67NlBD19
import HRS.MS.S67NlBD20
import HRS.MS.S67NlBD22
import HRS.MS.S67NlBD23
import HRS.MS.S67NlBD24

/-!
# S6.7 nonlinear breakdown, packet 25: projected source bound

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4766-4770 area, nonlinear part of
`S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: `v ∈ C²` (high weighted index); `F = movForce(√ρ₀ v)` and each `movForce(v W_iψ)` split
into local and far parts (14); the transport terms are bounded by 18 and 19, the nonlocal terms by
22 (Gaussian times local potential, level `σ-1-(movA-1)`) and 23 (Gaussian times far convolution with
the actual kernel `movb2_kfar`, jets bounded by `s67bd25_kfar_jets`), the product-source certificates
come from 20; `K` is the finite sum over coordinates of four terms; 24 projects.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- uniform jet bounds for the far kernels `∂_i g_far` -/
lemma s67bd25_kfar_jets (hs0 : 0 ≤ s) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i : Fin d, ContDiff ℝ (N : WithTop ℕ∞) (movb2_kfar d s i) ∧
      ∀ k ≤ N, ∀ z, ‖iteratedFDeriv ℝ k (movb2_kfar d s i) z‖ ≤ K := by
  choose C hC0 hC using fun j : Fin (N + 1) =>
    mv1_gfar_bound (d := d) hs0 ((j : ℕ) + 1) (by omega)
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC0 j), fun i => ?_⟩
  have hg : ContDiff ℝ ∞ (movb2_gfar d s) := mv1_gfar_smooth s
  have hF : ContDiff ℝ (N : WithTop ℕ∞) (fderiv ℝ (movb2_gfar d s)) :=
    hg.fderiv_right (m := (N : WithTop ℕ∞)) (by exact_mod_cast le_top)
  set L : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))
    with hL
  have hfun : movb2_kfar d s i = L ∘ (fderiv ℝ (movb2_gfar d s)) := rfl
  refine ⟨by rw [hfun]; exact L.contDiff.comp hF, fun k hk z => ?_⟩
  rw [hfun]
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun T => ?_)
    have := T.le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simpa [hL] using this
  refine (L.norm_iteratedFDeriv_comp_left (hF.contDiffAt) (by exact_mod_cast hk)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  have h1 := hC ⟨k, by omega⟩ z
  have h2 : (1 + ‖z‖) ^ (-s - (((k : ℕ) + 1 : ℕ) : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z])
      (by have : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  have h3 : ‖iteratedFDeriv ℝ (k + 1) (movb2_gfar d s) z‖ ≤ C ⟨k, by omega⟩ := by
    refine h1.trans ?_
    calc C ⟨k, by omega⟩ * (1 + ‖z‖) ^ (-s - (((k : ℕ) + 1 : ℕ) : ℝ))
        ≤ C ⟨k, by omega⟩ * 1 := mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (hC0 _)
      _ = _ := mul_one _
  calc ‖L‖ * ‖iteratedFDeriv ℝ (k + 1) (movb2_gfar d s) z‖
      ≤ 1 * C ⟨k, by omega⟩ :=
        mul_le_mul hLn h3 (norm_nonneg _) zero_le_one
    _ = C ⟨k, by omega⟩ := one_mul _
    _ ≤ ∑ j, C j := Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_univ _)

/-- four-term combination in `Σ^r` -/
lemma s67bd25_comb4 (r : ℝ) {f1 f2 f3 f4 : Euc d → ℝ} (h1 : MemOsc r f1) (h2 : MemOsc r f2)
    (h3 : MemOsc r f3) (h4 : MemOsc r f4) :
    MemOsc r (fun x => -f1 x - f2 x + f3 x + f4 x) ∧
    oscNorm r (fun x => -f1 x - f2 x + f3 x + f4 x) ≤
      oscNorm r f1 + oscNorm r f2 + oscNorm r f3 + oscNorm r f4 := by
  have e : (fun x => -f1 x - f2 x + f3 x + f4 x) =
      fun x => ((-1 * f1 x + -1 * f2 x) + f3 x) + f4 x := by funext x; ring
  obtain ⟨a1, b1⟩ := HRS.MS.MovC1.movc1_osc_smul r (-1) h1
  obtain ⟨a2, b2⟩ := HRS.MS.MovC1.movc1_osc_smul r (-1) h2
  obtain ⟨a12, b12⟩ := HRS.MS.MovC1.movc1_osc_add r a1 a2
  obtain ⟨a123, b123⟩ := HRS.MS.MovC1.movc1_osc_add r a12 h3
  obtain ⟨a1234, b1234⟩ := HRS.MS.MovC1.movc1_osc_add r a123 h4
  rw [e]
  refine ⟨a1234, b1234.trans ?_⟩
  rw [abs_neg, abs_one, one_mul] at b1 b2
  linarith

theorem s67bd_projected_source_bound (H : Mov2dTh d s β q ρ₀) (m : ℕ) (σ : ℝ)
    (hm : (d : ℝ) / 2 + 7 < m) (hσ : 2 ≤ σ) (hσm : σ + 4 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v ψ : Euc d → ℝ,
      Continuous v → MemOsc (m : ℝ) v → ContDiff ℝ 2 ψ → MemOsc σ ψ →
      (∀ i : Fin d, MemLp (s67bd_D i ψ) 2 volume) →
      MemOsc (σ - movA d s) (s67bd_R d s ρ₀ v ψ) ∧
      Integrable (fun x => Real.sqrt (ρ₀ x) * s67bd_R d s ρ₀ v ψ x) volume ∧
      (∫ x, Real.sqrt (ρ₀ x) * s67bd_R d s ρ₀ v ψ x) = 0 ∧
      oscNorm (σ - movA d s) (s67bd_R d s ρ₀ v ψ) ≤
        C * oscNorm (m : ℝ) v * oscNorm σ ψ := by
  have hd := H.hd
  have hs0 := H.hs0
  have hsd := H.hsd
  have ha1 : 1 ≤ movA d s := le_max_left _ _
  have ha2 : movA d s < 2 := by
    unfold movA; exact max_lt (by norm_num) (by linarith)
  have hr0 : 0 ≤ σ - movA d s := by linarith
  have hr1 : 1 ≤ σ - 1 := by linarith
  obtain ⟨C18, hC18, h18⟩ := s67bd_transport_local H m σ hm hσ hσm
  obtain ⟨C19, hC19, h19⟩ := s67bd_transport_far H m σ hσ
  obtain ⟨C20, hC20, h20⟩ := s67bd_product_source H m σ hm hσ hσm
  obtain ⟨C22, hC22, h22⟩ := s67bd_local_gaussian_output H (σ - 1) hr1
  obtain ⟨Kf, hKf, hkf⟩ := s67bd25_kfar_jets (d := d) (s := s) hs0 ⌈σ - movA d s⌉₊
  obtain ⟨C23, hC23, h23⟩ := s67bd_far_gaussian_output H (σ - movA d s) hr0
    ⌈σ - movA d s⌉₊ (Nat.le_ceil _) Kf hKf
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  have hsqrt : MemOsc (σ - movA d s) (fun x => Real.sqrt (ρ₀ x)) := by
    have := memOsc_schwartz (σ - movA d s) ψs
    rwa [hψs] at this
  have hsq2 : MemLp (fun x => Real.sqrt (ρ₀ x)) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 ψs).1
    rwa [hψs] at this
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.smooth _
  have hlog : ContDiff ℝ ∞ (fun y => Real.log (ρ₀ y)) :=
    hρsm.log (fun x => (hρpos x).ne')
  set T : ℝ := C18 + C19 + C22 * C20 + C23 * C20 with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hq0 : 0 ≤ 1 + oscNorm (σ - movA d s) (fun x => Real.sqrt (ρ₀ x)) := by
    have : 0 ≤ oscNorm (σ - movA d s) (fun x => Real.sqrt (ρ₀ x)) := Real.sqrt_nonneg _
    linarith
  refine ⟨(1 + oscNorm (σ - movA d s) (fun x => Real.sqrt (ρ₀ x))) * ((d : ℝ) * T),
    mul_nonneg hq0 (mul_nonneg (Nat.cast_nonneg d) hT0), fun v ψ hv hvm hψ2 hψm hψD => ?_⟩
  have hψ1 : ContDiff ℝ 1 ψ := hψ2.of_le (by norm_num)
  have hvC2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) v :=
    (mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ₀ H.hρ 0 m (by linarith)).choose_spec.2 v
      hv hvm |>.1
  have hvC1 : ContDiff ℝ 1 v := hvC2.of_le (by norm_num)
  -- the coordinate weights
  have hD1 : ∀ (u : Euc d → ℝ), ContDiff ℝ 2 u → ∀ i : Fin d, ContDiff ℝ 1 (s67bd_D i u) := by
    intro u hu i
    unfold s67bd_D
    exact (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hW1 : ∀ i : Fin d, ContDiff ℝ 1 (s67bd_W ρ₀ i ψ) := fun i =>
    (hD1 ψ hψ2 i).sub (((hD1 _ (hlog.of_le (by simp)) i).mul hψ1).div_const 2)
  have hh1 : ∀ i : Fin d, ContDiff ℝ 1 (fun x => v x * s67bd_W ρ₀ i ψ x) := fun i =>
    hvC1.mul (hW1 i)
  -- source of the transport force
  have hg1 : ContDiff ℝ 1 (fun x => Real.sqrt (ρ₀ x) * v x) := (hsqsm.of_le (by simp)).mul hvC1
  have hgI : Integrable (fun x => Real.sqrt (ρ₀ x) * v x) volume := hsq2.integrable_mul hvm.1
  have hsplit0 := s67bd_force_split hd hs0 hsd _ hg1 hgI
  -- the four pieces for each coordinate
  set A : ℝ := oscNorm (m : ℝ) v * oscNorm σ ψ with hA
  have hA0 : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  set g : Fin d → Euc d → ℝ := fun i x =>
        -(s67bd_local d s (fun y => Real.sqrt (ρ₀ y) * v y) i x * s67bd_W ρ₀ i ψ x) -
        (s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i x * s67bd_W ρ₀ i ψ x) +
        (Real.sqrt (ρ₀ x) * s67bd_local d s (fun y => v y * s67bd_W ρ₀ i ψ y) i x) +
        (Real.sqrt (ρ₀ x) * ∫ y, movb2_kfar d s i (x - y) * (v y * s67bd_W ρ₀ i ψ y))
    with hg
  have hpiece : ∀ i : Fin d, MemOsc (σ - movA d s) (g i) ∧
      oscNorm (σ - movA d s) (g i) ≤ T * A := by
    intro i
    obtain ⟨m1, n1⟩ := h18 v ψ hv hvm hψ1 hψm hψD i
    obtain ⟨m2, n2⟩ := h19 v ψ hvm hψ1 hψm hψD i
    obtain ⟨hI, hS, hbd⟩ := h20 v ψ hvm hψ1 hψm hψD i
    obtain ⟨m3, n3⟩ := h22 _ (hh1 i) hI hS i
    have e1 : σ - 1 - (movA d s - 1) = σ - movA d s := by ring
    rw [e1] at m3 n3
    obtain ⟨-, m4, n4⟩ := h23 (movb2_kfar d s i) (hkf i).1 (hkf i).2 _ hI
    obtain ⟨hcomb, hcn⟩ := s67bd25_comb4 (σ - movA d s) m1 m2 m3 m4
    refine ⟨hcomb, hcn.trans ?_⟩
    have hHn : 0 ≤ s67bd_Hnorm (σ - 1) (fun x => v x * s67bd_W ρ₀ i ψ x) := Real.sqrt_nonneg _
    have hIn : 0 ≤ ∫ x, |v x * s67bd_W ρ₀ i ψ x| := integral_nonneg (fun x => abs_nonneg _)
    have hbd' : (∫ x, |v x * s67bd_W ρ₀ i ψ x|) +
        s67bd_Hnorm (σ - 1) (fun x => v x * s67bd_W ρ₀ i ψ x) ≤ C20 * A := by
      refine hbd.trans_eq ?_
      rw [hA]; ring
    have b3 := n3.trans (mul_le_mul_of_nonneg_left (le_trans (le_of_eq (add_comm _ _)) hbd') hC22)
    have b4 := n4.trans (mul_le_mul_of_nonneg_left
      ((le_add_of_nonneg_right hHn).trans hbd') hC23)
    have b1 := le_of_le_of_eq n1
      (show C18 * oscNorm (m : ℝ) v * oscNorm σ ψ = C18 * A by rw [hA]; ring)
    have b2 := le_of_le_of_eq n2
      (show C19 * oscNorm (m : ℝ) v * oscNorm σ ψ = C19 * A by rw [hA]; ring)
    rw [hT]
    nlinarith [b1, b2, b3, b4]
  have hIi : ∀ i : Fin d, Integrable (fun x => v x * s67bd_W ρ₀ i ψ x) volume := fun i =>
    (h20 v ψ hvm hψ1 hψm hψD i).1
  have hKeq : s67bd_K d s ρ₀ v ψ = fun x => ∑ i : Fin d, g i x := by
    funext x
    unfold s67bd_K s67bd_F
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hF := ((hsplit0 x).2 i).2.2
    have hM := ((s67bd_force_split hd hs0 hsd _ (hh1 i) (hIi i) x).2 i).2.2
    have hfar : s67bd_far d s (fun y => v y * s67bd_W ρ₀ i ψ y) i x =
        ∫ y, movb2_kfar d s i (x - y) * (v y * s67bd_W ρ₀ i ψ y) := rfl
    rw [hF, hM, hfar]
    simp only [hg]
    ring
  obtain ⟨hKm, hKn⟩ := HRS.MS.MovC1.movc1_osc_sum (σ - movA d s) (Finset.univ : Finset (Fin d)) (f := g)
    (fun i _ => (hpiece i).1)
  have hKmem : MemOsc (σ - movA d s) (s67bd_K d s ρ₀ v ψ) := by rw [hKeq]; exact hKm
  have hKnorm : oscNorm (σ - movA d s) (s67bd_K d s ρ₀ v ψ) ≤ (d : ℝ) * (T * A) := by
    rw [hKeq]
    refine hKn.trans ?_
    refine (Finset.sum_le_sum (fun i _ => (hpiece i).2)).trans_eq ?_
    simp
  obtain ⟨-, hQm, hQI, hQ0, hQn⟩ := s67bd_projection H (σ - movA d s) hr0 _ hKmem
  refine ⟨hQm, hQI, hQ0, hQn.trans ?_⟩
  calc (1 + oscNorm (σ - movA d s) (fun x => Real.sqrt (ρ₀ x))) *
        oscNorm (σ - movA d s) (s67bd_K d s ρ₀ v ψ)
      ≤ (1 + oscNorm (σ - movA d s) (fun x => Real.sqrt (ρ₀ x))) * ((d : ℝ) * (T * A)) :=
        mul_le_mul_of_nonneg_left hKnorm hq0
    _ = _ := by rw [hA]; ring

end HRS.MS.BreakdownS67
