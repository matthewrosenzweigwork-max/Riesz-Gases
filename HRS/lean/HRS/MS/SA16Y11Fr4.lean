import HRS.MS.SA16Y9Cr5
import HRS.MS.SA16Y11Fr3
import HRS.MS.SA16Y11Co3
import HRS.MS.SA16Y11Iso

/-!
# S.A.16 (SA16Y11) Fr4: `Sa16FracSrc` (`SA16Y9Cr5`), the source bound required in the fractional regime `d-1 < s < d` (heat-Volterra pipeline `SA16ApproxF`)

Same data and hypotheses as `Sa16IsoSrc` (`SA16Y9Ci1`), for iso/hilbert matrices, with the nonlocal operators `sa16y5f_NInt` (`W^{m+2,p} →L W^{m,p}`, no `ι`) of the
interpolated mollified densities in place of `sa16y5_NInt`:
`‖(ν¹-ν²)Δ_m v + ι_m(B_{m+1}(bc¹_n) v - B_{m+1}(bc²_n) v) - (NInt¹_n - NInt²_n) v‖ ≤ Ks (|ν¹-ν²| + δ) ‖v‖`.
`sa16y11_fracSrc : Sa16FracSrc ...` from `sa16y11f_NInt_diff` (Fr3), the drift lemmas (Dr1, Dr3), `sa16y11_bcInt_bdd` and `sa16y4_drift_const`.
The drift difference uses `0 ≤ s < d` only; the nonlocal difference uses `sa16y3_extend(A)` (bound linear in `‖a‖_{C^{m+2}}`), no positivity and no fractional-force term.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.Phase2SA16P

section Frac
variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem sa16y11_fracSrc (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)]
    (MB Λ ΛV G₀ νbar T : ℝ) (MCls : Matrix (Fin d) (Fin d) ℝ → Prop)
    (hMCls : ∀ M, MCls M → ∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ, A.transpose = -A ∧
      M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A) :
    Sa16FracSrc d s m p MB Λ ΛV G₀ νbar T MCls := by
  intro hs1 hsd'
  obtain ⟨Cn, hCn0, hN⟩ := sa16y11f_NInt_diff d m hd s p MB Λ hs0 hsd' hs1
  obtain ⟨Cb, hCb1, hCb⟩ := sa16y11_bcInt_diff d m hd
  obtain ⟨A, L, hA0, hL0, hbc⟩ := sa16y4_drift_const hd hs0 hsd' (m + 2) MB Λ ΛV G₀
  obtain ⟨B', hB'⟩ := sa16y11_bcInt_bdd d m hA0 hL0
  obtain ⟨-, ⟨Cj, hCj0, hCj⟩, -, -⟩ := closed_jet_energy_calculus d m p
  have hcL0 : 0 ≤ sa16so_cL d m := by unfold sa16so_cL; positivity
  set K0 : ℝ := ((d : ℝ) * d * MB) * ((d : ℝ) * sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s) with hK0
  set c1 : ℝ := (d : ℝ) ^ (m + 2) * 2 ^ (d + 3) with hc1
  have hc10 : 0 < c1 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    rw [hc1]; positivity
  set C1 : ℝ := sa16so_cB d (m + 1) Cb with hC1
  have hC1pos : 0 < C1 := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hCb0 : 0 < Cb := by linarith
    rw [hC1, sa16so_cB]
    exact mul_pos (by positivity) (mul_pos hdpos (mul_pos (by positivity) (mul_pos hCb0 (by positivity))))
  refine ⟨sa16so_cL d m + (C1 * |K0| + Cn) * c1, by positivity, fun D1 D2 μ1 μ2 hD1 hD2 hMC hM hV δ hδ hcoef t ht n σ hσ v => ?_⟩
  obtain ⟨hDs1, -, -⟩ := hD1.hs
  obtain ⟨hDs2, -, -⟩ := hD2.hs
  have htT : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hreg1 : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ1 r) := fun r hr =>
    sa16y11_regDensity_mono (by omega) (sa16so_regDensity_of_MF hD1.hμ.regular (htT r hr))
  have hreg2 : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ2 r) := fun r hr =>
    sa16y11_regDensity_mono (by omega) (sa16so_regDensity_of_MF hD2.hμ.regular (htT r hr))
  have hVh1 : VHypRd (m + 3) ΛV G₀ D1.V := HRS.MP.RdGen.rg_VHyp_mono hD1.hV (by omega) le_rfl le_rfl
  have hMB1 : ∀ i j, |D1.M i j| ≤ MB := hD1.hM
  have hMB2 : ∀ i j, |D2.M i j| ≤ MB := hD2.hM
  have hMB0 : 0 ≤ MB := (abs_nonneg _).trans (hMB1 ⟨0, by omega⟩ ⟨0, by omega⟩)
  have hVh2 : VHypRd (m + 3) ΛV G₀ D2.V := HRS.MP.RdGen.rg_VHyp_mono hD2.hV (by omega) le_rfl le_rfl
  have hsd : s < d := hsd'
  -- weights of the density difference
  have hDec : ∀ r ∈ Icc (0 : ℝ) t, sa16y5_Dec (m + 2) (c1 * δ) (fun y => μ1 r y - μ2 r y) := by
    intro r hr
    have h := (sa16y11_wsup_le_coeff s m (μ1 r - μ2 r)).trans (hcoef r (htT r hr))
    have := sa16y11_Dec_of_wsup hd (m + 2) hδ h
    have e : c1 * δ = (d : ℝ) ^ (m + 2) * (2 ^ (d + 3) * δ) := by rw [hc1]; ring
    rw [e]; exact this
  -- the drift difference
  set δ' : ℝ := c1 * δ with hδ'
  have hδ'0 : 0 ≤ δ' := by positivity
  set δb : ℝ := |K0| * δ' with hδb
  have hδb0 : 0 ≤ δb := by positivity
  have hdrift : ∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => meanFieldDriftW D1 (μ1 r) y j) ∧
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => meanFieldDriftW D2 (μ2 r) y j) := by
    intro r hr j
    have h1 := (sa16p_drift_bounds hd hs0 hsd m hDs1 hMB1 hVh1 (hreg1 r hr)).1
    have h2 := (sa16p_drift_bounds hd hs0 hsd m hDs2 hMB2 hVh2 (hreg2 r hr)).1
    have h1' : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (meanFieldDriftW D1 (μ1 r)) :=
      h1.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))
    have h2' : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (meanFieldDriftW D2 (μ2 r)) :=
      h2.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))
    let L : Euc d →L[ℝ] ℝ := EuclideanSpace.proj j
    exact ⟨L.contDiff.comp h1', L.contDiff.comp h2'⟩
  -- weights of each density through order 1
  set W : ℝ := (d : ℝ) * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2) with hW
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbW : ∀ (μ : Euc d → ℝ), IsRegularDensityW (m + 3) Λ μ →
      ∀ j ≤ 1, ∀ y, ‖iteratedFDeriv ℝ j μ y‖ ≤ W * sa16p_w d y := by
    intro μ hμ j hj y
    refine (sa16p_regular_bounds hμ j (by omega) y).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (sa16p_w_pos y).le
    rw [hW]
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (le_max_right _ _)) (by positivity)
    calc (d : ℝ) ^ j ≤ (d : ℝ) ^ 1 := pow_le_pow_right₀ hd1 hj
      _ = d := pow_one _
  have hdd : ∀ r ∈ Icc (0 : ℝ) t, ∀ j ≤ m + 1, ∀ x,
      ‖iteratedFDeriv ℝ j (fun x => meanFieldDriftW D1 (μ1 r) x - meanFieldDriftW D2 (μ2 r) x) x‖ ≤
        ((d : ℝ) * d * MB) * ((d : ℝ) * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s * δ')) := by
    intro r hr
    exact sa16y11_drift_diff hd hs0 hsd m D1 D2 (μ1 r) (μ2 r) W δ' hDs1 hDs2 hM hV hMB1
      ((hreg1 r hr).1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3)))
      ((hreg2 r hr).1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 3)))
      (hbW _ (hreg1 r hr)) (hbW _ (hreg2 r hr)) (sa16y11_Dec_w (hDec r hr))
  have hder : ∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, ∀ k ≤ m + 1, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => meanFieldDriftW D1 (μ1 r) y j - meanFieldDriftW D2 (μ2 r) y j) x‖ ≤ δb := by
    intro r hr j k hk x
    have hv : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
        (fun y => meanFieldDriftW D1 (μ1 r) y - meanFieldDriftW D2 (μ2 r) y) := by
      have h1 := (sa16p_drift_bounds hd hs0 hsd m hDs1 hMB1 hVh1 (hreg1 r hr)).1
      have h2 := (sa16p_drift_bounds hd hs0 hsd m hDs2 hMB2 hVh2 (hreg2 r hr)).1
      have h1' : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (meanFieldDriftW D1 (μ1 r)) :=
        h1.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))
      have h2' : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (meanFieldDriftW D2 (μ2 r)) :=
        h2.of_le (by exact_mod_cast (by omega : m + 1 ≤ m + 2))
      exact h1'.sub h2'
    have hk' : ContDiff ℝ (k : WithTop ℕ∞) (fun y => meanFieldDriftW D1 (μ1 r) y - meanFieldDriftW D2 (μ2 r) y) :=
      hv.of_le (by exact_mod_cast hk)
    have e : (fun y => meanFieldDriftW D1 (μ1 r) y j - meanFieldDriftW D2 (μ2 r) y j) =
        fun y => (meanFieldDriftW D1 (μ1 r) y - meanFieldDriftW D2 (μ2 r) y) j := by
      funext y; simp only [PiLp.sub_apply]
    rw [e]
    refine (sa16y11_comp_iter hk' j x).trans ((hdd r hr k hk x).trans ?_)
    rw [hδb, hK0]
    nlinarith [le_abs_self ((d : ℝ) * d * MB * ((d : ℝ) * sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s)), hδ'0,
      mul_le_mul_of_nonneg_right (le_abs_self ((d : ℝ) * d * MB * ((d : ℝ) * sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s))) hδ'0]
  -- the three pieces
  have hbcb := hCb δb hδb0 t ht.1 (fun r => meanFieldDriftW D1 (μ1 r)) (fun r => meanFieldDriftW D2 (μ2 r)) (n + 1)
    (Nat.succ_pos n) hdrift hder σ hσ
  have hb1 := hB' t ht.1 (fun r => meanFieldDriftW D1 (μ1 r))
    (fun r hr => by
      obtain ⟨h1, h2, h3⟩ := hbc νbar T D1 μ1 hD1 r (htT r hr)
      exact ⟨h1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 2 + 2)), h2,
        fun j hj1 hj2 x => h3 j hj1 (by omega) x⟩) (n + 1) (Nat.succ_pos n) σ hσ
  have hb2 := hB' t ht.1 (fun r => meanFieldDriftW D2 (μ2 r))
    (fun r hr => by
      obtain ⟨h1, h2, h3⟩ := hbc νbar T D2 μ2 hD2 r (htT r hr)
      exact ⟨h1.of_le (by exact_mod_cast (by omega : m + 2 ≤ m + 2 + 2)), h2,
        fun j hj1 hj2 x => h3 j hj1 (by omega) x⟩) (n + 1) (Nat.succ_pos n) σ hσ
  have hBsub := sa16so_B_sub (p := p) hb1 hb2
  have hBn : ‖sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ j x -
      sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ j x)‖ ≤ C1 * δb := by
    refine (sa16so_B_norm (p := p) hbcb).trans (le_of_eq ?_)
    rw [hC1, sa16so_cB, sa16so_cB]; ring
  have hMC' := hMCls _ hMC
  have hNn := hN hMC' hMB1 t ht.1 μ1 μ2 hreg1 hreg2 δ' hδ'0 hDec (n + 1) (Nat.succ_pos n) σ hσ v
  have hBv : ‖sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ) v -
      sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ) v)‖ ≤ C1 * δb * ‖v‖ := by
    have e : sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ) v -
        sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ) v =
        (sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ j x -
          sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ j x)) v := by
      rw [hBsub]; simp only [ContinuousLinearMap.sub_apply]
    rw [e]
    have h3 := (sa16r_iota d m p).le_opNorm ((sa16so_B d (m + 1) p (fun j x =>
      sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ j x -
      sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ j x)) v)
    have h4 := sa16y4_iota_norm (d := d) (p := p) m
    have h5 := (sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ j x -
      sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ j x)).le_opNorm v
    have h6 := norm_nonneg ((sa16so_B d (m + 1) p (fun j x =>
      sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ j x -
      sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ j x)) v)
    calc _ ≤ ‖sa16r_iota d m p‖ * ‖(sa16so_B d (m + 1) p (fun j x =>
          sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ j x -
          sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ j x)) v‖ := h3
      _ ≤ 1 * ‖(sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D1 (μ1 r)) σ j x -
          sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D2 (μ2 r)) σ j x)) v‖ :=
          mul_le_mul_of_nonneg_right h4 h6
      _ ≤ (C1 * δb) * ‖v‖ := by
          rw [one_mul]
          exact h5.trans (mul_le_mul_of_nonneg_right hBn (norm_nonneg _))
  have hL : ‖(D1.invβ - D2.invβ) • sa16so_Lap d m p v‖ ≤ |D1.invβ - D2.invβ| * sa16so_cL d m * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact ((sa16so_Lap d m p).le_opNorm v).trans (mul_le_mul_of_nonneg_right (sa16so_Lap_norm m) (norm_nonneg _))
  rw [← hM]
  have hS := (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hL hBv)) hNn)
  refine hS.trans ?_
  have hy0 := norm_nonneg v
  have hnu := abs_nonneg (D1.invβ - D2.invβ)
  rw [hδb, hδ']
  have hcl := hcL0
  nlinarith [mul_nonneg hnu hy0, mul_nonneg hδ hy0, mul_nonneg hcl (mul_nonneg hnu hy0), mul_nonneg hcl (mul_nonneg hδ hy0),
    mul_nonneg hC1pos.le (mul_nonneg (abs_nonneg K0) (mul_nonneg hc10.le (mul_nonneg hδ hy0))),
    mul_nonneg hCn0 (mul_nonneg hc10.le (mul_nonneg hδ hy0)),
    mul_nonneg hC1pos.le (mul_nonneg (abs_nonneg K0) (mul_nonneg hc10.le (mul_nonneg hnu hy0))),
    mul_nonneg hCn0 (mul_nonneg hc10.le (mul_nonneg hnu hy0))]

end Frac

end HRS.Whole.AppendixA.Phase2SA16R

end
