import HRS.MS.SA16Y11Src
import HRS.MS.SA16Y11Co2
import HRS.MP.RdGenerator

/-!
# S.A.16 (SA16Y11) Co3: G3 for iso/hilbert (`d-2 < s < d-1`): the source bound from the `AdjointRdData` / `coeffNormE` hypotheses

`sa16y11_iso_src_of_data`: for two `AdjointRdData s (m+2)` data `D1, D2` with the same `M` and `V`, densities `μ1, μ2`
with `coeffNormE d s m (μ1 r - μ2 r) ≤ δ` on `[0,T]`, the source of the difference of the iso/hilbert approximants
(`K = sa16y5_Kint ... (meanFieldDriftW D_a (μ_a ·))`, `ν1 - ν2 = D1.invβ - D2.invβ`) satisfies, for every `y ∈ W^{m+2,p}`,
`jetEnergy_m(S)^{1/p} ≤ Ce (|D1.invβ - D2.invβ| + δ) ‖y‖`, `Ce` depending only on `d, m, s, p, MB, Λ`.
The only regularity used is `IsRegularDensityW (m+3)` (so `AdjointRdData` at level `m+2`, which gives `m+5`, is more than enough),
and the density difference only through order `m+2` (the `coeffNormE` level).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q HRS.Whole.AppendixA.Phase2SA16P

section Co3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y11_wsup_le_coeff (s : ℝ) (m : ℕ) (f : Euc d → ℝ) :
    weightedSupE (m + 2) ((d : ℝ) + 3) f ≤ coeffNormE d s m f := by
  unfold coeffNormE
  exact le_add_self.trans le_self_add

set_option maxHeartbeats 6400000 in
theorem sa16y11_iso_src_of_data (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ ΛV G₀ νbar T : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s < (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ Ce : ℝ, 0 < Ce ∧ ∀ (D1 D2 : WholeDyn d) (μ1 μ2 : ℝ → Euc d → ℝ),
      AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D1 T μ1 → AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D2 T μ2 →
      D1.M = D2.M → D1.V = D2.V → ∀ δ : ℝ, 0 ≤ δ →
      (∀ r ∈ Icc (0 : ℝ) T, coeffNormE d s m (μ1 r - μ2 r) ≤ ENNReal.ofReal δ) →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, ∀ (B1 B2 : ℝ),
      SA16BddCoef (m + 1) B1 (sa16y4_bcInt d N t (fun r => meanFieldDriftW D1 (μ1 r)) σ) →
      SA16BddCoef (m + 1) B2 (sa16y4_bcInt d N t (fun r => meanFieldDriftW D2 (μ2 r)) σ) →
      ∀ (ν1 ν2 : ℝ), ν1 - ν2 = D1.invβ - D2.invβ → ∀ y : WmpSpace d (m + 1 + 1) p,
        jetEnergy d m p ((ν1 - ν2) • sa16so_Lap d m p y +
          sa16r_iota d m p ((sa16y5_Kint d m N p s D1.M t μ1 (fun r => meanFieldDriftW D1 (μ1 r)) σ -
            sa16y5_Kint d m N p s D2.M t μ2 (fun r => meanFieldDriftW D2 (μ2 r)) σ) y)) ^ (1 / p) ≤
          Ce * (|D1.invβ - D2.invβ| + δ) * ‖y‖ := by
  obtain ⟨Ce0, hCe0, hsrc⟩ := sa16y11_iso_src_bound d m hd s p MB Λ hs0 hs1 hfar
  set K0 : ℝ := ((d : ℝ) * d * MB) * ((d : ℝ) * sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s) with hK0
  set c1 : ℝ := (d : ℝ) ^ (m + 2) * 2 ^ (d + 3) with hc1
  have hc10 : 0 < c1 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    rw [hc1]; positivity
  refine ⟨Ce0 * (1 + (|K0| + 1) * c1), by positivity, fun D1 D2 μ1 μ2 hD1 hD2 hM hV δ hδ hcoef t ht N hN σ hσ B1 B2
    hb1 hb2 ν1 ν2 hν y => ?_⟩
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
  have hsd : s < d := by linarith
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
  have hmain := hsrc D1.M hMB1 t ht.1 μ1 μ2 hreg1 hreg2 δ' hδ'0 hDec
    (fun r => meanFieldDriftW D1 (μ1 r)) (fun r => meanFieldDriftW D2 (μ2 r)) δb hδb0 hdrift hder N hN σ hσ B1 B2
    hb1 hb2 ν1 ν2 y
  rw [← hM]
  rw [hν] at hmain ⊢
  refine hmain.trans ?_
  have hy0 := norm_nonneg y
  have hnu := abs_nonneg (D1.invβ - D2.invβ)
  have key : |D1.invβ - D2.invβ| + δb + δ' ≤ (1 + (|K0| + 1) * c1) * (|D1.invβ - D2.invβ| + δ) := by
    rw [hδb, hδ']
    nlinarith [mul_nonneg (mul_nonneg (abs_nonneg K0) hc10.le) hnu, mul_nonneg hc10.le hnu, mul_nonneg (abs_nonneg K0) hδ,
      mul_nonneg hc10.le hδ, mul_nonneg (mul_nonneg (abs_nonneg K0) hc10.le) hδ]
  calc Ce0 * (|D1.invβ - D2.invβ| + δb + δ') * ‖y‖ ≤ Ce0 * ((1 + (|K0| + 1) * c1) * (|D1.invβ - D2.invβ| + δ)) * ‖y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left key hCe0.le) hy0
    _ = Ce0 * (1 + (|K0| + 1) * c1) * (|D1.invβ - D2.invβ| + δ) * ‖y‖ := by ring

end Co3

end HRS.Whole.AppendixA.Phase2SA16R

end
