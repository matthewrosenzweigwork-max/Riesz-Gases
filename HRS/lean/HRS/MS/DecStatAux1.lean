import HRS.MS.MainRdStatAux22
import HRS.MS.ZeroTempAux16

/-!
# SA4, packet 1: S.A.4 `main_rd_dec_stat`: plan, standing-assumption monotonicity, `C_b^{m_*}` data

Worker SA11 (2026-10-25), row S.A.4 `HRS.Whole.AppendixA.main_rd_dec_stat` (prefix `sa4_`, namespace `HRS.MS.DecStat`).

## Route (reduction to the S.A.2 engine `HRS/MS/MainRdStatAux*.lean`)

`AdjointInputRd (wClass m p) (wWeakClass m p) m_* C T Kad` with `j = m_* = d/2 + 3` gives, for the orbit `f = U^{r,t}φ` of a test
`φ ∈ wClass`, a `C_b^{m_*}` bound `‖f‖_{C_b^{m_*}} ≤ Kad ‖φ‖_{wClass}`.  Therefore:
* the uloc norms of the S.A.2 engine are controlled by `C_b^{m_*}` (`ulocNormE_le_cb`): the `Y_0` bound (`Sa4Y0`) and the covariance
  test bound (`Sa4Test`: index `mm = d/2 + 1 ≥ (d-s)/2`, `mm + 1 ≤ m_*`) hold with `cbNorm m_*` hypotheses only;
* the commutator along the orbit is the sub-Coulomb S.B.5(ii),(iii) (weak `W^{m,p}` jet, `sa11_transport`), with the extra additive
  error `c₂ e_N^𝔠`;
* all the remaining S.A.2 per-`N` lemmas that do not mention the commutator or the test class are reused (via
  `sa4_standing_mono`: `RdStanding` at level `(m_𝔠 + 3, m_𝔠 + 4)` implies it at `(m_* + 3, m_* + 4)`), the others are copied with
  these two changes (files `DecStatAux4..8`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.MainRdStat
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ}

/-- `RdStanding` is monotone in the two regularity levels. -/
theorem sa4_standing_mono {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ}
    {r mV r' mV' : ℕ} {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr : r' ≤ r) (hm : mV' ≤ mV) :
    RdStanding S R MB Λ ΛV G₀ m20 r' mV' C₀ 𝔈 :=
  { flow := hS.flow
    mean_field :=
      { solution := hS.mean_field.solution
        datum := hS.mean_field.datum
        regular := fun N hN => sa2_regular_mono (hS.mean_field.regular N hN) hr le_rfl
        time_derivative := hS.mean_field.time_derivative }
    matrix_bound := hS.matrix_bound
    potential := sa2_vhyp_mono hS.potential hm
    energy := hS.energy
    second_moment := hS.second_moment
    filtered := hS.filtered }

/-- The coordinate derivative of a `C_b^{k+1}` function is `C_b^k`, with the norm bound. -/
theorem sa4_vj_memCb {k : ℕ} {g : Euc d → ℝ} (hg : MemCb (k + 1) g) (j : Fin d) :
    MemCb k (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)) ∧
      cbNorm k (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)) ≤ cbNorm (k + 1) g := by
  set v : Euc d → ℝ := fun x => fderiv ℝ g x (EuclideanSpace.single j 1) with hv
  have hg1 : ContDiff ℝ k (fderiv ℝ g) := hg.1.fderiv_right (by exact_mod_cast le_rfl)
  have hvd : ContDiff ℝ k v :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Euc d)).contDiff.comp hg1
  have hb : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i v x‖ ≤ ‖iteratedFDeriv ℝ (i + 1) g x‖ := by
    intro i hi x
    have h := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ g)
      (c := (EuclideanSpace.single j (1 : ℝ) : Euc d)) (x := x) (N := (k : ℕ∞ω)) (n := i)
      hg1.contDiffAt (by exact_mod_cast hi)
    rw [EuclideanSpace.norm_single, norm_one, one_mul, norm_iteratedFDeriv_fderiv] at h
    exact h
  have hbdd : ∀ i ≤ k, BddAbove (Set.range fun x => ‖iteratedFDeriv ℝ i v x‖) := by
    intro i hi
    obtain ⟨M, hM⟩ := hg.2 (i + 1) (by omega)
    exact ⟨M, by
      rintro _ ⟨x, rfl⟩
      exact (hb i hi x).trans (hM ⟨x, rfl⟩)⟩
  refine ⟨⟨hvd, hbdd⟩, ?_⟩
  unfold cbNorm
  have hterm : ∀ i ∈ Finset.range (k + 1), (⨆ x : Euc d, ‖iteratedFDeriv ℝ i v x‖) ≤
      ⨆ x : Euc d, ‖iteratedFDeriv ℝ (i + 1) g x‖ := by
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    exact ciSup_le fun x => (hb i hi' x).trans (le_ciSup (hg.2 (i + 1) (by omega)) x)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_range_succ' (fun i => ⨆ x : Euc d, ‖iteratedFDeriv ℝ i g x‖) (k + 1)]
  have h0 : 0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 g x‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  linarith

/-- The `Y_0` bound for a function of class `C_b^{m_*}` (only `cbNorm m_*` is used). -/
def Sa4Y0 (d : ℕ) (χ : Euc d → ℝ) (Cy : ℝ) : Prop :=
  ∀ m₀ : ℕ, m₀ ≤ mStar d → ∀ (ψ : Euc d → ℝ) (X : ℝ), 0 ≤ X →
    MemCb (mStar d) ψ → cbNorm (mStar d) ψ ≤ X → Y0Class m₀ χ ψ ∧ y0Norm m₀ χ ψ ≤ Cy * X

theorem sa4_y0 {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) : ∃ Cy : ℝ, 0 ≤ Cy ∧ Sa4Y0 d χ Cy := by
  obtain ⟨Cu, hCu0, hCu⟩ := HRS.MS.Ul.ulocNormE_le_cb (d := d) (mStar d) χ hχ
  obtain ⟨Cy, hCy0, hCy⟩ := sa2_y0 hχ
  refine ⟨Cy * (Cu + 1), by positivity, fun m₀ hm ψ X hX hcb hcbX => ?_⟩
  have h2 : cbNorm 2 ψ ≤ X := (sa2_cbNorm_mono sa2_two_le_mStar ψ).trans hcbX
  have hul : ulocNormE (mStar d) χ ψ ≤ ENNReal.ofReal ((Cu + 1) * X) :=
    (hCu ψ hcb).trans (ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_left hcbX hCu0.le]))
  have hX' : cbNorm 2 ψ ≤ (Cu + 1) * X := h2.trans (by nlinarith)
  obtain ⟨h1, h3⟩ := hCy m₀ hm ψ ((Cu + 1) * X) (by positivity) (sa2_memCb_mono sa2_two_le_mStar hcb) hX' hul
  exact ⟨h1, h3.trans (le_of_eq (by ring))⟩

end HRS.MS.DecStat
