import HRS.Sections.Q41Aux17

/-!
# Packet Q41, helper 18: the smooth-test covariance is the limit of the truncated mode sums

`q41_cov2 H t s φ ψ` is the entry of `PDE.stationaryLagCov` for the pair of tests `(φ, ψ)` at
times `(t, s)`.  Along every enumeration of the nonzero lattice the double mode sums
`∑_{i,j<n} φ̂(e i) ψ̂(e j) κ(t,s; e_{e i}, e_{e j})` converge to `κ(t,s; φ, ψ)` for smooth `φ, ψ`
(`q41_cov2_limit`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.Q41

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.PDE.MFPair

variable {d : ℕ}

section Kappa

variable {s β c₀ Λ₀ : ℝ} {V ρβ : Torus d → ℝ}

/-- The two-time covariance of smooth tests: `C(φ, S(t'-t) ψ)` for `t ≤ t'` and the symmetric
expression otherwise (the entries of `PDE.stationaryLagCov`). -/
def q41_cov2 (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ) (t t' : ℝ)
    (φ ψ : Torus d → ℝ) : ℝ :=
  if t ≤ t' then
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β φ (Sg H (t' - t) ψ)
  else
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (Sg H (t - t') φ) ψ

variable (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ)

lemma q41_tr_eq (φ : Torus d → ℝ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    q41_tr φ e n = fun x => ∑ i ∈ Finset.range n,
      Torus.funRealCoeff φ (e i) * Torus.realMode (e i) x := rfl

lemma q41_phi_split (φ : Torus d → ℝ) (e : ℕ ≃ NonzeroLattice d) (n : ℕ) :
    (fun x => φ x + -Torus.mean φ) = fun x => q41_tr φ e n x + q41_res φ e n x := by
  funext x
  simp only [q41_res]
  ring

lemma q41_realMode_ck (k : NonzeroLattice d) :
    Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (Torus.realMode k) :=
  isCk_of_smooth_ps (HRS.FieldSingAux.isSmooth_realMode k) _

lemma q41_realMode_cont (k : NonzeroLattice d) : Continuous (Torus.realMode k) :=
  q41_cont_of_smooth (HRS.FieldSingAux.isSmooth_realMode k)

theorem q41_cov2_limit (hd : 1 ≤ d) (e : ℕ ≃ NonzeroLattice d) {φ ψ : Torus d → ℝ}
    (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n,
      Torus.funRealCoeff φ (e i) * Torus.funRealCoeff ψ (e j) *
        q41_cov2 H t t' (Torus.realMode (e i)) (Torus.realMode (e j))) atTop
      (𝓝 (q41_cov2 H t t' φ ψ)) := by
  classical
  have hC := q41_covProps hd H
  obtain ⟨M, hM0, hM⟩ := q41_S_bound H hd
  set Cv := susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β with hCv
  have hφc := q41_cont_of_smooth hφ
  have hψc := q41_cont_of_smooth hψ
  have hφck : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) φ := isCk_of_smooth_ps hφ _
  have hψck : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) ψ := isCk_of_smooth_ps hψ _
  have htrck : ∀ (χ : Torus d → ℝ) (n : ℕ),
      Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (q41_tr χ e n) := fun χ n =>
    isCk_of_smooth_ps (q41_tr_smooth χ e n) _
  have hresck : ∀ (χ : Torus d → ℝ), Torus.IsSmooth χ → ∀ n : ℕ,
      Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) (q41_res χ e n) := fun χ hχ n =>
    isCk_of_smooth_ps (q41_res_smooth hχ e n) _
  have htrc : ∀ (χ : Torus d → ℝ) (n : ℕ), Continuous (q41_tr χ e n) := fun χ n =>
    q41_cont_of_smooth (q41_tr_smooth χ e n)
  -- the sup-norm decay of the truncation errors
  have hsup0 : ∀ (χ : Torus d → ℝ), Torus.IsSmooth χ →
      Tendsto (fun n => Torus.cbNorm 0 (q41_res χ e n)) atTop (𝓝 0) := fun χ hχ =>
    q41_trunc_cb hχ e 0
  have hsupL : ∀ (χ : Torus d → ℝ), Torus.IsSmooth χ →
      Tendsto (fun n => M * Torus.cbNorm (mStar d + 4) (q41_res χ e n)) atTop (𝓝 0) := fun χ hχ => by
    simpa using (q41_trunc_cb hχ e (mStar d + 4)).const_mul M
  have habs0 : ∀ (χ : Torus d → ℝ), Torus.IsSmooth χ → ∀ n x,
      |q41_res χ e n x| ≤ Torus.cbNorm 0 (q41_res χ e n) := fun χ hχ n x =>
    abs_le_cb_ps (isCk_of_smooth_ps (q41_res_smooth hχ e n) 0) x
  -- `S h` of the truncation error, and the split `ψ - ∫ψ = ψ_n + res_n`
  have hSsplit : ∀ (χ : Torus d → ℝ), Torus.IsSmooth χ → ∀ (n : ℕ) {h : ℝ}, 0 ≤ h →
      Sg H h χ = fun y => Sg H h (q41_tr χ e n) y + Sg H h (q41_res χ e n) y := by
    intro χ hχ n h hh
    have hck : Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) χ := isCk_of_smooth_ps hχ _
    have e1 := q41_S_add_const H hd hck (-Torus.mean χ) hh
    rw [← e1, q41_phi_split χ e n]
    exact S_add_ps hd H (htrck χ n) (hresck χ hχ n) hh
  have hSdiff : ∀ (χ : Torus d → ℝ), Torus.IsSmooth χ → ∀ (n : ℕ) {h : ℝ}, 0 ≤ h → ∀ x,
      |Sg H h (q41_tr χ e n) x - Sg H h χ x| ≤ M * Torus.cbNorm (mStar d + 4) (q41_res χ e n) := by
    intro χ hχ n h hh x
    have := congrFun (hSsplit χ hχ n hh) x
    rw [this]
    rw [sub_add_cancel_left, abs_neg]
    exact (hM _ (hresck χ hχ n) h hh).2 x
  have hSck : ∀ (χ : Torus d → ℝ), Torus.IsCk ((mStar d + 4 : ℕ) : WithTop ℕ∞) χ → ∀ {h : ℝ},
      0 ≤ h → Continuous (Sg H h χ) := fun χ hχ h hh => (hM χ hχ h hh).1
  have hrescont : ∀ (χ : Torus d → ℝ), Torus.IsSmooth χ → ∀ n x,
      |q41_tr χ e n x - (χ x + -Torus.mean χ)| ≤ Torus.cbNorm 0 (q41_res χ e n) := by
    intro χ hχ n x
    have : q41_tr χ e n x - (χ x + -Torus.mean χ) = -q41_res χ e n x := by
      simp only [q41_res]; ring
    rw [this, abs_neg]
    exact habs0 χ hχ n x
  have hshift : ∀ (χ : Torus d → ℝ), Continuous χ → Continuous fun x => χ x + -Torus.mean χ :=
    fun χ hχ => hχ.add continuous_const
  by_cases hle : t ≤ t'
  · have hh : 0 ≤ t' - t := by linarith
    simp only [q41_cov2, if_pos hle]
    have hsum : ∀ n, Cv (q41_tr φ e n) (Sg H (t' - t) (q41_tr ψ e n)) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Torus.funRealCoeff φ (e i) *
          Torus.funRealCoeff ψ (e j) * Cv (Torus.realMode (e i))
            (Sg H (t' - t) (Torus.realMode (e j))) := by
      intro n
      rw [q41_tr_eq ψ e n, q41_S_sum H hd (Finset.range n) (fun j => Torus.funRealCoeff ψ (e j))
        (fun j => Torus.realMode (e j)) (fun j => q41_realMode_ck _) hh, q41_tr_eq φ e n]
      have hcn : Continuous fun y => ∑ j ∈ Finset.range n, Torus.funRealCoeff ψ (e j) *
          Sg H (t' - t) (Torus.realMode (e j)) y :=
        continuous_finset_sum _ fun j _ => continuous_const.mul (hSck _ (q41_realMode_ck _) hh)
      rw [hC.sum1 (Finset.range n) (fun i => Torus.funRealCoeff φ (e i))
        (fun i => Torus.realMode (e i)) (fun i => q41_realMode_cont _) _ hcn]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hC.sum2 (Finset.range n) (fun j => Torus.funRealCoeff ψ (e j))
        (fun j => Sg H (t' - t) (Torus.realMode (e j))) (fun j => hSck _ (q41_realMode_ck _) hh) _
        (q41_realMode_cont _), Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hlim := hC.tendsto (f := fun x => φ x + -Torus.mean φ) (g := Sg H (t' - t) ψ)
      (fn := fun n => q41_tr φ e n) (gn := fun n => Sg H (t' - t) (q41_tr ψ e n))
      (hshift φ hφc) (hSck ψ hψck hh) (fun n => htrc φ n)
      (fun n => hSck _ (htrck ψ n) hh) (hsup0 φ hφ) (hsupL ψ hψ)
      (hrescont φ hφ) (fun n x => hSdiff ψ hψ n hh x)
    have hc1 := hC.const1 φ (Sg H (t' - t) ψ) (-Torus.mean φ) hφc (hSck ψ hψck hh)
    rw [hc1] at hlim
    simpa only [hsum] using hlim
  · have hh : 0 ≤ t - t' := by linarith
    simp only [q41_cov2, if_neg hle]
    have hsum : ∀ n, Cv (Sg H (t - t') (q41_tr φ e n)) (q41_tr ψ e n) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, Torus.funRealCoeff φ (e i) *
          Torus.funRealCoeff ψ (e j) * Cv (Sg H (t - t') (Torus.realMode (e i)))
            (Torus.realMode (e j)) := by
      intro n
      rw [q41_tr_eq φ e n, q41_S_sum H hd (Finset.range n) (fun i => Torus.funRealCoeff φ (e i))
        (fun i => Torus.realMode (e i)) (fun i => q41_realMode_ck _) hh, q41_tr_eq ψ e n]
      have hcn : Continuous fun y => ∑ j ∈ Finset.range n, Torus.funRealCoeff ψ (e j) *
          Torus.realMode (e j) y :=
        continuous_finset_sum _ fun j _ => continuous_const.mul (q41_realMode_cont _)
      rw [hC.sum1 (Finset.range n) (fun i => Torus.funRealCoeff φ (e i))
        (fun i => Sg H (t - t') (Torus.realMode (e i))) (fun i => hSck _ (q41_realMode_ck _) hh) _ hcn]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hC.sum2 (Finset.range n) (fun j => Torus.funRealCoeff ψ (e j))
        (fun j => Torus.realMode (e j)) (fun j => q41_realMode_cont _) _
        (hSck _ (q41_realMode_ck _) hh), Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hlim := hC.tendsto (f := Sg H (t - t') φ) (g := fun x => ψ x + -Torus.mean ψ)
      (fn := fun n => Sg H (t - t') (q41_tr φ e n)) (gn := fun n => q41_tr ψ e n)
      (hSck φ hφck hh) (hshift ψ hψc) (fun n => hSck _ (htrck φ n) hh)
      (fun n => htrc ψ n) (hsupL φ hφ) (hsup0 ψ hψ)
      (fun n x => hSdiff φ hφ n hh x) (hrescont ψ hψ)
    have hc2 := hC.const2 (Sg H (t - t') φ) ψ (-Torus.mean ψ) (hSck φ hφck hh) hψc
    rw [hc2] at hlim
    simpa only [hsum] using hlim

end Kappa

end HRS.Q41
