import HRS.MC.D3TAsm
import HRS.Energy.StaticLimitEnergy

/-!
# Packet D47, auxiliary facts 1: the spectral form of `g_η` for every `η > 0`.

`g_η = specKernel a_η - κ_η` with `a_η(k) = ĝ_η(k) ≥ 0` (`k ≠ 0`), `a_η(0) = 0`, `κ_η = b (∫φ) η^{d-s}/(d-s)`;
`Δg_η = specKernel (-4π²|k|² a_η)`.  All for arbitrary `η > 0` (the `η < 1` restriction of D.3 is not needed).
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D47

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1 HRS.MC.D3T3 HRS.StaticLimitAux

variable {d : ℕ}

/-- The spectral coefficients of `g_η - const`. -/
def d47_a (ψ : Euc d → ℝ) (s b lam : ℝ) (k : Lattice d) : ℝ :=
  if k = 0 then 0 else fdlGhat ψ s b lam k

/-- The constant `κ_η = b (∫φ) η^{d-s}/(d-s)`. -/
def d47_kappa (ψ : Euc d → ℝ) (s b lam : ℝ) : ℝ :=
  b * (∫ y, fdlPhi ψ y) * (lam ^ ((d : ℝ) - s) / ((d : ℝ) - s))

lemma d47_enorm_zero : Lattice.enorm (0 : Lattice d) = 0 := by
  have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  simp [Lattice.enorm, this]

lemma d47_a_nonneg {ψ : Euc d → ℝ} {s b lam : ℝ} (hb0 : 0 ≤ b) (hlam : 0 < lam) (k : Lattice d) :
    0 ≤ d47_a ψ s b lam k := by
  unfold d47_a
  split_ifs
  · exact le_rfl
  · exact d3f_ghat_nonneg hb0 hlam k

lemma d47_enorm_sq_a {ψ : Euc d → ℝ} {s b lam : ℝ} (k : Lattice d) :
    Lattice.enorm k ^ 2 * d47_a ψ s b lam k = Lattice.enorm k ^ 2 * fdlGhat ψ s b lam k := by
  unfold d47_a
  split_ifs with h
  · subst h; simp [d47_enorm_zero]
  · rfl

lemma d47_a_le {ψ : Euc d → ℝ} {s b lam : ℝ} (hb0 : 0 ≤ b) (hlam : 0 < lam) (k : Lattice d) :
    d47_a ψ s b lam k ≤ Lattice.enorm k ^ 2 * d47_a ψ s b lam k := by
  have h0 := d47_a_nonneg (ψ := ψ) (s := s) hb0 hlam k
  by_cases hk : k = 0
  · subst hk; simp [d47_a]
  · have h1 := d3f_enorm_ge_one hk
    have : 1 ≤ Lattice.enorm k ^ 2 := by nlinarith
    nlinarith

lemma d47_sum_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    {b : ℝ} (hb0 : 0 < b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ lam : ℝ, 0 < lam → ∀ F : Finset (Lattice d),
      ∑ k ∈ F, Lattice.enorm k ^ 2 * d47_a ψ s b lam k ≤ M * lam ^ (-s - 2) := by
  obtain ⟨M, hM0, hM⟩ := d3f_ghat_partial hd hs0 hψ hb0
  refine ⟨M, hM0, fun lam hlam F => ?_⟩
  simp_rw [d47_enorm_sq_a]
  exact hM lam hlam F

lemma d47_summable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    {b : ℝ} (hb0 : 0 < b) {lam : ℝ} (hlam : 0 < lam) :
    Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * d47_a ψ s b lam k) ∧
    Summable (d47_a ψ s b lam) := by
  obtain ⟨M, hM0, hM⟩ := d47_sum_bound hd hs0 hψ hb0
  have hnn : ∀ k : Lattice d, 0 ≤ Lattice.enorm k ^ 2 * d47_a ψ s b lam k :=
    fun k => mul_nonneg (sq_nonneg _) (d47_a_nonneg hb0.le hlam k)
  have h1 : Summable (fun k : Lattice d => Lattice.enorm k ^ 2 * d47_a ψ s b lam k) :=
    summable_of_sum_le hnn (fun F => hM lam hlam F)
  refine ⟨h1, Summable.of_nonneg_of_le (fun k => d47_a_nonneg hb0.le hlam k)
    (fun k => d47_a_le hb0.le hlam k) h1⟩

lemma d47_tsum_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ)
    {b : ℝ} (hb0 : 0 < b) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ lam : ℝ, 0 < lam →
      ∑' k : Lattice d, Lattice.enorm k ^ 2 * d47_a ψ s b lam k ≤ M * lam ^ (-s - 2) := by
  obtain ⟨M, hM0, hM⟩ := d47_sum_bound hd hs0 hψ hb0
  refine ⟨M, hM0, fun lam hlam => ?_⟩
  have hnn : ∀ k : Lattice d, 0 ≤ Lattice.enorm k ^ 2 * d47_a ψ s b lam k :=
    fun k => mul_nonneg (sq_nonneg _) (d47_a_nonneg hb0.le hlam k)
  exact Real.tsum_le_of_sum_le hnn (fun F => hM lam hlam F)

lemma d47_funFourierCoeff (g : Torus d → ℝ) (k : Lattice d) :
    Torus.funFourierCoeff (fun x => (g x : ℂ)) k = Torus.fcoef g k := by
  simp only [Torus.funFourierCoeff, UnitAddTorus.mFourierCoeff, Torus.fcoef, smul_eq_mul]
  rw [Torus.volume_eq_pi_haar]
  rfl

lemma d47_Hs_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    Hs ψ s b lam = specKernel (d47_a ψ s b lam) := by
  refine eq_specKernel_of_coeff _ (d3f_Hs_continuous hd hs0 hψ hb.1 hlam) _
    (d47_summable hd hs0 hψ hb.1 hlam).2 (fun k => ?_)
  rw [d47_funFourierCoeff, d3f_fcoef_Hs hd hs0 hsd hψ hb hlam k]
  unfold d47_a
  split_ifs <;> simp

lemma d47_trunc_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    fdlTruncT ψ s b lam = fun x => specKernel (d47_a ψ s b lam) x - d47_kappa ψ s b lam := by
  rw [d3f_truncT_eq hd hs0 hsd hψ hb hlam, d47_Hs_eq hd hs0 hsd hψ hb hlam]
  rfl

lemma d47_cosMode_zero (k : Lattice d) : Torus.cosMode k (0 : Torus d) = 1 := by
  have h : (0 : Torus d) = Torus.mk 0 := by
    ext i; simp [Torus.mk]
  rw [h, Torus.cosMode_mk]
  simp [Lattice.dot]

lemma d47_spec_zero {a : Lattice d → ℝ} : specKernel a 0 = ∑' k, a k := by
  unfold specKernel
  simp [d47_cosMode_zero]

lemma d47_lap_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    Torus.laplacian (fdlTruncT ψ s b lam) =
      specKernel (fun k => -(4 * Real.pi ^ 2 * (Lattice.enorm k ^ 2 * d47_a ψ s b lam k))) := by
  set G := fdlTruncT ψ s b lam with hG
  have hsm : ∀ n : ℕ, ContDiff ℝ n (Torus.lift G) := d3f_trunc_smooth hd hs0 hsd hψ hb hlam
  have h2 : Torus.IsCk 2 G := by
    have := hsm 2
    unfold Torus.IsCk
    exact_mod_cast this
  have hcont : Continuous (Torus.laplacian G) := by
    have : Torus.laplacian G = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j G) x :=
      funext (HRS.PDE.laplacian_eq_sum G h2)
    rw [this]
    exact continuous_finset_sum _ fun j _ => HRS.PDE.continuous_partialDeriv j _
      (HRS.PDE.isCk_one_partialDeriv j G h2)
  have hsum : Summable (fun k : Lattice d =>
      -(4 * Real.pi ^ 2 * (Lattice.enorm k ^ 2 * d47_a ψ s b lam k))) :=
    ((d47_summable hd hs0 hψ hb.1 hlam).1.mul_left (4 * Real.pi ^ 2)).neg
  refine eq_specKernel_of_coeff _ hcont _ hsum (fun k => ?_)
  rw [d47_funFourierCoeff, ← HRS.PDE.coeffOf_eq_fcoef, HRS.PDE.coeffOf_laplacian G h2]
  unfold HRS.PDE.laplaceCoeff
  rw [HRS.PDE.coeffOf_eq_fcoef]
  by_cases hk : k = 0
  · subst hk; simp [d47_enorm_zero]
  · rw [hG, d3f_fcoef_trunc hd hs0 hsd hψ hb hlam hk]
    unfold d47_a
    simp only [hk, if_false]
    push_cast
    ring

lemma d47_lap_zero (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {lam : ℝ} (hlam : 0 < lam) :
    Torus.laplacian (fdlTruncT ψ s b lam) 0 =
      -(4 * Real.pi ^ 2 * ∑' k : Lattice d, Lattice.enorm k ^ 2 * d47_a ψ s b lam k) := by
  rw [d47_lap_eq hd hs0 hsd hψ hb hlam, d47_spec_zero, tsum_neg, tsum_mul_left]

end HRS.MC.D47
