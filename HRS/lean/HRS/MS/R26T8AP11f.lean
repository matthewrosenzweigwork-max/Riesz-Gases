import HRS.MS.R26T8AP11f23
import HRS.MS.R26T8AP11f2

/-!
# S8.2 T8A P11f: `r26t8a_nonlocal_outer` (Pro contract, verbatim)
`oneJ(Q(·,y))(x) - localRiesz (criticalS d) chi (divSource ρ Q) x y` is `Conormal k 0 (M+2) 0 (C A)`.
Proof (no use of P11e): by P10a `oneJ = ∫ g(x-u) S(u,y) du`; with `1 = θ1 + ψ0`, `chi = θ1 chi + ψ0` in the source variable the
difference is `PF - chi(x-y) PC + (1-chi(x-y)) T2` (`r26t8a_f22_D_eq`), a globally `C^k` function with joint jets `≤ B Cρ A jb(y)^M`
(`r26t8a_f21_model_jets`), hence `Conormal` (`r26t8a_conormal_of_smooth`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 800000 in
theorem r26t8a_nonlocal_outer (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ Q : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal (k + 2) b M (sigma - 2) A Q →
        Conormal k 0 (M + 2) 0 (C * A) (fun x y =>
          oneJ (critCoeff d a beta rho) (fun u => Q u y) x -
          r26t8a_localRiesz (criticalS d) chi (r26t8a_divSource rho Q) x y) := by
  classical
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta ρ0
  swap
  · exact ⟨0, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩
  obtain ⟨ρ0, h0⟩ := hex
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hρs, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith)
    ha hbeta h0
  obtain ⟨Cρ, cρ, hCρ, hcρ, hρb⟩ := r26t8a_f23_rho_unif hg (k + 1)
  obtain ⟨B, hB0, hB⟩ := r26t8a_f21_model_jets hchi hd k b M (sigma - 2) cρ hM hcρ (by linarith)
  refine ⟨2 ^ k * (B * Cρ), by positivity, ?_⟩
  intro rho hrho Q A hA hQ
  have hρeq : rho = ρ0 :=
    (critical_thermal_eq d hd a beta ha hbeta hrho).trans (critical_thermal_eq d hd a beta ha hbeta h0).symm
  subst hρeq
  obtain ⟨hmc, hmj⟩ := hB A hA hQ hρs hCρ hρb
  set Fm : Euc d → Euc d → ℝ := fun x y => r26t8a_f20_model chi ((d : ℝ) / 2) ((d : ℝ) / 2) rho Q (x, y) with hFm
  have hunc : Function.uncurry Fm = r26t8a_f20_model chi ((d : ℝ) / 2) ((d : ℝ) / 2) rho Q := rfl
  have hCon : Conormal k 0 M 0 (2 ^ k * (B * Cρ * A)) Fm := by
    refine r26t8a_conormal_of_smooth (by positivity) (by rw [hunc]; exact hmc) fun j hj x y => ?_
    rw [hunc]
    refine (hmj j hj (x, y)).trans ?_
    have hjx : 1 ≤ jbracket x ^ M := Real.one_le_rpow (s83_one_le_jb x) hM
    have hjy : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s83_jb_pos y).le _
    have hX : 0 ≤ B * Cρ * A := by positivity
    show B * Cρ * A * jbracket y ^ M ≤ B * Cρ * A * (jbracket x ^ M * jbracket y ^ M)
    nlinarith [mul_le_mul_of_nonneg_right hjx hjy]
  have hker : ∀ w : Euc d, rieszKernel d (criticalS d) w = ‖w‖ ^ (-((d : ℝ) / 2)) := by
    intro w
    have hs : criticalS d ≠ 0 := by unfold criticalS; positivity
    rw [rieszKernel, if_neg hs]; rfl
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p | p.1 ≠ p.2} :=
    hQ.1.of_le (by exact_mod_cast (by omega : 2 ≤ k + 2))
  have hcongr : ∀ x y : Euc d, x ≠ y → Fm x y =
      oneJ (critCoeff d a beta rho) (fun u => Q u y) x -
        r26t8a_localRiesz (criticalS d) chi (r26t8a_divSource rho Q) x y := by
    intro x y hxy
    obtain ⟨hint', hid⟩ := r26t8a_conormal_potential_ibp d hd k b a beta M sigma ha hbeta hM hsd rho hrho Q A hA
      hQ x y hxy
    simp only [hker] at hint' hid
    rw [hid]
    exact (r26t8a_f22_D_eq hchi hd hQ2 hρs hxy hint').symm
  have hCon' := r26t8a_conormal_congr (g := fun x y => oneJ (critCoeff d a beta rho) (fun u => Q u y) x -
      r26t8a_localRiesz (criticalS d) chi (r26t8a_divSource rho Q) x y) hcongr hCon
  have hM2 := r26t8a_f23_conormal_M_mono (M' := M + 2) (by linarith) (by positivity) hCon'
  have e : 2 ^ k * (B * Cρ) * A = 2 ^ k * (B * Cρ * A) := by ring
  rw [e]
  exact hM2

end HRS.MS.R26T8A
