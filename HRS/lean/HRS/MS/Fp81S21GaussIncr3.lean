import HRS.MS.Fp81S21GaussIncr2
import HRS.MS.Fp81S21WindowFeature5
import HRS.MS.S104gJc2
import HRS.MS.MovDecAux3

/-!
# HRS S2.1(iii), SOL71: terminal-time Lipschitz control of the gradient

The scalar terminal derivative is not used as a substitute for differentiating
the gradient.  Instead, the S101 jet data and terminal difference quotients are
fed to `s104g_lipT`, which proves the required C1-valued estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.CovMeas HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

private theorem fp81s21_gauss_incr_gradient_lipschitz_on_horizon
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hH : 0 < H)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {c : MultiIndex p.d → ℝ}
    (hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      H (2 * p.d + 8) c)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) H) (huH : u < H)
    (α : MultiIndex p.d) :
    ∀ s ∈ Icc u H, ∀ t ∈ Icc u H, ∀ x : Euc p.d,
      ‖gradient (propagatorW (r26t3_coeff R) u t
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x -
        gradient (propagatorW (r26t3_coeff R) u s
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ≤
        c α * |t - s| := by
  classical
  let C : WholeCoeff p.d := r26t3_coeff R
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let U1 : ℝ → ℝ → Euc p.d → ℝ := fun t r =>
    if r = u then propagatorW C u t φ else 0
  let U2 : ℝ → ℝ → Euc p.d → ℝ := fun t r =>
    if r = u then propagatorW C u t (generatorW C t φ) else 0
  have horb : S104nOrbit C φ H :=
    s104b_orbit_of_termRegGen hterm R.admissible R.resulting α H hH.le
  have horder : 2 ≤ 2 * p.d + 8 + 1 := by
    have := p.hd
    omega
  have hEq := fp81s21_window_s101Dt_eq_generator p R hH
    (by norm_num : 0 ≤ (0 : ℝ)) (by simpa using hu)
    (by simpa using huH) hterm
  have hsm1 : ∀ t ∈ Icc (0 : ℝ) H, ∀ r ∈ Icc (0 : ℝ) t,
      ContDiff ℝ 2 (U1 t r) := by
    intro t ht r hr
    by_cases hru : r = u
    · subst r
      have htt : t ∈ Icc u H := ⟨hr.2, ht.2⟩
      simpa [U1] using (hD.smoothU α u hu t htt).of_le
        (by exact_mod_cast horder)
    · simpa [U1, hru, Pi.zero_def] using
        (contDiff_const : ContDiff ℝ 2 (fun _ : Euc p.d => (0 : ℝ)))
  have hsm2 : ∀ t ∈ Icc (0 : ℝ) H, ∀ r ∈ Icc (0 : ℝ) t,
      ContDiff ℝ 1 (U2 t r) := by
    intro t ht r hr
    by_cases hru : r = u
    · subst r
      have htt : t ∈ Icc u H := ⟨hr.2, ht.2⟩
      have hderFun : (fun x => s101Dt C (wholeSpaceIndex p.d : ℝ)
          H u t α x) = propagatorW C u t (generatorW C t φ) := by
        funext x
        simpa [C, φ] using hEq t (by simpa using htt) α x
      have hcont : ContDiff ℝ 2 (fun x => s101Dt C
          (wholeSpaceIndex p.d : ℝ) H u t α x) :=
        (hD.smoothD α u hu t htt).of_le (by exact_mod_cast horder)
      have hcont1 : ContDiff ℝ 1 (fun x => s101Dt C
          (wholeSpaceIndex p.d : ℝ) H u t α x) := hcont.of_le (by norm_num)
      rw [hderFun] at hcont1
      simpa [U2, C, φ] using hcont1
    · simpa [U2, hru, Pi.zero_def] using
        (contDiff_const : ContDiff ℝ 1 (fun _ : Euc p.d => (0 : ℝ)))
  have hdq : ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ H → ∀ e : ℝ, 0 < e →
      ∃ η : ℝ, 0 < η ∧
        ∀ h : ℝ, h ≠ 0 → |h| < η → r ≤ t + h → t + h ≤ H →
          ∀ x : Euc p.d,
            ‖iteratedFDeriv ℝ 1
              (fun y => h⁻¹ * (U1 (t + h) r y - U1 t r y) - U2 t r y) x‖ ≤ e := by
    intro r t hr hrt ht e he
    by_cases hru : r = u
    · subst r
      have hτ : t - u ∈ Icc (0 : ℝ) (H - u) := by
        constructor <;> linarith
      obtain ⟨η, hη, hq⟩ := horb.diff01 u hu (t - u) hτ e he
      refine ⟨η, hη, fun h hne hlt hrt' ht' x => ?_⟩
      have hτh : (t - u) + h ∈ Icc (0 : ℝ) (H - u) := by
        constructor <;> linarith
      have hq' := hq h hne hlt hτh 1 (by norm_num) x
      have hshift0 : u + (t - u) = t := by ring
      have hshift1 : u + ((t - u) + h) = t + h := by ring
      simpa [U1, U2, hshift0, hshift1, C, φ] using hq'
    · refine ⟨1, by norm_num, fun h hne hlt hrt' ht' x => ?_⟩
      simpa [U1, U2, hru] using le_of_lt he
  have hb : ∀ t ∈ Icc (0 : ℝ) H, ∀ r ∈ Icc (0 : ℝ) t,
      ∀ x : Euc p.d, ‖gradient (U2 t r) x‖ ≤ c α := by
    intro t ht r hr x
    by_cases hru : r = u
    · subst r
      have htt : t ∈ Icc u H := ⟨hr.2, ht.2⟩
      have hderFun : (fun y => s101Dt C (wholeSpaceIndex p.d : ℝ)
          H u t α y) = propagatorW C u t (generatorW C t φ) := by
        funext y
        simpa [C, φ] using hEq t (by simpa using htt) α y
      have hbd := hD.bddD α u hu t htt 1 (by omega) x
      simp only [U2, if_pos rfl]
      rw [← hderFun]
      rw [HRS.MS.MovDec.mov2e_norm_gradient, ← norm_iteratedFDeriv_one]
      simpa using hbd
    · have hgrad0 : gradient (0 : Euc p.d → ℝ) x = 0 := by simp [gradient]
      simpa [U2, hru, hgrad0] using hD.nonneg α
  have hLip := HRS.MS.R2WinOrbNL.s104g_lipT hsm1 hsm2 hdq
    (Gb := c α) hb
  intro s hs t ht x
  have ht0 : t ∈ Icc (0 : ℝ) H := ⟨hu.1.trans ht.1, ht.2⟩
  have hs0 : s ∈ Icc (0 : ℝ) H := ⟨hu.1.trans hs.1, hs.2⟩
  have hresult := hLip t ht0 s hs0 u hu.1 ht.1 hs.1 x
  simpa [U1, U2, C, φ] using hresult

/-- The gradient of `U^{r,t} ψα` is Lipschitz in terminal time with a
trajectory-dependent mode envelope, uniformly over every start time. -/
theorem fp81s21_gauss_incr_gradient_terminal_lipschitz (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ g' : ℝ, 0 ≤ g' ∧
          ∀ r s t : ℝ, 0 ≤ r → r ≤ s → r ≤ t →
            ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
              ‖gradient (propagatorW (r26t3_coeff R) r t
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x -
                gradient (propagatorW (r26t3_coeff R) r s
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖ ≤
                g' * s104_b p.d α * |t - s| := by
  obtain ⟨δu, hδu, hδuhalf, huniform⟩ :=
    fp81s21_uniform_orbit_amplitudes p
  obtain ⟨δc, Co, co, hδc, hδchalf, hco, hcommon⟩ :=
    fp81s21_common_radius p
  let δ0 : ℝ := min δu δc
  have hδ0 : 0 < δ0 := lt_min hδu hδc
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδuhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨CoR, coR, hcoR, hsumR, hdata⟩ :=
    huniform δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨hclaims, -, hterm, -⟩ :=
    hcommon δ hδ (hδle.trans (min_le_right _ _)) R.ρβ R.thermal
  let g' : ℝ := (p.d : ℝ) ^ ((2 * p.d + 8) + 1) * |CoR|
  have hg' : 0 ≤ g' := by dsimp [g']; positivity
  have hcoef : ∀ α : MultiIndex p.d,
      fp81s21_uniform_orbit_coefficient p CoR α = g' * s104_b p.d α := by
    intro α
    simp [fp81s21_uniform_orbit_coefficient, g',
      HRS.MS.R2WinOrb.s103_b, HRS.MS.R2WinErr.s104_b]
    ring
  refine ⟨g', hg', ?_⟩
  intro r s t hr hrs hrt α x
  let H : ℝ := max s t + 1
  have hs0 : 0 ≤ s := hr.trans hrs
  have ht0 : 0 ≤ t := hr.trans hrt
  have hmax0 : 0 ≤ max s t := le_max_of_le_left hs0
  have hH : 0 < H := by dsimp [H]; linarith
  have hmaxLt : max s t < H := by dsimp [H]; linarith
  have hrH : r ∈ Icc (0 : ℝ) H := by
    constructor
    · exact hr
    · exact le_of_lt (lt_of_le_of_lt (le_max_of_le_left hrs) hmaxLt)
  have hsH : s ∈ Icc r H := by
    constructor
    · exact hrs
    · exact le_of_lt (lt_of_le_of_lt (le_max_left s t) hmaxLt)
  have htH : t ∈ Icc r H := by
    constructor
    · exact hrt
    · exact le_of_lt (lt_of_le_of_lt (le_max_right s t) hmaxLt)
  have hD := hdata H hH
  have hLip := fp81s21_gauss_incr_gradient_lipschitz_on_horizon
    p R hH hterm hD hrH (lt_of_le_of_lt (le_max_of_le_left hrs) hmaxLt)
    α s hsH t htH x
  calc
    ‖gradient (propagatorW (r26t3_coeff R) r t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x -
      gradient (propagatorW (r26t3_coeff R) r s
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x‖
      ≤ fp81s21_uniform_orbit_coefficient p CoR α * |t - s| := hLip
    _ = g' * s104_b p.d α * |t - s| := by rw [hcoef α]

#print axioms fp81s21_gauss_incr_gradient_terminal_lipschitz

end HRS.Fp81.S21

end
