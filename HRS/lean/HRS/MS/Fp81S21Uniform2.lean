import HRS.MS.Fp81S21Uniform
import HRS.MS.Fp81S21MovingStd3

/-!
# HRS S2.1(iii), SOL26 packet 5: a horizon-independent orbit coefficient family

The moving orbit producer has one all-time amplitude `Co * s103_b`. This file turns that
amplitude into a single square-summable `S101Data` coefficient family that works on every
finite horizon.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.CovMeas
open HRS.MS.R2WinOrb HRS.MS.R2WinOrbNL HRS.MS.R2WinErr

/-- The horizon-independent coefficient envelope extracted from the all-time moving orbit bound. -/
def fp81s21_uniform_orbit_coefficient (p : Parameters) (Co : ℝ)
    (α : MultiIndex p.d) : ℝ :=
  (p.d : ℝ) ^ ((2 * p.d + 8) + 1) * (|Co| * s103_b p.d α)

private theorem fp81s21_uniform_s101data_at
    (p : Parameters) {δ H Co co : ℝ} (R : Trajectory p δ)
    (hH : 0 < H)
    (hclaims : S103nOrbitClaims p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁) :
    S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8)
      (fp81s21_uniform_orbit_coefficient p Co) := by
  obtain ⟨cH, hDH⟩ := fp81s21_moving_s101data_of_common p R hH hclaims hterm
  let C : WholeCoeff p.d := r26t3_coeff R
  let K : ℕ := 4 * p.d + 42
  let r : ℕ := 2 * p.d + 8
  let φ : MultiIndex p.d → Euc p.d → ℝ :=
    fun α => oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let A : MultiIndex p.d → ℝ := fun α => |Co| * s103_b p.d α
  let c : MultiIndex p.d → ℝ := fp81s21_uniform_orbit_coefficient p Co
  have hrK : r + 1 ≤ K := by dsimp [r, K]; omega
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hA : ∀ α, 0 ≤ A α := by
    intro α
    exact mul_nonneg (abs_nonneg _) (s103_b_nonneg α)
  have hsup0 : ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup C K t (φ α) (A α) := by
    intro α t ht
    have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
    have hmono : Co * s103_b p.d α ≤ A α :=
      mul_le_mul_of_nonneg_right (le_abs_self Co) (s103_b_nonneg α)
    exact HRS.MS.R2WinOrb.s103_orbitSup_mono hraw.1 hmono
  have hsup1 : ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup C K t (generatorW C t (φ α)) (A α) := by
    intro α t ht
    have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
    have hmono : Co * s103_b p.d α ≤ A α :=
      mul_le_mul_of_nonneg_right (le_abs_self Co) (s103_b_nonneg α)
    exact HRS.MS.R2WinOrb.s103_orbitSup_mono hraw.2.2.1 hmono
  have horb : ∀ α : MultiIndex p.d, S104nOrbit C (φ α) H := by
    intro α
    exact s104b_orbit_of_termRegGen hterm R.admissible R.resulting α H hH.le
  have hU : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
      ContDiff ℝ K (propagatorW C v t (φ α)) ∧
      r2CbNormE K (propagatorW C v t (φ α)) ≤ ENNReal.ofReal (A α) := by
    intro α v hv t ht
    have htH : t ∈ Icc (0 : ℝ) H := ⟨hv.1.trans ht.1, ht.2⟩
    obtain ⟨f, hf⟩ := (horb α).ex0 t htH
    have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
    exact hsup0 α t htH.1 (fun z => propagatorW C z t (φ α)) hcanonical v
      ⟨hv.1, ht.1⟩
  have hG : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
      ContDiff ℝ K (propagatorW C v t (generatorW C t (φ α))) ∧
      r2CbNormE K (propagatorW C v t (generatorW C t (φ α))) ≤ ENNReal.ofReal (A α) := by
    intro α v hv t ht
    have htH : t ∈ Icc (0 : ℝ) H := ⟨hv.1.trans ht.1, ht.2⟩
    obtain ⟨f, hf⟩ := (horb α).ex1 t htH
    have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
    exact hsup1 α t htH.1
      (fun z => propagatorW C z t (generatorW C t (φ α))) hcanonical v
      ⟨hv.1, ht.1⟩
  have hder : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H, ∀ x,
      HasDerivWithinAt (fun z => propagatorW C v z (φ α) x)
        (propagatorW C v t (generatorW C t (φ α)) x) (Icc v H) t := by
    intro α v hv t ht x
    let Fa : ℝ → Euc p.d → ℝ := fun τ => propagatorW C v (v + τ) (φ α)
    let Fb : ℝ → Euc p.d → ℝ := fun τ =>
      propagatorW C v (v + τ) (generatorW C (v + τ) (φ α))
    have hvT : v ∈ Icc (0 : ℝ) H := hv
    have hτ : t - v ∈ Icc (0 : ℝ) (H - v) := by
      constructor <;> linarith [ht.1, ht.2]
    have hcdA : ∀ τ ∈ Icc (0 : ℝ) (H - v),
        ContDiff ℝ (0 : WithTop ℕ∞) (Fa τ) := by
      intro τ hτ'
      have hz : v + τ ∈ Icc (0 : ℝ) H := by
        constructor <;> linarith [hv.1, hτ'.1, hτ'.2]
      exact (hU α v hv (v + τ) ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩).1.of_le
        (by norm_num)
    have hcdB : ∀ τ ∈ Icc (0 : ℝ) (H - v),
        ContDiff ℝ (0 : WithTop ℕ∞) (Fb τ) := by
      intro τ hτ'
      have hz : v + τ ∈ Icc (0 : ℝ) H := by
        constructor <;> linarith [hv.1, hτ'.1, hτ'.2]
      exact (hG α v hv (v + τ) ⟨by linarith [hτ'.1], by linarith [hτ'.2]⟩).1.of_le
        (by norm_num)
    have hdiff : ∀ τ ∈ Icc (0 : ℝ) (H - v), ∀ ε : ℝ, 0 < ε →
        ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, h ≠ 0 → |h| < η →
          τ + h ∈ Icc (0 : ℝ) (H - v) → ∀ y : Euc p.d,
            ‖iteratedFDeriv ℝ 0
              (fun z => h⁻¹ * (Fa (τ + h) z - Fa τ z) - Fb τ z) y‖ ≤ ε := by
      intro τ hτ' ε hε
      obtain ⟨η, hη, hq⟩ := (horb α).diff01 v hvT τ hτ' ε hε
      refine ⟨η, hη, fun h hne hlt hτh y => ?_⟩
      exact hq h hne hlt hτh 0 (by norm_num) y
    have hderτ := HRS.MS.R2WinOrb.s103_hasDeriv_val hcdA hcdB hdiff x
      (t - v) hτ
    have hshift : HasDerivWithinAt (fun z : ℝ => z - v) 1 (Icc v H) t :=
      ((hasDerivAt_id t).sub_const v).hasDerivWithinAt
    have hmaps : MapsTo (fun z : ℝ => z - v) (Icc v H) (Icc (0 : ℝ) (H - v)) := by
      intro z hz
      constructor <;> linarith [hz.1, hz.2]
    have hcomp := hderτ.comp t hshift hmaps
    have hcomp' : HasDerivWithinAt (fun z => Fa (z - v) x)
        (Fb (t - v) x) (Icc v H) t := by
      simpa [Function.comp_def] using hcomp
    have heq : ∀ z ∈ Icc v H, Fa (z - v) x = propagatorW C v z (φ α) x := by
      intro z hz
      dsimp [Fa]
      congr 1
      ring
    have heq' : ∀ z ∈ Icc v H, propagatorW C v z (φ α) x = Fa (z - v) x := by
      intro z hz
      exact (heq z hz).symm
    have hactual := hcomp'.congr_of_mem heq' ht
    have htarget : Fb (t - v) x = propagatorW C v t (generatorW C t (φ α)) x := by
      dsimp [Fb]
      congr 2 <;> ring
    exact hactual.congr_deriv htarget
  have hEqDeriv : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H, v < H →
      (fun x => derivWithin (fun z => propagatorW C v z (φ α) x) (Icc v H) t) =
        propagatorW C v t (generatorW C t (φ α)) := by
    intro α v hv t ht hvH
    funext x
    exact (hder α v hv t ht x).derivWithin (uniqueDiffOn_Icc hvH t ht)
  have hEqZero : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H, v = H → t = H →
      (fun x => derivWithin (fun z => propagatorW C v z (φ α) x) (Icc v H) t) =
        (fun _ => (0 : ℝ)) := by
    intro α v hv t ht hvH htH
    funext x
    apply derivWithin_zero_of_not_accPt
    rw [hvH, htH, Icc_self, accPt_principal_iff_clusterPt]
    simp [ClusterPt]
  have hDnorm : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H,
      r2CbNormE K
        (fun x => derivWithin (fun z => propagatorW C v z (φ α) x) (Icc v H) t) ≤
        ENNReal.ofReal (A α) := by
    intro α v hv t ht
    by_cases hvH : v < H
    · rw [hEqDeriv α v hv t ht hvH]
      exact (hG α v hv t ht).2
    · have hvEq : v = H := le_antisymm hv.2 (le_of_not_gt hvH)
      have htEq : t = H := le_antisymm ht.2 (hvEq ▸ ht.1)
      rw [hEqZero α v hv t ht hvEq htEq]
      simp [r2CbNormE]
  have hsq := HRS.MS.ProClosureS111.stationary_weight_square_summable
    (d := p.d) hd1
  have hscale : Summable
      (fun α : MultiIndex p.d =>
        (((p.d : ℝ) ^ (r + 1) * |Co|) ^ 2) * s103_b p.d α ^ 2) :=
    hsq.mul_left (((p.d : ℝ) ^ (r + 1) * |Co|) ^ 2)
  have hsum : Summable (fun α : MultiIndex p.d => c α ^ 2) := by
    convert hscale using 1 <;> ext α <;> simp [c, fp81s21_uniform_orbit_coefficient, r] <;> ring
  refine ⟨?_, hsum, hDH.smoothU, hDH.smoothD, hDH.diffT, ?_, ?_⟩
  · intro α
    dsimp [c, fp81s21_uniform_orbit_coefficient]
    exact mul_nonneg (by positivity) (hA α)
  · intro α u hu t ht j hj x
    have hsup := (hU α u hu t ht).2
    have hwsup :=
      (HRS.MS.ProClosureS111.weightedSup_zero_le_r2CbNormE hrK _).trans hsup
    have hnorm := s101_norm_of_wsup hd1 (hA α) hwsup j hj x
    simpa [c, fp81s21_uniform_orbit_coefficient, r, s101Dt] using hnorm
  · intro α u hu t ht j hj x
    have hsup := hDnorm α u hu t ht
    have hwsup :=
      (HRS.MS.ProClosureS111.weightedSup_zero_le_r2CbNormE hrK _).trans hsup
    have hnorm := s101_norm_of_wsup hd1 (hA α) hwsup j hj x
    simpa [c, fp81s21_uniform_orbit_coefficient, r, s101Dt] using hnorm

/-- One coefficient family works on every horizon. `Co`, the exponential orbit rate `co`,
and `s103_b` are chosen before the trajectory; the derived coefficients have no `H` binder.
For each `H > 0` they form the `S101Data` field required by the moving producer. -/
theorem fp81s21_uniform_orbit_amplitudes (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ (R : Trajectory p δ),
        ∃ Co co : ℝ, 0 < co ∧
          Summable (fun α : MultiIndex p.d =>
            fp81s21_uniform_orbit_coefficient p Co α ^ 2) ∧
          ∀ H : ℝ, 0 < H →
            S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
              (2 * p.d + 8) (fp81s21_uniform_orbit_coefficient p Co) := by
  obtain ⟨δ0, Co, co, hδ0, hδ0Half, hco, hcommon⟩ := fp81s21_common_radius p
  refine ⟨δ0, hδ0, hδ0Half, ?_⟩
  intro δ hδ hδle R
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδle R.ρβ R.thermal
  have hOne := fp81s21_uniform_s101data_at p R (H := 1) one_pos hclaims hterm
  refine ⟨Co, co, hco, hOne.summable, ?_⟩
  intro H hH
  exact fp81s21_uniform_s101data_at p R hH hclaims hterm

#print axioms HRS.Fp81.S21.fp81s21_uniform_orbit_amplitudes

end HRS.Fp81.S21
