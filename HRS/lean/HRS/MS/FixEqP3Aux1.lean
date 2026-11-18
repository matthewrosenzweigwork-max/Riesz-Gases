import HRS.MS.FixEqP2Aux9

/-!
# S5.7 `fixed_equation` (worker S57P), part 13: high-order bounds of the generator of `fixedEqCoeff` on the Hermite features

`s57p_gen_hi`: for `φ ∈ C^{R+3}` (bounded jets `B`, and `(1+|x|)`-weighted jets `B1` through order `R+1`) the function
`𝓛_τ φ` of `fixedEqCoeff` is a bounded `C^R` class: `RgW 1 R (K_B B + K_1 B_1)`.
`s57p_gen_ul`: `‖𝓛_τ φ_α‖_{H^R_ul} ≤ C_g λ_α^{(J-m)/2}` for the Hermite features `φ_α = oscTestFun m α`.
Both are the analogue for `fixedEqCoeff` of `s55f_gen_core`, `s55f_gen_ul` (which are stated for `WholeSetup` coefficients).
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the linear transport `x ↦ -(Qx)_j` as a weighted class of any order -/
theorem s57p_RgW_linearR (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) (R : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ RgW (fun x : Euc d => 1 + ‖x‖) R K (fun x => -(Torus.matVec Q x) j) := by
  let L : Euc d →L[ℝ] ℝ := -((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp
    (Matrix.toEuclideanLin Q).toContinuousLinearMap)
  have hL : ∀ x, -(Torus.matVec Q x) j = L x := fun x => by simp [L, Torus.matVec]
  have e : (fun x => -(Torus.matVec Q x) j) = fun x => L x := funext hL
  refine ⟨‖L‖, norm_nonneg _, ?_⟩
  rw [e]
  refine ⟨L.contDiff, fun n hn x => ?_⟩
  have hw : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · rw [norm_iteratedFDeriv_zero]
      calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
        _ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    · rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
      calc ‖L‖ = ‖L‖ * 1 := (mul_one _).symm
        _ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  · obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
    have h1 : ‖iteratedFDeriv ℝ (n' + 1 + 1) (fun x => L x) x‖ = 0 := by
      rw [← norm_iteratedFDeriv_fderiv]
      have : (fderiv ℝ (fun x => L x)) = fun _ => L := by funext y; exact L.fderiv
      rw [this, iteratedFDeriv_const_of_ne (by omega)]
      simp
    rw [show n' + 2 = n' + 1 + 1 by ring, h1]
    positivity

/-- a `C^k` bounded vector field as a weighted class of order `k` -/
theorem s57p_c_RgWk {k : ℕ} {Λc : ℝ} {g : Euc d → Euc d} (hg : ContDiff ℝ k g)
    (hb : ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ Λc) (j : Fin d) :
    RgW (fun x : Euc d => 1 + ‖x‖) k Λc (fun x => g x j) := by
  have hΛ : 0 ≤ Λc := le_trans (norm_nonneg _) (hb 0 (Nat.zero_le _) 0)
  let P : Euc d →L[ℝ] ℝ := EuclideanSpace.proj j
  have hP : ‖P‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    simpa [P] using PiLp.norm_apply_le y j
  have e : (fun x => g x j) = fun x => P (g x) := rfl
  rw [e]
  refine ⟨P.contDiff.comp hg, fun n hn x => ?_⟩
  have := P.norm_iteratedFDeriv_comp_left (f := g) (x := x) (n := n) (N := (k : ℕ)) hg.contDiffAt
    (by exact_mod_cast hn)
  have hw : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  calc ‖iteratedFDeriv ℝ n (fun x => P (g x)) x‖ ≤ ‖P‖ * ‖iteratedFDeriv ℝ n g x‖ := this
    _ ≤ 1 * Λc := mul_le_mul hP (hb n hn x) (norm_nonneg _) zero_le_one
    _ ≤ Λc * (1 + ‖x‖) := by nlinarith

/-- **Bounded generator estimate for `fixedEqCoeff`**. -/
theorem s57p_gen_hi (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M Q : Matrix (Fin d) (Fin d) ℝ)
    (R : ℕ) {A Λc νbar : ℝ} (hA : 0 ≤ A) (hΛc : 0 ≤ Λc) (hνbar : 0 ≤ νbar) :
    ∃ KB K1 : ℝ, 0 ≤ KB ∧ 0 ≤ K1 ∧ ∀ {ν : ℝ}, |ν| ≤ νbar → ∀ {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {τ : ℝ},
      RgDecay (R + 2) (fun _ => A) (ρ τ) → ContDiff ℝ R (c τ) → (∀ i ≤ R, ∀ x, ‖iteratedFDeriv ℝ i (c τ) x‖ ≤ Λc) →
      ∀ {B B1 : ℝ}, 0 ≤ B → 0 ≤ B1 → ∀ {φ : Euc d → ℝ}, ContDiff ℝ ((R + 2 + 1 : ℕ) : WithTop ℕ∞) φ →
      (∀ n, n ≤ R + 2 + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ ≤ B) →
      (∀ n, n ≤ R + 1 → ∀ x, ‖iteratedFDeriv ℝ n φ x‖ * (1 + ‖x‖) ≤ B1) →
      RgW (fun _ => (1 : ℝ)) R (KB * B + K1 * B1) (generatorW (fixedEqCoeff s M Q ν c ρ) τ φ) := by
  choose Kj hKj0 hKj using fun j : Fin d => s57p_RgW_linearR Q j R
  set Bb : ℝ := ∑ j, Kj j + Λc with hBb
  have hBb0 : 0 ≤ Bb := add_nonneg (Finset.sum_nonneg fun j _ => hKj0 j) hΛc
  have hMB := s55f_matBound M
  set MB : ℝ := ∑ i, ∑ j, |M i j| with hMBdef
  have hMB0 : 0 ≤ MB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hσ : 0 ≤ movtr_sigma s := rg_sigma_nonneg hs0
  have hnear := rg_near_nonneg (d := d) s
  have hW := rg_W_nonneg (d := d)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set Kn : ℝ := d * (movtr_sigma s * ((2 ^ (R + 2) * A * ((d : ℝ) * MB)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (R + 2) * A * ((d : ℝ) * MB)) * rgW d)) with hKn
  have hKn0 : 0 ≤ Kn := by rw [hKn]; positivity
  refine ⟨νbar * d + Kn, d * (2 ^ R * Bb), by positivity, by positivity, ?_⟩
  intro ν hν c ρ τ hρ hc hcb B B1 hB hB1 φ hφ hBφ hB1φ
  have hφ2 : ContDiff ℝ ((R + 2 : ℕ) : WithTop ℕ∞) φ := hφ.of_le (by exact_mod_cast Nat.le_succ _)
  have hφ1 : ContDiff ℝ ((R + 1 : ℕ) : WithTop ℕ∞) φ :=
    hφ.of_le (by exact_mod_cast (by omega : R + 1 ≤ R + 2 + 1))
  have hφR : ContDiff ℝ (R : WithTop ℕ∞) φ := hφ.of_le (by exact_mod_cast (by omega : R ≤ R + 2 + 1))
  have hLap := rg_laplacian (k := R) hφ2 (fun n hn x => hBφ n (by omega) x)
  have hg1 : RgW (fun _ => (1 : ℝ)) R (|ν| * (d * B)) (fun x => ν * Laplacian.laplacian φ x) :=
    hLap.const_mul _
  have hb : ∀ j : Fin d, RgW (fun x : Euc d => 1 + ‖x‖) R Bb
      (fun x => (-(Torus.matVec Q x) + c τ x) j) := by
    intro j
    have h3 := RgW.add (hKj j) (s57p_c_RgWk hc hcb j)
    refine (h3.mono (fun x => by positivity) ?_)
    rw [hBb]
    have : Kj j ≤ ∑ j, Kj j := Finset.single_le_sum (f := Kj) (fun j _ => hKj0 j) (Finset.mem_univ j)
    linarith
  have hgrad : ∀ j : Fin d, RgW (fun _ => (1 : ℝ)) R B (fun x => gradient φ x j) := fun j =>
    rg_grad_comp hφ1 (fun n hn x => hBφ n (by omega) x) j
  have hg2j : ∀ j ∈ (Finset.univ : Finset (Fin d)),
      RgW (fun _ => (1 : ℝ)) R (2 ^ R * Bb * B1)
        (fun x => (-(Torus.matVec Q x) + c τ x) j * gradient φ x j) := by
    intro j _
    refine s55f_mul_lin hBb0 hB1 (hb j) (hgrad j).1 ?_
    intro n hn x
    have e : (fun x => gradient φ x j) = fun x => fderiv ℝ φ x (EuclideanSpace.single j (1 : ℝ)) := by
      funext y; exact movtr_gradient_apply φ y j
    rw [e]
    have h1 := rg_diruv (n := n) (φ := φ) (hφ.of_le (by exact_mod_cast (by omega : n + 1 ≤ R + 2 + 1)))
      (EuclideanSpace.single j 1) x
    rw [rg_norm_single, one_mul] at h1
    exact (mul_le_mul_of_nonneg_right h1 (by positivity)).trans (hB1φ (n + 1) (by omega) x)
  have hg2 := RgW.sum (w := fun _ : Euc d => (1 : ℝ)) (k := R) Finset.univ hg2j
  have hBg : 0 ≤ (d : ℝ) * MB * B := by positivity
  have hg4 := rg_T3 hd hs0 hsd (k := R) hA hBg hρ
    (g := fun j y => Torus.matVec M.transpose (gradient φ y) j)
    (fun j => rg_matgrad hMB hφ hBφ j)
  have hfun : generatorW (fixedEqCoeff s M Q ν c ρ) τ φ = fun x =>
      (ν * Laplacian.laplacian φ x + ∑ j : Fin d, (-(Torus.matVec Q x) + c τ x) j * gradient φ x j) -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
          (fun y => ρ τ y * (Torus.matVec M.transpose (gradient φ y)) j) x) j := by
    funext x
    have h : generatorW (fixedEqCoeff s M Q ν c ρ) τ φ x =
        (ν * Laplacian.laplacian φ x + inner ℝ (-(Torus.matVec Q x) + c τ x) (gradient φ x)) -
          ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
            (fun y => ρ τ y * (Torus.matVec M.transpose (gradient φ y)) j) x) j := rfl
    rw [h, HRS.Whole.Q09B.q09b_inner_euc]
  rw [hfun]
  have hmain := (hg1.add hg2).sub hg4
  refine hmain.mono (fun _ => zero_le_one) ?_
  have h1 : |ν| * (d * B) ≤ νbar * (d * B) :=
    mul_le_mul_of_nonneg_right hν (by positivity)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have e : (d : ℝ) * (movtr_sigma s * ((2 ^ (R + 2) * A * ((d : ℝ) * MB * B)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (R + 2) * A * ((d : ℝ) * MB * B)) * rgW d)) =
      B * (d * (movtr_sigma s * ((2 ^ (R + 2) * A * ((d : ℝ) * MB)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (R + 2) * A * ((d : ℝ) * MB)) * rgW d))) := by ring
  rw [hKn]
  nlinarith [e, h1]

/-- **`‖𝓛_τ φ_α‖_{H^R_ul} ≤ C_g λ_α^{(J-m)/2}`** for the Hermite features. -/
theorem s57p_gen_ul {θ : Euc d → ℝ} (hθ : IsUlCutoff θ) (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M Q : Matrix (Fin d) (Fin d) ℝ) (m : ℝ) (J R : ℕ) (hJ : 3 * R + 9 ≤ J) {A Λc νbar : ℝ} (hA : 0 ≤ A)
    (hΛc : 0 ≤ Λc) (hνbar : 0 ≤ νbar) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ {ν : ℝ}, |ν| ≤ νbar → ∀ {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {τ : ℝ},
      RgDecay (R + 2) (fun _ => A) (ρ τ) → ContDiff ℝ R (c τ) → (∀ i ≤ R, ∀ x, ‖iteratedFDeriv ℝ i (c τ) x‖ ≤ Λc) →
      ∀ α : MultiIndex d, ContDiff ℝ (R : WithTop ℕ∞) (generatorW (fixedEqCoeff s M Q ν c ρ) τ (oscTestFun m α)) ∧
        ulNormE R θ (generatorW (fixedEqCoeff s M Q ν c ρ) τ (oscTestFun m α)) ≤
          ENNReal.ofReal (Cg * oscEigenvalue d α ^ (((J : ℝ) - m) / 2)) := by
  obtain ⟨KB, K1, hKB0, hK10, hK⟩ := s57p_gen_hi hd hs0 hsd M Q R hA hΛc hνbar
  have hceil2 : ⌈(1 + (((R + 3 : ℕ) : ℝ))) / 2⌉₊ ≤ R + 3 := by
    rw [Nat.ceil_le]; push_cast
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    linarith
  obtain ⟨C0, hC0, hosc⟩ := s55_osc_bounds hθ m R (R + 3) 1 (by norm_num) J (by omega) (by omega)
  obtain ⟨Cu, hCu0, hCu⟩ := s55_ul_of_sup hθ R
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨Cu * (KB * (d : ℝ) ^ (R + 3) + K1 * (2 * (d : ℝ) ^ (R + 3))) * C0, by positivity, ?_⟩
  intro ν hν c ρ τ hρ hc hcb α
  obtain ⟨hsm, -, hdec⟩ := hosc α
  set e : ℝ := (((J : ℝ) - m) / 2) with he
  set Λφ : ℝ := C0 * oscEigenvalue d α ^ e with hΛφ
  have hΛφ0 : 0 ≤ Λφ := mul_nonneg hC0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hφR : ContDiff ℝ ((R + 3 : ℕ) : WithTop ℕ∞) (oscTestFun m α) := s55_cd_of_inf (R + 3) hsm
  have hnorm := s55f_decay_to_norm hφR hdec
  rw [max_eq_left hΛφ0] at hnorm
  set B : ℝ := (d : ℝ) ^ (R + 3) * Λφ with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hpow : ∀ n ≤ R + 3, (d : ℝ) ^ n ≤ (d : ℝ) ^ (R + 3) := fun n hn => pow_le_pow_right₀ hd1' hn
  have hBφ : ∀ n, n ≤ R + 2 + 1 → ∀ x, ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ ≤ B := by
    intro n hn x
    exact ((hnorm n (by omega) x).1).trans (mul_le_mul_of_nonneg_right (hpow n (by omega)) hΛφ0)
  have hB1φ : ∀ n, n ≤ R + 1 → ∀ x, ‖iteratedFDeriv ℝ n (oscTestFun m α) x‖ * (1 + ‖x‖) ≤ 2 * B := by
    intro n hn x
    exact ((hnorm n (by omega) x).2).trans (by
      have := mul_le_mul_of_nonneg_right (hpow n (by omega)) hΛφ0
      linarith)
  have hcore := hK hν hρ hc hcb hB0 (by positivity : (0 : ℝ) ≤ 2 * B)
    (s55_cd_of_inf (R + 2 + 1) hsm) hBφ hB1φ
  refine ⟨hcore.1, ?_⟩
  have hK0 : 0 ≤ KB * B + K1 * (2 * B) := by positivity
  have hul := hCu _ (KB * B + K1 * (2 * B)) hK0 hcore.1 (fun l hl idx x => by
    have h1 := s55f_partial_le_norm idx (generatorW (fixedEqCoeff s M Q ν c ρ) τ (oscTestFun m α)) x
    have h2 := hcore.2 l hl x
    simp only [mul_one] at h2
    exact h1.trans h2)
  refine hul.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [hBdef, hΛφ]
  ring

end HRS.MS.FixEq
