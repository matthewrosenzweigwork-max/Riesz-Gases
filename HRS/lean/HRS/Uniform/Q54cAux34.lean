import HRS.Uniform.Q54cAux33

/-!
# Q54c, part 34: `⟨b_{a,j}, lpFun n ψ⟩ = ∂_jψ(a)`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Torus

variable {d : ℕ}

open Classical in
theorem Dmode_rep (k : NonzeroLattice d) (j : Fin d) (a : Torus d) :
    Dmode k j (Torus.rep a) = Torus.partialDeriv j (Torus.realMode k) a := by
  rw [HRS.Uniform.Q14.q14_partialDeriv_realMode]
  unfold Dmode
  by_cases hp : Lattice.IsPosHalf k.1
  · have hs : Real.sin (Torus.freqFunctional k.1 (Torus.rep a)) = Torus.sinMode k.1 a := by
      have h := Torus.sinMode_mk k.1 (Torus.rep a)
      rw [Torus.mk_rep] at h
      rw [h, Torus.freqFunctional_apply]
    simp only [hp, ite_true, hs]
  · have hs : Real.cos (Torus.freqFunctional k.1 (Torus.rep a)) = Torus.cosMode k.1 a := by
      have h := Torus.cosMode_mk k.1 (Torus.rep a)
      rw [Torus.mk_rep] at h
      rw [h, Torus.freqFunctional_apply]
    simp only [hp, ite_false, hs]

theorem partialDeriv_series {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {ψ : Torus d → ℝ} (hψ : MemSobolev n ψ)
    (hc : Continuous ψ) (hψ1 : Torus.IsCk 1 ψ) (j : Fin d) (a : Torus d) :
    HasSum (fun k : NonzeroLattice d => Torus.funRealCoeff ψ k * Torus.partialDeriv j (Torus.realMode k) a)
      (Torus.partialDeriv j ψ a) := by
  set z₀ : Euc d := Torus.rep a with hz₀
  set e : Euc d := EuclideanSpace.single j 1 with he
  set c : NonzeroLattice d → ℝ := fun k => Torus.funRealCoeff ψ k with hcdef
  have hfc : Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖ := by
    have := summable_norm_of_memHs n (by linarith) (coeffOf ψ) (hsNormSq_coeffOf n ψ hψ).1
    simpa [HRS.PDE.coeffOf_eq_fcoef] using this
  have hexp := fun x => Torus.hasSum_realExpansion hc hfc x
  have hu : Summable fun k : NonzeroLattice d => Real.sqrt 2 * (Lattice.jp k.1 * |c k|) :=
    (summable_jp_mul_realCoeff (n := n) (by linarith) hψ).mul_left _
  set g : NonzeroLattice d → ℝ → ℝ := fun k s => c k * Torus.lift (Torus.realMode k) (z₀ + s • e) with hg
  set g' : NonzeroLattice d → ℝ → ℝ := fun k s => c k * Dmode k j (z₀ + s • e) with hg'
  have hgd : ∀ k s, HasDerivAt (g k) (g' k s) s := fun k s =>
    (hasDerivAt_lift_realMode k j z₀ s).const_mul (c k)
  have hbd : ∀ k s, ‖g' k s‖ ≤ Real.sqrt 2 * (Lattice.jp k.1 * |c k|) := by
    intro k s
    rw [Real.norm_eq_abs, hg', abs_mul]
    calc |c k| * |Dmode k j (z₀ + s • e)| ≤ |c k| * (Real.sqrt 2 * Lattice.jp k.1) :=
          mul_le_mul_of_nonneg_left (abs_Dmode_le k j _) (abs_nonneg _)
      _ = _ := by ring
  have hg0 : Summable fun k => g k 0 := by
    have := (hexp (Torus.mk z₀)).summable
    refine this.congr fun k => ?_
    simp [hg, Torus.lift, hcdef]
  have htsum := hasDerivAt_tsum hu hgd hbd hg0 0
  have hfun : (fun s : ℝ => ∑' k, g k s) = fun s => Torus.lift ψ (z₀ + s • e) - Torus.mean ψ := by
    funext s
    have := (hexp (Torus.mk (z₀ + s • e))).tsum_eq
    simpa [hg, Torus.lift, hcdef] using this
  rw [hfun] at htsum
  have hψd : HasFDerivAt (Torus.lift ψ) (fderiv ℝ (Torus.lift ψ) z₀) (z₀ + (0 : ℝ) • e) := by
    have hd : ContDiff ℝ 1 (Torus.lift ψ) := hψ1
    simpa using (hd.differentiable one_ne_zero z₀).hasFDerivAt
  have hline : HasDerivAt (fun s : ℝ => z₀ + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z₀
  have hcomp := (hψd.comp_hasDerivAt (0 : ℝ) hline).sub_const (Torus.mean ψ)
  have huniq := htsum.unique hcomp
  have hsum' : Summable fun k => g' k 0 :=
    Summable.of_norm_bounded hu fun k => hbd k 0
  have hval : ∀ k, g' k 0 = c k * Torus.partialDeriv j (Torus.realMode k) a := by
    intro k
    simp only [hg', zero_smul, add_zero, hz₀]
    rw [Dmode_rep]
  have : HasSum (fun k => g' k 0) (∑' k, g' k 0) := hsum'.hasSum
  rw [huniq] at this
  have e2 : Torus.partialDeriv j ψ a = fderiv ℝ (Torus.lift ψ) z₀ e := rfl
  rw [e2]
  have e3 : (fun k => g' k 0) =
      fun k : NonzeroLattice d => Torus.funRealCoeff ψ k * Torus.partialDeriv j (Torus.realMode k) a :=
    funext hval
  rw [e3] at this
  exact this

theorem inner_bVec_lpFun {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {ψ : Torus d → ℝ} (hψ : MemSobolev n ψ)
    (hc : Continuous ψ) (hψ1 : Torus.IsCk 1 ψ) (j : Fin d) (a : Torus d) :
    inner ℝ (bVec n j a) (lpFun n ψ) = Torus.partialDeriv j ψ a := by
  rw [HRS.Uniform.Q54.inner_eq_tsum_coord]
  have hs := partialDeriv_series hn hψ hc hψ1 j a
  refine (tsum_congr fun k => ?_).trans hs.tsum_eq
  rw [HRS.Uniform.Q14.q14_coord_bVec (by linarith) j a k, coord_lpFun hψ]
  have hj := Real.rpow_pos_of_pos (Torus.jp_pos k.1) n
  have : Lattice.jp k.1 ^ (-n) * Lattice.jp k.1 ^ n = 1 := by
    rw [← Real.rpow_add (Torus.jp_pos k.1)]; simp
  calc Lattice.jp k.1 ^ (-n) * Torus.partialDeriv j (Torus.realMode k) a *
        (Lattice.jp k.1 ^ n * Torus.funRealCoeff ψ k)
      = (Lattice.jp k.1 ^ (-n) * Lattice.jp k.1 ^ n) *
        (Torus.funRealCoeff ψ k * Torus.partialDeriv j (Torus.realMode k) a) := by ring
    _ = _ := by rw [this, one_mul]

end HRS.Uniform.Q54c
