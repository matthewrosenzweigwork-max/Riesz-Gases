import HRS.MS.R2WinOrbTRD10

/-!
# S10.3 packet [C], part 11: the datum class of `L_tφ_α` (second level)

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_phi_syn3`: the tests `φ_α` lie in `SyN 3 n (K b_α)` (all jets decay like `(1+‖x‖)⁻³`).
* `s103c_force_dec`: the full decay `‖D^j(∇g*h)(x)‖ ≤ C A (1+‖x‖)^{-(s+1+j)}` (the form of `ult_core`).
* `DatD` calculus (`DatD.add`, `SyN.toDatD`) and `s103c_g1_datd`: for a density `h = ρ_l ∈ U2Dec` the datum `L_hφ_α` lies in `DatD`, with a constant
  linear in `b_α` and independent of `l`.  This is what the layer estimate (`s103c_layer1`) and the weighted estimate need for the second-level data.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb
  HRS.MS.MovOsc

variable {d : ℕ}

theorem s103c_phi_syn3 (n : ℕ) (hn : n ≤ 10 * d + 100) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ α : MultiIndex d, SyN 3 n (K * s103_b d α) (oscTestFun ((24 * d + 240 : ℕ) : ℝ) α) := by
  have hj : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : SchwartzMap (Euc d) ℝ) (x : Euc d),
      (1 + ‖x‖) ^ 3 * ‖iteratedFDeriv ℝ j f x‖ ≤ C * oscNorm ((3 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f :=
    fun j => HRS.MS.R2WinOrb.s103_weighted 3 j
  choose C hC0 hC using hj
  refine ⟨∑ j ∈ Finset.range (n + 1), C j, Finset.sum_nonneg fun j _ => hC0 j, fun α => ?_⟩
  obtain ⟨f, hf⟩ : ∃ f : SchwartzMap (Euc d) ℝ, ⇑f = oscTestFun ((24 * d + 240 : ℕ) : ℝ) α := by
    have hmem : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α ∈ mo_Hspan d := by
      have : oscTestFun ((24 * d + 240 : ℕ) : ℝ) α =
          (oscEigenvalue d α ^ (-(((24 * d + 240 : ℕ) : ℝ) / 2))) • hermiteFunD α := by
        funext x; simp [oscTestFun]
      rw [this]
      exact Submodule.smul_mem _ _ (mova3_hermite_mem α)
    exact mova3c_hspan_schwartz hmem
  rw [← hf]
  have hb0 := s103_b_nonneg (d := d) α
  refine ⟨(f.smooth _).of_le (s103_cast_le_infty _), fun j hjn x => ?_⟩
  have hCj : ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ 3 ≤
      C j * oscNorm ((3 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f := by
    rw [mul_comm]; exact hC j f x
  refine hCj.trans ?_
  have hjm : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have hle : C j ≤ ∑ j ∈ Finset.range (n + 1), C j := Finset.single_le_sum (f := C) (fun i _ => hC0 i) hjm
  have hosc : oscNorm ((3 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤ s103_b d α := by
    rw [hf, HRS.MS.R2WinOrb.s103_oscNorm_test]
    unfold s103_b
    refine Real.rpow_le_rpow_of_exponent_le (one_le_oscEigenvalue α) ?_
    have hfl : (⌊(j : ℝ) + (d : ℝ) / 2⌋₊ : ℝ) ≤ (j : ℝ) + (d : ℝ) / 2 := Nat.floor_le (by positivity)
    have hjn' : (j : ℝ) ≤ (n : ℝ) := by exact_mod_cast hjn
    have hn' : (n : ℝ) ≤ 10 * (d : ℝ) + 100 := by exact_mod_cast hn
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    push_cast
    linarith
  have hoscnn : 0 ≤ oscNorm ((3 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f := Real.sqrt_nonneg _
  calc C j * oscNorm ((3 + ⌊(j : ℝ) + (d : ℝ) / 2⌋₊ + 1 : ℕ) : ℝ) f ≤ C j * s103_b d α :=
        mul_le_mul_of_nonneg_left hosc (hC0 j)
    _ ≤ _ := mul_le_mul_of_nonneg_right hle hb0

theorem SyN.toDatD {N : ℕ} {A : ℝ} {f : Euc d → ℝ} (h : SyN 2 N A f) : DatD N A f :=
  ⟨h.1, h.bd.2, fun j _ hj x => h.2 j hj x⟩

theorem DatD.add {N : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : DatD N A f) (hg : DatD N B g) :
    DatD N (A + B) (fun x => f x + g x) := by
  refine ⟨hf.1.add hg.1, fun j hj x => ?_, fun j h1 hj x => ?_⟩
  · have e : (fun x => f x + g x) = f + g := rfl
    rw [e, iteratedFDeriv_add_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
      (hg.1.of_le (by exact_mod_cast hj)).contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hf.2.1 j hj x) (hg.2.1 j hj x))
  · have e : (fun x => f x + g x) = f + g := rfl
    rw [e, iteratedFDeriv_add_apply (hf.1.of_le (by exact_mod_cast hj)).contDiffAt
      (hg.1.of_le (by exact_mod_cast hj)).contDiffAt]
    have hp : 0 ≤ (1 + ‖x‖) ^ 2 := by positivity
    calc ‖iteratedFDeriv ℝ j f x + iteratedFDeriv ℝ j g x‖ * (1 + ‖x‖) ^ 2 ≤
        (‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖) * (1 + ‖x‖) ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_add_le _ _) hp
      _ = ‖iteratedFDeriv ℝ j f x‖ * (1 + ‖x‖) ^ 2 + ‖iteratedFDeriv ℝ j g x‖ * (1 + ‖x‖) ^ 2 := by ring
      _ ≤ A + B := add_le_add (hf.2.2 j h1 hj x) (hg.2.2 j h1 hj x)

theorem DatD.zero (N : ℕ) : DatD N 0 (fun _ : Euc d => (0 : ℝ)) := (SyN.zero (d := d) 2 N).toDatD

theorem DatD.sum {N : ℕ} {ι : Type*} (S : Finset ι) (f : ι → Euc d → ℝ) (A : ι → ℝ)
    (h : ∀ i ∈ S, DatD N (A i) (f i)) : DatD N (∑ i ∈ S, A i) (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using DatD.zero (d := d) N
  | insert a S ha ih =>
    have h1 := h a (Finset.mem_insert_self _ _)
    have h2 := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have := h1.add h2
    simp only [Finset.sum_insert ha]
    exact this

theorem s103c_force_dec {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) {L : ℝ}
    (hL : (d : ℝ) + k + s + 3 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℝ) (h : Euc d → ℝ), 0 ≤ A → U2Dec (k + 1) L A h →
      ∀ i : Fin d, DatD k (C * A) (fun x => movForce d s h x i) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hdL : (d : ℝ) < L := by linarith
  choose Ci hCi0 hCi using fun i : Fin d => ult_core (by omega : 1 ≤ d) (ult_ker_kap hs0 hsd i) k hL
  refine ⟨∑ i, Ci i, Finset.sum_nonneg fun i _ => hCi0 i, fun A h hA hdec i => ?_⟩
  have hfun : (fun x => movForce d s h x i) = ultK (u2_kap d s i) h := by
    funext x
    exact (ult_conv_comp (by omega : 1 ≤ d) hs0 hsd hdL hA (ult_U2Dec_mono hdec (by omega : 1 ≤ k + 1)) x).2 i
  rw [hfun]
  obtain ⟨hcd, hb⟩ := hCi i A h hA hdec
  have hle : Ci i ≤ ∑ i, Ci i := Finset.single_le_sum (f := Ci) (fun i _ => hCi0 i) (Finset.mem_univ i)
  have hCA : 0 ≤ (∑ i, Ci i) * A := mul_nonneg (Finset.sum_nonneg fun i _ => hCi0 i) hA
  refine ⟨hcd, fun j hj x => ?_, fun j h1 hj x => ?_⟩
  · refine (hb j hj x).trans ?_
    have hw : (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by
        have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        linarith)
    calc Ci i * A * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) ≤ Ci i * A * 1 :=
          mul_le_mul_of_nonneg_left hw (mul_nonneg (hCi0 i) hA)
      _ ≤ (∑ i, Ci i) * A := by rw [mul_one]; gcongr
  · have hx : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hexp : (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) * (1 + ‖x‖) ^ 2 ≤ 1 := by
      have : ((1 + ‖x‖) ^ (2 : ℕ) : ℝ) = (1 + ‖x‖) ^ ((2 : ℕ) : ℝ) := (Real.rpow_natCast _ 2).symm
      rw [this, ← Real.rpow_add hx]
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x])
      push_cast
      have : (1 : ℝ) ≤ j := by exact_mod_cast h1
      linarith
    calc ‖iteratedFDeriv ℝ j (ultK (u2_kap d s i) h) x‖ * (1 + ‖x‖) ^ 2 ≤
        Ci i * A * (1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) * (1 + ‖x‖) ^ 2 :=
          mul_le_mul_of_nonneg_right (hb j hj x) (by positivity)
      _ = Ci i * A * ((1 + ‖x‖) ^ (-(s + 1 + (j : ℝ))) * (1 + ‖x‖) ^ 2) := by ring
      _ ≤ Ci i * A * 1 := mul_le_mul_of_nonneg_left hexp (mul_nonneg (hCi0 i) hA)
      _ ≤ (∑ i, Ci i) * A := by rw [mul_one]; gcongr

theorem s103c_g1_datd {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (a β : ℝ) (M : ℕ) {L : ℝ}
    (hL : (d : ℝ) + M + s + 3 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Aρ Aφ : ℝ) (h φ : Euc d → ℝ), 0 ≤ Aρ → 0 ≤ Aφ → U2Dec (M + 1) L Aρ h →
      SyN 3 (M + 2) Aφ φ →
      DatD M (C * ((1 + Aρ) * Aφ))
        (fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => h)) 0 φ x) := by
  obtain ⟨Cf, hCf0, hCf⟩ := s103c_force_dec hd hs0 hsd M hL
  refine ⟨|β⁻¹| * d + d * (|a| * ((M : ℝ) + 1)) + d * 2 ^ M * Cf + d * (Cf * 2 ^ (M + 1)), by positivity, ?_⟩
  intro Aρ Aφ h φ hAρ hAφ hdec hφ
  have hn : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  have hDφ : ∀ i : Fin d, SyN 3 (M + 1) Aφ (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) := fun i => by
    have := hφ.deriv (EuclideanSpace.single i (1 : ℝ))
    rwa [hn i, mul_one] at this
  have hDDφ : ∀ i : Fin d, SyN 3 M Aφ (fun y => fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) y
      (EuclideanSpace.single i (1 : ℝ))) := fun i => by
    have := (hDφ i).deriv (EuclideanSpace.single i (1 : ℝ))
    rwa [hn i, mul_one] at this
  have hφ2 : ContDiff ℝ 2 φ := by
    have := hφ.1.of_le (show ((2 : ℕ) : WithTop ℕ∞) ≤ ((M + 2 : ℕ) : WithTop ℕ∞) by exact_mod_cast (by omega))
    exact_mod_cast this
  -- the `L_0` part
  have T1a : DatD M (|β⁻¹| * ∑ i : Fin d, Aφ) (fun x => β⁻¹ * Laplacian.laplacian φ x) := by
    have hlap : ∀ x, Laplacian.laplacian φ x = ∑ i : Fin d,
        fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) :=
      fun x => s103n_lap_eq hφ2 x
    simp only [hlap]
    have := (SyN.sum Finset.univ _ _ (fun i _ => (hDDφ i).mono_p (p := 3) (q := 2) (by norm_num))).smul β⁻¹
    exact this.toDatD
  have T1b : DatD M (∑ i : Fin d, |(-a)| * (((M : ℝ) + 1) * Aφ))
      (fun x => ∑ i : Fin d, (-a) * (x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := by
    have := SyN.sum Finset.univ _ _ (fun i _ => ((((hDφ i).mono_N (Nat.le_succ M)).xmul (p := 2) i).smul (-a)))
    exact this.toDatD
  -- the nonlocal part
  have hDb : ∀ i : Fin d, Bd (M + 1) Aφ (fun y => fderiv ℝ φ y (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => (hDφ i).bd
  have hFd : ∀ i : Fin d, DatD M (Cf * Aρ) (fun x => movForce d s h x i) := fun i => hCf Aρ h hAρ hdec i
  have T2 : DatD M (∑ i : Fin d, |(-1 : ℝ)| * (2 ^ M * Aφ * (Cf * Aρ)))
      (fun x => ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i *
        fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) := by
    have := SyN.sum (N := M) Finset.univ (fun i x => (-1 : ℝ) * (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) *
      movForce d s h x i)) _ (fun i _ => ((((hDφ i).mono_N (Nat.le_succ M)).mono_p (p := 3) (q := 2) (by norm_num)).mul_bd
        (hFd i).bd).smul (-1))
    have e : (fun x => ∑ i : Fin d, (-1 : ℝ) * (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) *
        movForce d s h x i)) = fun x => ∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i *
          fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
      funext x; refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [e] at this
    exact this.toDatD
  have hhj : ∀ j : Fin d, U2Dec (M + 1) L (Aρ * Aφ * 2 ^ (M + 1))
      (fun y => h y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) := fun j =>
    who_u2dec_mul hdec (hDb j).1 (fun i hi y => (hDb j).2 i hi y)
  have T3 : DatD M (∑ j : Fin d, Cf * (Aρ * Aφ * 2 ^ (M + 1)))
      (fun x => ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j) :=
    DatD.sum Finset.univ _ _ (fun j _ => hCf _ _ (by positivity) (hhj j) j)
  have hsum := (T1a.add T1b).add (T2.add T3)
  have hfun : (fun x => generatorW ((quadraticGradientDyn d s a β).coeff (fun _ => h)) 0 φ x) = fun x =>
      (β⁻¹ * Laplacian.laplacian φ x + ∑ i : Fin d, (-a) * (x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)))) +
      (∑ i : Fin d, (-1 : ℝ) * (movForce d s h x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) +
       ∑ j : Fin d, movForce d s (fun y => h y * fderiv ℝ φ y (EuclideanSpace.single j (1 : ℝ))) x j) := by
    funext x
    rw [s103b_gen_split, s103b_L0_eq]
    simp only [s103bQ, Finset.sum_neg_distrib, neg_mul, sub_eq_add_neg]
  rw [hfun]
  refine hsum.mono_A ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, abs_neg, abs_one, one_mul]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hM1 : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
  have h2M : (0 : ℝ) ≤ 2 ^ M := by positivity
  rw [pow_succ]
  have hX : 0 ≤ 2 ^ M * Cf * Aφ := mul_nonneg (mul_nonneg h2M hCf0) hAφ
  have p1 := mul_nonneg (mul_nonneg hd0 (abs_nonneg β⁻¹)) (mul_nonneg hAρ hAφ)
  have p2 := mul_nonneg (mul_nonneg hd0 (mul_nonneg (abs_nonneg a) hM1)) (mul_nonneg hAρ hAφ)
  have p3 := mul_nonneg hd0 hX
  nlinarith [p1, p2, p3]

end HRS.MS.R2WinOrbNL

end
