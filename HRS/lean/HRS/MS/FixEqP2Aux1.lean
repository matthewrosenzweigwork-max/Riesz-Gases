import HRS.MS.FixEqP1Aux3
import HRS.MS.GoMeasAux3
import HRS.MS.OrbFeatAux2

/-!
# S5.7 `fixed_equation` (worker S57P), part 4: generator facts for `fixedEqCoeff` (inputs of the stability and Duhamel arguments)

For the coefficients `fixedEqCoeff s M Q ν c ρ` (free transport `-Qx + c_t(x)`, nonlocal term along `ρ_t`):

* `s57p_gen_rgW`: `‖D^n 𝓛_τ u‖ ≤ B K (1+|x|)`, `n ≤ 1`, for `u ∈ C^4` with `‖D^n u‖ ≤ B` (`n ≤ 4`);
* `s57p_gen_tendsto`: continuity of `(τ, u) ↦ 𝓛_τ u (x)` along converging families (jets converging pointwise);
* `s57p_rho_data`: the decay class and pointwise time continuity of `ρ` from the hypotheses of `fixed_equation`.

All proofs follow `HRS/MS/GoMeasAux2.lean` (`s55m_*`), whose transport `meanFieldDriftW D (ρ τ)` is replaced by `-Qx + c_τ`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.Whole.AppendixA

variable {d : ℕ}

/-- the data used about `(c, ρ)`: bounded `C^3` transport, `ρ_t` of decay class `3` uniformly, weak time continuity -/
structure S57pFeData (s : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (c : ℝ → Euc d → Euc d)
    (ρ : ℝ → Euc d → ℝ) (T : ℝ) : Prop where
  hd : 1 ≤ d
  hs0 : 0 ≤ s
  hsd : s < d
  hν : 0 ≤ ν
  rho : ∃ A : ℝ, 0 ≤ A ∧ (∀ t ∈ Set.Icc (0 : ℝ) T, RgDecay 3 (fun _ => A) (ρ t)) ∧
    ∀ y, ContinuousOn (fun t => ρ t y) (Set.Icc (0 : ℝ) T)
  drift : ∃ Λc : ℝ, 0 ≤ Λc ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ 3 (c t) ∧
    ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i (c t) x‖ ≤ Λc
  cont : ContinuousOn (fun p : ℝ × Euc d => c p.1 p.2) (Set.Icc (0 : ℝ) T ×ˢ Set.univ)

/-- the linear part of the transport as a weighted class -/
theorem s57p_RgW_linear (Q : Matrix (Fin d) (Fin d) ℝ) (j : Fin d) :
    ∃ K : ℝ, 0 ≤ K ∧ RgW (fun x : Euc d => 1 + ‖x‖) 1 K (fun x => -(Torus.matVec Q x) j) := by
  let L : Euc d →L[ℝ] ℝ := -((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp
    (Matrix.toEuclideanLin Q).toContinuousLinearMap)
  have hL : ∀ x, -(Torus.matVec Q x) j = L x := fun x => by simp [L, Torus.matVec]
  have e : (fun x => -(Torus.matVec Q x) j) = fun x => L x := funext hL
  rw [e]
  refine ⟨‖L‖, norm_nonneg _, L.contDiff.of_le (by exact_mod_cast le_top), fun n hn x => ?_⟩
  have hw : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  interval_cases n
  · rw [norm_iteratedFDeriv_zero]
    calc ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
      _ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
  · rw [norm_iteratedFDeriv_one, ContinuousLinearMap.fderiv]
    calc ‖L‖ = ‖L‖ * 1 := (mul_one _).symm
      _ ≤ ‖L‖ * (1 + ‖x‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg _)


theorem s57p_c_RgW {Λc : ℝ} {g : Euc d → Euc d} (hg : ContDiff ℝ 3 g)
    (hb : ∀ i ≤ 3, ∀ x, ‖iteratedFDeriv ℝ i g x‖ ≤ Λc) (j : Fin d) :
    RgW (fun x : Euc d => 1 + ‖x‖) 1 Λc (fun x => g x j) := by
  have hΛ : 0 ≤ Λc := le_trans (norm_nonneg _) (hb 0 (by norm_num) 0)
  let P : Euc d →L[ℝ] ℝ := EuclideanSpace.proj j
  have hP : ‖P‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => ?_
    simpa [P] using PiLp.norm_apply_le y j
  have e : (fun x => g x j) = fun x => P (g x) := rfl
  rw [e]
  have h1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  refine ⟨P.contDiff.comp h1, fun n hn x => ?_⟩
  have := P.norm_iteratedFDeriv_comp_left (f := g) (x := x) (n := n) (N := (1 : ℕ)) h1.contDiffAt (by exact_mod_cast hn)
  have hw : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  calc ‖iteratedFDeriv ℝ n (fun x => P (g x)) x‖ ≤ ‖P‖ * ‖iteratedFDeriv ℝ n g x‖ := this
    _ ≤ 1 * Λc := mul_le_mul hP (hb n (by omega) x) (norm_nonneg _) zero_le_one
    _ ≤ Λc * (1 + ‖x‖) := by nlinarith

/-- **Uniform bound of the generator** of `fixedEqCoeff` on `C^4` functions. -/
theorem s57p_gen_rgW {s : ℝ} (M Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} {c : ℝ → Euc d → Euc d}
    {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hD : S57pFeData s Q ν c ρ T) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B → ContDiff ℝ 4 u →
      (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
      RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW (fixedEqCoeff s M Q ν c ρ) τ u) := by
  obtain ⟨A, hA0, hdec, -⟩ := hD.rho
  obtain ⟨Λc, hΛc, hc⟩ := hD.drift
  choose Kj hKj0 hKj using fun j : Fin d => s57p_RgW_linear Q j
  set Bb : ℝ := ∑ j, Kj j + Λc with hBb
  have hBb0 : 0 ≤ Bb := add_nonneg (Finset.sum_nonneg fun j _ => hKj0 j) hΛc
  have hMB := s55f_matBound M
  set MB : ℝ := ∑ i, ∑ j, |M i j| with hMBdef
  have hMB0 : 0 ≤ MB := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hσ : 0 ≤ movtr_sigma s := rg_sigma_nonneg hD.hs0
  have hnear := rg_near_nonneg (d := d) s
  have hW := rg_W_nonneg (d := d)
  set Kn : ℝ := d * (movtr_sigma s * ((2 ^ (1 + 2) * A * ((d : ℝ) * MB)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (1 + 2) * A * ((d : ℝ) * MB)) * rgW d)) with hKn
  have hKn0 : 0 ≤ Kn := by rw [hKn]; positivity
  refine ⟨|ν| * d + d * (2 ^ 1 * Bb) + Kn, by positivity, fun τ hτ B u hB hu hub => ?_⟩
  have hu3 : ContDiff ℝ 3 u := hu.of_le (by norm_num)
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  have hLap := rg_laplacian (k := 1) (hu.of_le (by norm_num)) (fun n hn x => hub n (by omega) x)
  have hνt : RgW (fun _ : Euc d => (1 : ℝ)) 1 (|ν| * (d * B)) (fun x => ν * Laplacian.laplacian u x) :=
    hLap.const_mul _
  have hb : ∀ j : Fin d, RgW (fun x : Euc d => 1 + ‖x‖) 1 Bb
      (fun x => (-(Torus.matVec Q x) + c τ x) j) := by
    intro j
    have h1 := (hKj j)
    have h2 := s57p_c_RgW (hc τ hτ).1 (hc τ hτ).2 j
    have h3 := RgW.add h1 h2
    refine (h3.mono (fun x => by positivity) ?_)
    rw [hBb]
    have : Kj j ≤ ∑ j, Kj j := Finset.single_le_sum (f := Kj) (fun j _ => hKj0 j) (Finset.mem_univ j)
    linarith
  have hT2 := rg_transport (k := 1) hB hBb0 (hu.of_le (by norm_num)) (fun n hn x => hub n (by omega) x)
    (b := fun x => -(Torus.matVec Q x) + c τ x) hb
  have hBg : 0 ≤ (d : ℝ) * MB * B := by positivity
  have hT3 := rg_T3 hD.hd hD.hs0 hD.hsd (k := 1) hA0 hBg (hdec τ hτ)
    (g := fun j y => Torus.matVec M.transpose (gradient u y) j)
    (fun j => rg_matgrad (k := 1) hMB (by push_cast; norm_num; exact hu)
      (fun n hn x => hub n (by omega) x) j)
  have hmain := (hνt.of_one.add hT2).sub hT3.of_one
  have hfun : generatorW (fixedEqCoeff s M Q ν c ρ) τ u = fun x =>
      (ν * Laplacian.laplacian u x + inner ℝ (-(Torus.matVec Q x) + c τ x) (gradient u x)) -
        ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
          (fun y => ρ τ y * (Torus.matVec M.transpose (gradient u y)) j) x) j := rfl
  rw [hfun]
  refine hmain.mono (fun x => by positivity) ?_
  rw [hKn]
  have e : (d : ℝ) * (movtr_sigma s * ((2 ^ (1 + 2) * A * ((d : ℝ) * MB * B)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (1 + 2) * A * ((d : ℝ) * MB * B)) * rgW d)) =
      B * (d * (movtr_sigma s * ((2 ^ (1 + 2) * A * ((d : ℝ) * MB)) * rgNear d s +
      4 ^ (s + 1) * (2 ^ (1 + 2) * A * ((d : ℝ) * MB)) * rgW d))) := by ring
  nlinarith [e]

/-- **Continuity of the generator** along converging families. -/
theorem s57p_gen_tendsto {s : ℝ} (M Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} {c : ℝ → Euc d → Euc d}
    {ρ : ℝ → Euc d → ℝ} {T : ℝ} (hD : S57pFeData s Q ν c ρ T) {B : ℝ} (hB : 0 ≤ B)
    {τ : ℕ → ℝ} {τ₀ : ℝ} (hτ : ∀ m, τ m ∈ Set.Icc (0 : ℝ) T) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) T)
    (hτt : Tendsto τ atTop (𝓝 τ₀)) {u : ℕ → Euc d → ℝ} {u₀ : Euc d → ℝ}
    (hu : ∀ m, ContDiff ℝ 3 (u m) ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n (u m) x‖ ≤ B)
    (hu₀ : ContDiff ℝ 3 u₀ ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n u₀ x‖ ≤ B)
    (h1 : ∀ y, Tendsto (fun m => iteratedFDeriv ℝ 1 (u m) y) atTop (𝓝 (iteratedFDeriv ℝ 1 u₀ y)))
    (x : Euc d)
    (h2 : Tendsto (fun m => iteratedFDeriv ℝ 2 (u m) x) atTop (𝓝 (iteratedFDeriv ℝ 2 u₀ x))) :
    Tendsto (fun m => generatorW (fixedEqCoeff s M Q ν c ρ) (τ m) (u m) x) atTop
      (𝓝 (generatorW (fixedEqCoeff s M Q ν c ρ) τ₀ u₀ x)) := by
  obtain ⟨A, hA, hρ, hpt⟩ := hD.rho
  have hMB := s55f_matBound M
  have hMB0 : 0 ≤ ∑ i, ∑ j, |M i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  show Tendsto (fun m => ν * Laplacian.laplacian (u m) x +
      inner ℝ (-(Torus.matVec Q x) + c (τ m) x) (gradient (u m) x) -
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ (τ m) y * (Torus.matVec M.transpose (gradient (u m) y)) j) x) j) atTop
    (𝓝 (ν * Laplacian.laplacian u₀ x + inner ℝ (-(Torus.matVec Q x) + c τ₀ x) (gradient u₀ x) -
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ₀ y * (Torus.matVec M.transpose (gradient u₀ y)) j) x) j))
  have hρt : ∀ y, Tendsto (fun m => ρ (τ m) y) atTop (𝓝 (ρ τ₀ y)) := fun y =>
    ((hpt y τ₀ hτ₀).tendsto).comp (tendsto_nhdsWithin_iff.2 ⟨hτt, Eventually.of_forall hτ⟩)
  have hρ2 : ∀ t ∈ Set.Icc (0 : ℝ) T, RgDecay 2 (fun _ => A) (ρ t) := fun t ht =>
    rg_decay_mono (by norm_num) (hρ t ht)
  have hct : Tendsto (fun m => c (τ m) x) atTop (𝓝 (c τ₀ x)) := by
    have hc := hD.cont (τ₀, x) ⟨hτ₀, Set.mem_univ _⟩
    have hseq : Tendsto (fun m => ((τ m, x) : ℝ × Euc d)) atTop (𝓝[Set.Icc (0 : ℝ) T ×ˢ Set.univ] (τ₀, x)) :=
      tendsto_nhdsWithin_iff.2 ⟨(hτt.prodMk_nhds tendsto_const_nhds),
        Eventually.of_forall fun m => ⟨hτ m, Set.mem_univ _⟩⟩
    exact hc.tendsto.comp hseq
  have hdrift : Tendsto (fun m => -(Torus.matVec Q x) + c (τ m) x) atTop (𝓝 (-(Torus.matVec Q x) + c τ₀ x)) :=
    tendsto_const_nhds.add hct
  have hgrad : Tendsto (fun m => gradient (u m) x) atTop (𝓝 (gradient u₀ x)) :=
    s55m_grad_tendsto (h1 x)
  have hlap := s55m_lap_tendsto h2
  have hnl : Tendsto (fun m => ∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ (τ m) y * (Torus.matVec M.transpose (gradient (u m) y)) j) x) j) atTop
      (𝓝 (∑ j : Fin d, (convGradConvW (rieszKernelGrad d s)
        (fun y => ρ τ₀ y * (Torus.matVec M.transpose (gradient u₀ y)) j) x) j)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    refine s55m_conv_tendsto hD.hd hD.hs0 hD.hsd (c := 2 ^ 2 * A * ((d : ℝ) * (∑ i, ∑ j, |M i j|) * B)) (by positivity)
      (k := fun m y => ρ (τ m) y * (Torus.matVec M.transpose (gradient (u m) y)) j)
      (k₀ := fun y => ρ τ₀ y * (Torus.matVec M.transpose (gradient u₀ y)) j)
      (fun m => s55m_nl_decay hMB hMB0 hA hB (hρ2 _ (hτ m)) (hu m).1 (hu m).2 j)
      (s55m_nl_decay hMB hMB0 hA hB (hρ2 _ hτ₀) hu₀.1 hu₀.2 j) (fun y => ?_) x j
    refine (hρt y).mul ?_
    simp only [HRS.Whole.Q09B.q09b_matVec_apply]
    refine tendsto_finsetSum _ fun i _ => Tendsto.const_mul _ ?_
    exact ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp (s55m_grad_tendsto (h1 y))
  exact ((hlap.const_mul _).add (hdrift.inner hgrad)).sub hnl

/-- the decay class and pointwise time continuity of `ρ` from the weighted bounds of `fixed_equation` -/
theorem s57p_rho_data (b : WholeBounds d) (hb : b.Valid) {n : ℕ} (hn : 3 ≤ n) {ρ : ℝ → Euc d → ℝ}
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ n (ρ t) ∧ weightedSupE n b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hcont : ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B : ℝ, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) b.T)) :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ t ∈ Set.Icc (0 : ℝ) b.T, RgDecay 3 (fun _ => A) (ρ t)) ∧
      ∀ y, ContinuousOn (fun t => ρ t y) (Set.Icc (0 : ℝ) b.T) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hL := hb.hL
  have hs0 := hb.hs0
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg b.k
  have hdL : (d : ℝ) + 3 ≤ b.L := by linarith
  set Λ3 : ℝ := (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max b.Λ 0 with hΛ3
  have hreg3 : ∀ t ∈ Set.Icc (0 : ℝ) b.T, MemCb 3 (ρ t) ∧
      weightedSupE 3 ((d : ℝ) + 3) (ρ t) < ⊤ ∧
      HRS.cbNorm 3 (ρ t) + (weightedSupE 3 ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ3 := fun t ht =>
    s55_regular_slice hn hdL (hdens t ht).1 (hdens t ht).2
  set A : ℝ := (d : ℝ) ^ 3 * max Λ3 0 * 2 ^ ((d : ℝ) + 3) with hAdef
  have hA : 0 ≤ A := by positivity
  have hdec : ∀ r ∈ Set.Icc (0 : ℝ) b.T, RgDecay 3 (fun _ => A) (ρ r) := by
    intro r hr
    have hcb := hreg3 r hr
    exact rg_rho_decay hd1 (r := 3) (Λ := max Λ3 0) hcb.1 hcb.2.1
      (by linarith [hcb.2.2, le_max_left Λ3 0, show 0 ≤ HRS.cbNorm 3 (ρ r) from
        Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _])
  refine ⟨A, hA, hdec, fun y => ?_⟩
  have hparts := fun r hr => rg_decay_parts (n := 3) (by omega) (a := fun _ => A)
    (fun _ => hA) (hdec r hr)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    linarith
  have hdiff : ∀ r ∈ Set.Icc (0 : ℝ) b.T, Differentiable ℝ (ρ r) := fun r hr =>
    ((hparts r hr).1).differentiable (by norm_num)
  have h1' : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ y, ‖fderiv ℝ (ρ r) y‖ ≤ A := fun r hr y =>
    ((hparts r hr).2.2.1 y).trans (by
      calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ A * 1 := mul_le_mul_of_nonneg_left (hw y) hA
        _ = A := mul_one _)
  have hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) b.T) := by
    intro ψ hψ hcs
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hψ.continuous
    exact hcont ψ hψ.continuous ⟨C, fun x => by simpa using hC x⟩
  exact s55_pointwise hA hweak hdiff h1' y

/-- from `cbNormVecE` to pointwise derivative bounds -/
theorem s57p_cbVec_bound {K : ℕ} {v : Euc d → Euc d} {Λ : ℝ} (h : cbNormVecE K v ≤ ENNReal.ofReal Λ)
    {i : ℕ} (hi : i ≤ K) (x : Euc d) : ‖iteratedFDeriv ℝ i v x‖ ≤ max Λ 0 := by
  unfold cbNormVecE at h
  have h1 : (⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i v y‖) ≤ ENNReal.ofReal Λ :=
    (Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v y‖)
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))).trans h
  have h2 : ENNReal.ofReal ‖iteratedFDeriv ℝ i v x‖ ≤ ENNReal.ofReal Λ := (le_iSup _ x).trans h1
  by_cases hΛ : 0 ≤ Λ
  · exact ((ENNReal.ofReal_le_ofReal_iff hΛ).1 h2).trans (le_max_left _ _)
  · push Not at hΛ
    rw [ENNReal.ofReal_of_nonpos hΛ.le] at h2
    have := ENNReal.ofReal_eq_zero.1 (le_antisymm h2 zero_le)
    exact this.trans (le_max_right _ _)

/-- `S57pFeData` from the hypotheses of `fixed_equation` -/
theorem s57p_feData (b : WholeBounds d) (hb : b.Valid) {n : ℕ} (hn : 3 ≤ n) {ν : ℝ} (hν : 0 ≤ ν)
    {c : ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ}
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ n (ρ t) ∧ weightedSupE n b.L (ρ t) ≤ ENNReal.ofReal b.Λ)
    (hc : ∀ t ∈ Set.Icc (0 : ℝ) b.T, ContDiff ℝ n (c t) ∧ cbNormVecE n (c t) ≤ ENNReal.ofReal b.Λ)
    (hF : FixedEqFcauHyp b ν c ρ) : S57pFeData b.s b.Q ν c ρ b.T := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  refine ⟨hd1, hb.hs0, hb.hsd, hν, s57p_rho_data b hb hn hdens hF.rho_cont, ?_, hF.drift_cont⟩
  refine ⟨max b.Λ 0, le_max_right _ _, fun t ht => ⟨(hc t ht).1.of_le (by exact_mod_cast hn),
    fun i hi x => ?_⟩⟩
  exact s57p_cbVec_bound (hc t ht).2 (by omega) x

end HRS.MS.FixEq
