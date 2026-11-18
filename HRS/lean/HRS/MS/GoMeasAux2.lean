import HRS.MS.GoFeatTie
import HRS.MS.GoMeasAux1

/-!
# S55M, part 2: the generator along converging families (coefficients of a `WholeSetup`)

Helper names carry the prefix `s55m_`; namespace `HRS.MS.Go`.

* `s55m_rgT_tendsto`: dominated convergence for the cancellation-convention convolution `rgT κ` (fixed point `x`).
* `s55m_gen_rgW`: uniform bound `‖D^n 𝓛_τ u‖ ≤ B·K (1+|x|)`, `n ≤ 1`, for `u ∈ C^4` with `‖D^n u‖ ≤ B`, `n ≤ 4`
  (`rg_gen_core`, `τ ∈ [0,T]`, constants independent of `τ`, `u`).
* `s55m_gen_tendsto`: if `τ_m → τ` in `[0,T]` and `u_m → u` in `C^2` pointwise with a uniform `C^4` bound, then
  `𝓛_{τ_m} u_m (x) → 𝓛_τ u (x)` for every `x` (needs the continuity in `τ` of `ρ_τ(y)`, from the weak mean-field
  identity `S.mf`, as in `s55f_weak_cont_bdd`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Go
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd HRS.MP.RdGen

variable {d : ℕ}

/-! ### Dominated convergence for `rgT` -/

theorem s55m_rgT_tendsto (hd : 1 ≤ d) {s σ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {κ : Euc d → ℝ}
    (hκ : RgKer d s σ κ) {k : ℕ → Euc d → ℝ} {k₀ : Euc d → ℝ} {b0 b1 : ℝ} (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1)
    (hdiff : ∀ m, Differentiable ℝ (k m))
    (h0 : ∀ m y, ‖k m y‖ ≤ b0 * (1 + ‖y‖) ^ (-((d : ℝ) + 1)))
    (h1 : ∀ m y, ‖fderiv ℝ (k m) y‖ ≤ b1)
    (ht : ∀ y, Tendsto (fun m => k m y) atTop (𝓝 (k₀ y))) (x : Euc d) :
    Tendsto (fun m => rgT κ (k m) x) atTop (𝓝 (rgT κ k₀ x)) := by
  unfold rgT
  refine tendsto_integral_of_dominated_convergence (rgMaj d s σ b0 b1 x)
    (fun m => rg_aesm hκ.meas (hdiff m).continuous x) (rg_maj_integrable hd hsd σ b0 b1 x)
    (fun m => ?_) ?_
  · filter_upwards [movtr_ae_ne_zero (d := d) hd] with z hz
    exact rg_norm_le hs0 hκ (hdiff m) hb0 hb1 (h0 m) (h1 m) x z hz
  · refine Eventually.of_forall fun z => ?_
    refine Tendsto.const_smul ?_ _
    unfold rgR
    by_cases hz : ‖z‖ ≤ 1 / 4
    · simp only [hz, if_true]
      exact (ht _).sub (ht _)
    · simp only [hz, if_false]
      exact ht _

/-! ### The derivatives along a converging family -/

/-- Pointwise convergence of the Laplacian from that of the second derivative at the point. -/
theorem s55m_lap_tendsto {u : ℕ → Euc d → ℝ} {u₀ : Euc d → ℝ} {x : Euc d}
    (h : Tendsto (fun m => iteratedFDeriv ℝ 2 (u m) x) atTop (𝓝 (iteratedFDeriv ℝ 2 u₀ x))) :
    Tendsto (fun m => Laplacian.laplacian (u m) x) atTop (𝓝 (Laplacian.laplacian u₀ x)) := by
  have e : ∀ f : Euc d → ℝ, Laplacian.laplacian f x = ∑ i, iteratedFDeriv ℝ 2 f x
      ![(EuclideanSpace.basisFun (Fin d) ℝ) i, (EuclideanSpace.basisFun (Fin d) ℝ) i] := fun f => by
    have := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := f)
      (EuclideanSpace.basisFun (Fin d) ℝ)) x
    simpa using this
  simp only [e]
  refine tendsto_finsetSum _ fun i _ => ?_
  exact ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Euc d) ℝ
    ![(EuclideanSpace.basisFun (Fin d) ℝ) i, (EuclideanSpace.basisFun (Fin d) ℝ) i]).continuous.tendsto _).comp h

theorem s55m_grad_tendsto {u : ℕ → Euc d → ℝ} {u₀ : Euc d → ℝ} {x : Euc d}
    (h : Tendsto (fun m => iteratedFDeriv ℝ 1 (u m) x) atTop (𝓝 (iteratedFDeriv ℝ 1 u₀ x))) :
    Tendsto (fun m => gradient (u m) x) atTop (𝓝 (gradient u₀ x)) := by
  have e : ∀ f : Euc d → ℝ, gradient f x = (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f x) := fun f => rfl
  simp only [e]
  have e1 : ∀ f : Euc d → ℝ, fderiv ℝ f x = continuousMultilinearCurryFin1 ℝ (Euc d) ℝ
      (iteratedFDeriv ℝ 1 f x) := fun f => by
    ext v; simp [iteratedFDeriv_one_apply]
  have h' : Tendsto (fun m => fderiv ℝ (u m) x) atTop (𝓝 (fderiv ℝ u₀ x)) := by
    simp only [e1]
    exact ((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.tendsto _).comp h
  exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.tendsto _).comp h'

theorem s55m_tendsto_euc {v : ℕ → Euc d} {v₀ : Euc d} (h : ∀ i, Tendsto (fun m => v m i) atTop (𝓝 (v₀ i))) :
    Tendsto v atTop (𝓝 v₀) := by
  have h' : Tendsto (fun m => (WithLp.ofLp (v m) : Fin d → ℝ)) atTop (𝓝 (WithLp.ofLp v₀)) :=
    tendsto_pi_nhds.2 h
  have := ((PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).tendsto _).comp h'
  simpa [Function.comp_def] using this

/-! ### Convolution components along a converging family -/

theorem s55m_conv_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 ≤ c)
    {k : ℕ → Euc d → ℝ} {k₀ : Euc d → ℝ} (hk : ∀ m, RgDecay 2 (fun _ => c) (k m))
    (hk₀ : RgDecay 2 (fun _ => c) k₀) (ht : ∀ y, Tendsto (fun m => k m y) atTop (𝓝 (k₀ y)))
    (x : Euc d) (j : Fin d) :
    Tendsto (fun m => (convGradConvW (rieszKernelGrad d s) (k m) x) j) atTop
      (𝓝 ((convGradConvW (rieszKernelGrad d s) k₀ x) j)) := by
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have parts : ∀ {f : Euc d → ℝ}, RgDecay 2 (fun _ => c) f → Differentiable ℝ f ∧
      (∀ y, ‖f y‖ ≤ c * (1 + ‖y‖) ^ (-((d : ℝ) + 1))) ∧ (∀ y, ‖fderiv ℝ f y‖ ≤ c) := by
    intro f hf
    obtain ⟨h2, h0, h1, -⟩ := rg_decay_parts (n := 2) le_rfl (a := fun _ => c) (fun _ => hc) hf
    exact ⟨h2.differentiable (by norm_num), h0, fun y => (h1 y).trans (by
      calc c * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ c * 1 := mul_le_mul_of_nonneg_left (hw y) hc
        _ = c := mul_one _)⟩
  have e : ∀ f : Euc d → ℝ, RgDecay 2 (fun _ => c) f →
      (convGradConvW (rieszKernelGrad d s) f x) j = rgT (fun z => (rieszKernelGrad d s z) j) f x := by
    intro f hf
    obtain ⟨hd', h0, h1⟩ := parts hf
    exact rg_force_comp hd hs0 hsd hd' hc hc h0 h1 x j
  simp only [e _ (hk _), e _ hk₀]
  exact s55m_rgT_tendsto hd hs0 hsd (rgKerComp_ok hs0 j) hc hc (fun m => (parts (hk m)).1)
    (fun m => (parts (hk m)).2.1) (fun m => (parts (hk m)).2.2) ht x

/-! ### Decay class of `ρ ·(Mᵀ∇u)_j` -/

theorem s55m_nl_decay {MB A B : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} (hMB : PDE.MatBound MB M) (hMB0 : 0 ≤ MB)
    (hA : 0 ≤ A) (hB : 0 ≤ B) {ρ' u : Euc d → ℝ} (hρ' : RgDecay 2 (fun _ => A) ρ') (hu : ContDiff ℝ 3 u)
    (hub : ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) (j : Fin d) :
    RgDecay 2 (fun _ => 2 ^ 2 * A * ((d : ℝ) * MB * B))
      (fun y => ρ' y * (Torus.matVec M.transpose (gradient u y)) j) := by
  have hg : RgW (fun _ => (1 : ℝ)) (0 + 2) ((d : ℝ) * MB * B) (fun y => Torus.matVec M.transpose (gradient u y) j) :=
    rg_matgrad (k := 0) hMB (by push_cast; norm_num; exact hu) (fun n hn x => hub n (by omega) x) j
  have hBg : 0 ≤ (d : ℝ) * MB * B := by positivity
  have hw0 : ∀ y : Euc d, 0 ≤ (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := fun y => Real.rpow_nonneg (by positivity) _
  exact RgW.mul (w := fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) (k := 2) hw0 hA hBg hρ'
    (by simpa using hg)

/-! ### The generator along a converging family -/

theorem s55m_gen_tendsto (hd : 1 ≤ d) (D : WholeDyn d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) {MB A T B : ℝ}
    (hMB : PDE.MatBound MB D.M) (hMB0 : 0 ≤ MB) (hA : 0 ≤ A) (hB : 0 ≤ B) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ t ∈ Set.Icc (0 : ℝ) T, RgDecay 3 (fun _ => A) (ρ t))
    (hpt : ∀ y, ContinuousOn (fun t => ρ t y) (Set.Icc (0 : ℝ) T))
    {τ : ℕ → ℝ} {τ₀ : ℝ} (hτ : ∀ m, τ m ∈ Set.Icc (0 : ℝ) T) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) T)
    (hτt : Tendsto τ atTop (𝓝 τ₀)) {u : ℕ → Euc d → ℝ} {u₀ : Euc d → ℝ}
    (hu : ∀ m, ContDiff ℝ 3 (u m) ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n (u m) x‖ ≤ B)
    (hu₀ : ContDiff ℝ 3 u₀ ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n u₀ x‖ ≤ B)
    (h1 : ∀ y, Tendsto (fun m => iteratedFDeriv ℝ 1 (u m) y) atTop (𝓝 (iteratedFDeriv ℝ 1 u₀ y)))
    (x : Euc d)
    (h2 : Tendsto (fun m => iteratedFDeriv ℝ 2 (u m) x) atTop (𝓝 (iteratedFDeriv ℝ 2 u₀ x))) :
    Tendsto (fun m => generatorW (D.coeff ρ) (τ m) (u m) x) atTop
      (𝓝 (generatorW (D.coeff ρ) τ₀ u₀ x)) := by
  simp only [generatorW_coeff]
  have hρt : ∀ y, Tendsto (fun m => ρ (τ m) y) atTop (𝓝 (ρ τ₀ y)) := fun y =>
    ((hpt y τ₀ hτ₀).tendsto).comp (tendsto_nhdsWithin_iff.2 ⟨hτt, Eventually.of_forall hτ⟩)
  have hρ2 : ∀ t ∈ Set.Icc (0 : ℝ) T, RgDecay 2 (fun _ => A) (ρ t) := fun t ht =>
    rg_decay_mono (by norm_num) (hρ t ht)
  have hconv : ∀ i, Tendsto (fun m => (convGradConvW (rieszKernelGrad d D.s) (ρ (τ m)) x) i) atTop
      (𝓝 ((convGradConvW (rieszKernelGrad d D.s) (ρ τ₀) x) i)) := fun i =>
    s55m_conv_tendsto hd hs0 hsd hA (k := fun m => ρ (τ m)) (k₀ := ρ τ₀) (fun m => hρ2 _ (hτ m))
      (hρ2 _ hτ₀) hρt x i
  have hdrift : Tendsto (fun m => meanFieldDriftW D (ρ (τ m)) x) atTop
      (𝓝 (meanFieldDriftW D (ρ τ₀) x)) := by
    refine s55m_tendsto_euc fun j => ?_
    simp only [meanFieldDriftW, PiLp.sub_apply, HRS.Whole.Q09B.q09b_matVec_apply]
    exact (tendsto_finsetSum _ fun i _ => (hconv i).const_mul _).sub tendsto_const_nhds
  have hgrad : Tendsto (fun m => gradient (u m) x) atTop (𝓝 (gradient u₀ x)) :=
    s55m_grad_tendsto (h1 x)
  have hlap := s55m_lap_tendsto h2
  have hnl : Tendsto (fun m => nlTermRd D (ρ (τ m)) (u m) x) atTop (𝓝 (nlTermRd D (ρ τ₀) u₀ x)) := by
    unfold nlTermRd
    refine tendsto_finsetSum _ fun j _ => ?_
    refine s55m_conv_tendsto hd hs0 hsd (c := 2 ^ 2 * A * ((d : ℝ) * MB * B)) (by positivity)
      (k := fun m y => ρ (τ m) y * (Torus.matVec D.M.transpose (gradient (u m) y)) j)
      (k₀ := fun y => ρ τ₀ y * (Torus.matVec D.M.transpose (gradient u₀ y)) j)
      (fun m => s55m_nl_decay hMB hMB0 hA hB (hρ2 _ (hτ m)) (hu m).1 (hu m).2 j)
      (s55m_nl_decay hMB hMB0 hA hB (hρ2 _ hτ₀) hu₀.1 hu₀.2 j) (fun y => ?_) x j
    refine (hρt y).mul ?_
    simp only [HRS.Whole.Q09B.q09b_matVec_apply]
    refine tendsto_finsetSum _ fun i _ => Tendsto.const_mul _ ?_
    exact ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp (s55m_grad_tendsto (h1 y))
  exact ((hlap.const_mul _).add (hdrift.inner hgrad)).sub hnl

/-! ### Coefficient data of a `WholeSetup` -/

theorem s55m_rho_data (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ (∀ t ∈ Set.Icc (0 : ℝ) b.T, RgDecay 3 (fun _ => A) (S.ρ N t)) ∧
      ∀ y, ContinuousOn (fun t => S.ρ N t y) (Set.Icc (0 : ℝ) b.T) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg b.k
  have hL := hb.hL
  have hs0 := hb.hs0
  have hdL : (d : ℝ) + 3 ≤ b.L := by linarith
  have hn : 3 ≤ b.k + 6 + ⌈(d : ℝ) / 2⌉₊ := by omega
  obtain ⟨Λ', hρ⟩ := s55f_coeffHyp b hb S N
  set Λ3 : ℝ := (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max b.Λ 0 with hΛ3
  have hreg3 : ∀ t ∈ Set.Icc (0 : ℝ) b.T, MemCb 3 (S.ρ N t) ∧
      weightedSupE 3 ((d : ℝ) + 3) (S.ρ N t) < ⊤ ∧
      HRS.cbNorm 3 (S.ρ N t) + (weightedSupE 3 ((d : ℝ) + 3) (S.ρ N t)).toReal ≤ Λ3 := fun t ht =>
    s55_regular_slice hn hdL (S.dens N t ht).1 (S.dens N t ht).2
  set A : ℝ := (d : ℝ) ^ 3 * max Λ3 0 * 2 ^ ((d : ℝ) + 3) with hAdef
  have hA : 0 ≤ A := by positivity
  have hdec : ∀ r ∈ Set.Icc (0 : ℝ) b.T, RgDecay 3 (fun _ => A) (S.ρ N r) := by
    intro r hr
    have hcb := hreg3 r hr
    have hcb0 : 0 ≤ HRS.cbNorm 3 (S.ρ N r) :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    exact rg_rho_decay hd1 (r := 3) (Λ := max Λ3 0) hcb.1 hcb.2.1
      (by linarith [hcb.2.2, le_max_left Λ3 0])
  refine ⟨A, hA, hdec, fun y => ?_⟩
  have hparts := fun r hr => rg_decay_parts (n := 3) (by omega) (a := fun _ => A)
    (fun _ => hA) (hdec r hr)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    linarith
  have hdiff : ∀ r ∈ Set.Icc (0 : ℝ) b.T, Differentiable ℝ (S.ρ N r) := fun r hr =>
    ((hparts r hr).1).differentiable (by norm_num)
  have h1' : ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ y, ‖fderiv ℝ (S.ρ N r) y‖ ≤ A := fun r hr y =>
    ((hparts r hr).2.2.1 y).trans (by
      calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ A * 1 := mul_le_mul_of_nonneg_left (hw y) hA
        _ = A := mul_one _)
  have hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * S.ρ N r x) (Set.Icc (0 : ℝ) b.T) := by
    intro ψ hψ hcs
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hψ.continuous
    exact hρ.cont ψ hψ.continuous ⟨C, fun x => by simpa using hC x⟩
  exact s55_pointwise hA hweak hdiff h1' y

/-! ### Uniform bound of the generator -/

theorem s55m_gen_rgW (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc (0 : ℝ) b.T, ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B → ContDiff ℝ 4 u →
      (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
      RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW (S.coeff N) τ u) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  obtain ⟨A, hA0, hdec, -⟩ := s55m_rho_data b hb S N
  obtain ⟨ΛV, G₀, hV⟩ := s55f_vhyp_quadV hb.hQ b.c 2
  have hMB0 : 0 ≤ ∑ i, ∑ j, |b.M i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hV' : VHypRd (1 + 1) (max ΛV 0) (max G₀ 0) (quadV b.Q b.c) :=
    rg_VHyp_mono hV (by norm_num) (le_max_left _ _) (le_max_left _ _)
  have hν := (S.hinvβ N)
  refine ⟨rgK d b.s (∑ i, ∑ j, |b.M i j|) (max ΛV 0) (max G₀ 0) b.νstar A 1,
    rgK_nonneg hb.hs0 hMB0 (le_max_right _ _) (le_max_right _ _) hb.hν hA0 1, fun τ hτ B u hB hu hub => ?_⟩
  exact rg_gen_core hd1 hb.hs0 hb.hsd (k := 1) le_rfl hMB0 (le_max_right _ _) (le_max_right _ _) hA0 hB
    (D := S.dyn N) rfl (s55f_matBound _) hV' hν.1 hν.2 (hdec τ hτ) (by norm_num; exact hu)
    (fun n hn x => hub n (by omega) x)

end HRS.MS.Go
