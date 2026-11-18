import HRS.MP.SelfSimSpec
import HRS.Whole.AppendixAAdjoint
import HRS.Stochastic.EmpiricalIto

/-!
# MPSSP3: packets P7 (drift regularity) and P3 (forward equation) of the S.A.28 plan

Proofs of `HRS.MP.SelfSim.ss_P7_drift_regular` and `HRS.MP.SelfSim.ss_P3_fke` (see `HRS/MP/SelfSimSpec.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP3

variable {d : ℕ}

/-! ### P7: regularity of the drifts -/

theorem ssp3_gradient_measurable (f : Euc d → ℝ) : Measurable (gradient f) := by
  have h : gradient f = fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f x) := rfl
  rw [h]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem ssp3_rkg_measurable (s : ℝ) : Measurable (rieszKernelGrad d s) :=
  ssp3_gradient_measurable _

theorem ssp3_rkg_continuousAt (s : ℝ) {z : Euc d} (hz : z ≠ 0) :
    ContinuousAt (rieszKernelGrad d s) z := by
  have hev : rieszKernelGrad d s =ᶠ[𝓝 z] fun x : Euc d => (q09_c s * ‖x‖ ^ (-s - 2)) • x := by
    filter_upwards [isOpen_ne.mem_nhds hz] with x hx
    ext i
    rw [q09_rkg_eq s i hx]
    simp [q09_H, mul_assoc]
  refine ContinuousAt.congr ?_ hev.symm
  have h1 : ContinuousAt (fun x : Euc d => ‖x‖ ^ (-s - 2)) z :=
    (continuousAt_id.norm).rpow_const (Or.inl (norm_ne_zero_iff.2 hz))
  exact (h1.const_mul _).smul continuousAt_id

theorem ssp3_gradient_zero : gradient (fun _ : Euc d => (0 : ℝ)) = fun _ => 0 := by
  funext x; simp [gradient]

theorem ssp3_matVec_neg_one_continuous : Continuous (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)) :=
  LinearMap.continuous_of_finiteDimensional _

/-- The pair-force map `(r, Ξ) ↦ ∇g(Ξ_i - Ξ_j)` is measurable. -/
theorem ssp3_pair_measurable (s : ℝ) (N : ℕ) (i j : Fin N) :
    Measurable (fun p : ℝ × EucConfig d N => rieszKernelGrad d s (p.2 i - p.2 j)) :=
  (ssp3_rkg_measurable s).comp
    (((measurable_pi_apply i).comp measurable_snd).sub ((measurable_pi_apply j).comp measurable_snd))

theorem ssp3_pair_continuousAt (s : ℝ) (N : ℕ) {i j : Fin N} {p : ℝ × EucConfig d N}
    (h : p.2 i ≠ p.2 j) :
    ContinuousAt (fun p : ℝ × EucConfig d N => rieszKernelGrad d s (p.2 i - p.2 j)) p := by
  have hg := ssp3_rkg_continuousAt s (sub_ne_zero.2 h)
  have hf : ContinuousAt (fun p : ℝ × EucConfig d N => p.2 i - p.2 j) p :=
    (((continuous_apply i).comp continuous_snd).sub
      ((continuous_apply j).comp continuous_snd)).continuousAt
  exact ContinuousAt.comp (f := fun p : ℝ × EucConfig d N => p.2 i - p.2 j) (x := p) hg hf

theorem ssp3_not_collision {N : ℕ} {Ξ : EucConfig d N} (h : Ξ ∈ (eucCollisionSet d N)ᶜ) {i j : Fin N}
    (hij : i ≠ j) : Ξ i ≠ Ξ j := fun he => h ⟨i, j, hij, he⟩

theorem ssp3_ssDrift_measurable (s : ℝ) (N : ℕ) :
    Measurable (fun p : ℝ × EucConfig d N => ssDrift d s N p.1 p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold ssDrift
  have h1 : Measurable (fun p : ℝ × EucConfig d N => aSelfSim s p.1 / N) := by
    unfold aSelfSim; fun_prop
  have h2 : Measurable (fun p : ℝ × EucConfig d N => ∑ j ∈ Finset.univ.erase i,
      rieszKernelGrad d s (p.2 i - p.2 j)) :=
    Finset.measurable_sum _ fun j _ => ssp3_pair_measurable s N i j
  have h3 : Measurable (fun p : ℝ × EucConfig d N => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have h4 := h1.smul h2
  have h5 := h3.const_smul (1 / 2 : ℝ)
  exact (h4.add h5).neg

theorem ssp3_ssDrift_continuousOn (s : ℝ) (N : ℕ) (S : ℝ) :
    ContinuousOn (fun p : ℝ × EucConfig d N => ssDrift d s N p.1 p.2)
      (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_pi.2 fun i => ?_
  unfold ssDrift
  have h1 : ContinuousAt (fun p : ℝ × EucConfig d N => aSelfSim s p.1 / N) p := by
    unfold aSelfSim; fun_prop
  have h2 : ContinuousAt (fun p : ℝ × EucConfig d N => ∑ j ∈ Finset.univ.erase i,
      rieszKernelGrad d s (p.2 i - p.2 j)) p :=
    tendsto_finsetSum _ fun j hj =>
      ssp3_pair_continuousAt s N (ssp3_not_collision hp.2 (Finset.ne_of_mem_erase hj).symm)
  have h3 : ContinuousAt (fun p : ℝ × EucConfig d N => p.2 i) p :=
    ((continuous_apply i).comp continuous_snd).continuousAt
  have h4 := h1.smul h2
  have h5 := h3.const_smul (1 / 2 : ℝ)
  exact (h4.add h5).neg

theorem ssp3_partDrift_eq (s invβ : ℝ) (N : ℕ) (Ξ : EucConfig d N) (i : Fin N) :
    particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) Ξ i =
      (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i,
        Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (rieszKernelGrad d s (Ξ i - Ξ j)) := by
  have := congrFun ssp3_gradient_zero (Ξ i)
  simp only [particleDriftW, this, sub_zero]

theorem ssp3_partDrift_measurable (s invβ : ℝ) (N : ℕ) :
    Measurable (fun p : ℝ × EucConfig d N => fun i : Fin N =>
        particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) p.2 i) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [ssp3_partDrift_eq]
  have h : Measurable (fun p : ℝ × EucConfig d N => ∑ j ∈ Finset.univ.erase i,
      Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (rieszKernelGrad d s (p.2 i - p.2 j))) :=
    Finset.measurable_sum _ fun j _ =>
      ssp3_matVec_neg_one_continuous.measurable.comp (ssp3_pair_measurable s N i j)
  exact h.const_smul (1 / (N : ℝ))

theorem ssp3_partDrift_continuousOn (s invβ : ℝ) (N : ℕ) (S : ℝ) :
    ContinuousOn (fun p : ℝ × EucConfig d N => fun i : Fin N =>
        particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) p.2 i)
      (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ) := by
  intro p hp
  refine ContinuousAt.continuousWithinAt ?_
  refine continuousAt_pi.2 fun i => ?_
  simp only [ssp3_partDrift_eq]
  have h : ContinuousAt (fun p : ℝ × EucConfig d N => ∑ j ∈ Finset.univ.erase i,
      Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) (rieszKernelGrad d s (p.2 i - p.2 j))) p :=
    tendsto_finsetSum _ fun j hj =>
      ssp3_matVec_neg_one_continuous.continuousAt.comp
        (ssp3_pair_continuousAt s N (ssp3_not_collision hp.2 (Finset.ne_of_mem_erase hj).symm))
  exact h.const_smul (1 / (N : ℝ))

theorem ss_P7_drift_regular_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ) (invβ : ℝ) :
    (Measurable (fun p : ℝ × EucConfig d N => ssDrift d s N p.1 p.2) ∧
      ∀ S : ℝ, ContinuousOn (fun p : ℝ × EucConfig d N => ssDrift d s N p.1 p.2)
        (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ)) ∧
    (Measurable (fun p : ℝ × EucConfig d N => fun i : Fin N =>
        particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) p.2 i) ∧
      ∀ S : ℝ, ContinuousOn (fun p : ℝ × EucConfig d N => fun i : Fin N =>
        particleDriftW (⟨s, -1, fun _ => 0, invβ⟩ : WholeDyn d) p.2 i)
        (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ)) :=
  ⟨⟨ssp3_ssDrift_measurable s N, ssp3_ssDrift_continuousOn s N⟩,
    ⟨ssp3_partDrift_measurable s invβ N, ssp3_partDrift_continuousOn s invβ N⟩⟩

example := (@ss_P7_drift_regular_proof : type_of% @HRS.MP.SelfSim.ss_P7_drift_regular)

/-! ### P3: forward equation for the laws of an additive-noise solution -/

section P3

variable {N : ℕ}

/-- The noise directions `σ_k = √(2ν) e_k`. -/
def ssp3_sigma (d N : ℕ) (ν : ℝ) (k : Fin N × Fin d) : EucConfig d N :=
  Real.sqrt (2 * ν) • configBasis d N k

/-- The Itô drift of `Φ(r, Y_r)` as a function of `(r, x)`: `∂_rΦ + DΦ[b] + ½ ∑_k D²Φ[σ_k, σ_k]`. -/
def ssp3_G (ν S : ℝ) (Φ : ℝ → EucConfig d N → ℝ) (b : ℝ → EucConfig d N → EucConfig d N)
    (s : ℝ) (x : EucConfig d N) : ℝ :=
  derivWithin (fun r => Φ r x) (Set.Icc 0 S) s + fderiv ℝ (Φ s) x (b s x) +
    (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (Φ s)) x (ssp3_sigma d N ν k) (ssp3_sigma d N ν k)

theorem ssp3_fderiv_eq_zero {K : Set (EucConfig d N)} (hK : IsClosed K) {Φ : ℝ → EucConfig d N → ℝ}
    (hsupp : ∀ r x, x ∉ K → Φ r x = 0) (s : ℝ) {x : EucConfig d N} (hx : x ∉ K) :
    fderiv ℝ (Φ s) x = 0 := by
  have hev : Φ s =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with z hz
    exact hsupp s z hz
  rw [hev.fderiv_eq]
  simp

theorem ssp3_fderiv2_eq_zero {K : Set (EucConfig d N)} (hK : IsClosed K)
    {Φ : ℝ → EucConfig d N → ℝ} (hsupp : ∀ r x, x ∉ K → Φ r x = 0) (s : ℝ)
    {x : EucConfig d N} (hx : x ∉ K) : fderiv ℝ (fderiv ℝ (Φ s)) x = 0 := by
  have hev : fderiv ℝ (Φ s) =ᶠ[𝓝 x] fun _ => (0 : EucConfig d N →L[ℝ] ℝ) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with z hz
    exact ssp3_fderiv_eq_zero hK hsupp s hz
  rw [hev.fderiv_eq]
  simp

theorem ssp3_derivWithin_eq_zero {K : Set (EucConfig d N)} {Φ : ℝ → EucConfig d N → ℝ}
    (hsupp : ∀ r x, x ∉ K → Φ r x = 0) (A : Set ℝ) (s : ℝ) {x : EucConfig d N} (hx : x ∉ K) :
    derivWithin (fun r => Φ r x) A s = 0 := by
  have : (fun r => Φ r x) = fun _ => (0 : ℝ) := funext fun r => hsupp r x hx
  rw [this]
  simp

theorem ssp3_G_eq_zero {K : Set (EucConfig d N)} (hK : IsClosed K) {Φ : ℝ → EucConfig d N → ℝ}
    (hsupp : ∀ r x, x ∉ K → Φ r x = 0) (ν S : ℝ) (b : ℝ → EucConfig d N → EucConfig d N) (s : ℝ)
    {x : EucConfig d N} (hx : x ∉ K) : ssp3_G ν S Φ b s x = 0 := by
  unfold ssp3_G
  rw [ssp3_derivWithin_eq_zero hsupp _ s hx, ssp3_fderiv_eq_zero hK hsupp s hx,
    ssp3_fderiv2_eq_zero hK hsupp s hx]
  simp

/-- A function continuous on `[0,S] × K` (`K` compact) and zero off `K` is bounded on `[0,S] × E`. -/
theorem ssp3_bdd_of_supp {α : Type*} [NormedAddCommGroup α] {S : ℝ} {K : Set (EucConfig d N)}
    (hK : IsCompact K) {f : ℝ → EucConfig d N → α}
    (hf : ContinuousOn (fun p : ℝ × EucConfig d N => f p.1 p.2) (Set.Icc 0 S ×ˢ K))
    (hz : ∀ s x, x ∉ K → f s x = 0) : ∃ C : ℝ, ∀ s ∈ Set.Icc 0 S, ∀ x, ‖f s x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hf
  refine ⟨max C 0, fun s hs x => ?_⟩
  by_cases hx : x ∈ K
  · exact (hC (s, x) ⟨hs, hx⟩).trans (le_max_left _ _)
  · rw [hz s x hx, norm_zero]; exact le_max_right _ _

/-- Boundedness of the Itô drift function on `[0,S] × E`. -/
theorem ssp3_G_bdd {ν S : ℝ} {Φ : ℝ → EucConfig d N → ℝ} {b : ℝ → EucConfig d N → EucConfig d N}
    (hbc : ContinuousOn (fun p : ℝ × EucConfig d N => b p.1 p.2)
      (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ))
    (hΦ : IsC12On S Set.univ Φ) {K : Set (EucConfig d N)} (hK : IsCompact K)
    (hdisj : Disjoint K (eucCollisionSet d N)) (hsupp : ∀ r x, x ∉ K → Φ r x = 0) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc 0 S, ∀ x, ‖ssp3_G ν S Φ b s x‖ ≤ C := by
  refine ssp3_bdd_of_supp hK ?_ (fun s x hx => ssp3_G_eq_zero hK.isClosed hsupp ν S b s hx)
  have hKc : K ⊆ (eucCollisionSet d N)ᶜ := Set.disjoint_left.1 hdisj
  have hsub : Set.Icc 0 S ×ˢ K ⊆ Set.Icc 0 S ×ˢ (Set.univ : Set (EucConfig d N)) :=
    Set.prod_mono subset_rfl (Set.subset_univ _)
  have hb := hbc.mono (Set.prod_mono (subset_refl (Set.Icc (0 : ℝ) S)) hKc)
  have h1 := hΦ.cont_deriv.mono hsub
  have h2 := (hΦ.cont_fderiv.mono hsub).clm_apply hb
  have h3 : ContinuousOn (fun p : ℝ × EucConfig d N => (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (Φ p.1)) p.2 (ssp3_sigma d N ν k) (ssp3_sigma d N ν k))
      (Set.Icc 0 S ×ˢ K) := by
    refine continuousOn_const.mul (continuousOn_finsetSum _ fun k _ => ?_)
    exact (((hΦ.cont_fderiv₂.mono hsub).clm_apply continuousOn_const).clm_apply continuousOn_const)
  exact (h1.add h2).add h3

theorem ssp3_noise_sum (ν : ℝ) (c : Fin N × Fin d → ℝ) (i : Fin N) (j : Fin d) :
    (∑ k : Fin N × Fin d, c k • ssp3_sigma d N ν k) i j = Real.sqrt (2 * ν) * c (i, j) := by
  simp [ssp3_sigma, configBasis, Finset.sum_apply, Pi.single_apply, Fintype.sum_prod_type]
  ring

/-- Measurability of the clamped Itô drift function. -/
theorem ssp3_Gcl_measurable {ν S : ℝ} (hS : 0 ≤ S) {Φ : ℝ → EucConfig d N → ℝ}
    {b : ℝ → EucConfig d N → EucConfig d N}
    (hbm : Measurable fun p : ℝ × EucConfig d N => b p.1 p.2) (hΦ : IsC12On S Set.univ Φ) :
    Measurable (fun q : ℝ × EucConfig d N => ssp3_G ν S Φ b (clampTI S q.1) q.2) := by
  have hq : Continuous (fun q : ℝ × EucConfig d N => (clampTI S q.1, q.2)) :=
    ((continuous_clampTI S).comp continuous_fst).prodMk continuous_snd
  have hmem : ∀ q : ℝ × EucConfig d N,
      (clampTI S q.1, q.2) ∈ Set.Icc 0 S ×ˢ (Set.univ : Set (EucConfig d N)) :=
    fun q => ⟨clampTI_mem hS q.1, Set.mem_univ _⟩
  have hdt : Continuous (fun q : ℝ × EucConfig d N =>
      derivWithin (fun r => Φ r q.2) (Set.Icc 0 S) (clampTI S q.1)) :=
    ContinuousOn.comp_continuous hΦ.cont_deriv hq hmem
  have hfd : Continuous (fun q : ℝ × EucConfig d N => fderiv ℝ (Φ (clampTI S q.1)) q.2) :=
    ContinuousOn.comp_continuous hΦ.cont_fderiv hq hmem
  have hfd2 : Continuous (fun q : ℝ × EucConfig d N =>
      fderiv ℝ (fderiv ℝ (Φ (clampTI S q.1))) q.2) :=
    ContinuousOn.comp_continuous hΦ.cont_fderiv₂ hq hmem
  have hbq : Measurable (fun q : ℝ × EucConfig d N => b (clampTI S q.1) q.2) :=
    hbm.comp (((continuous_clampTI S).measurable.comp measurable_fst).prodMk measurable_snd)
  have h4 : Measurable (fun q : ℝ × EucConfig d N =>
      fderiv ℝ (Φ (clampTI S q.1)) q.2 (b (clampTI S q.1) q.2)) :=
    (continuous_fst.clm_apply continuous_snd).measurable.comp (hfd.measurable.prodMk hbq)
  have h5 : Measurable (fun q : ℝ × EucConfig d N => (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ (Φ (clampTI S q.1))) q.2 (ssp3_sigma d N ν k) (ssp3_sigma d N ν k)) := by
    refine measurable_const.mul (Finset.measurable_sum _ fun k _ => ?_)
    have ha : Measurable (fun q : ℝ × EucConfig d N =>
        fderiv ℝ (fderiv ℝ (Φ (clampTI S q.1))) q.2 (ssp3_sigma d N ν k)) :=
      hfd2.measurable.apply_continuousLinearMap (ssp3_sigma d N ν k)
    exact ha.apply_continuousLinearMap (ssp3_sigma d N ν k)
  exact (hdt.measurable.add h4).add h5

/-- The Itô drift function is the integrand of `SolvesFKEW`, on `[0,S]`. -/
theorem ssp3_G_eq_integrand {ν S : ℝ} (hν : 0 ≤ ν) (hS : 0 < S) {Φ : ℝ → EucConfig d N → ℝ}
    (hΦ : ContDiff ℝ 2 (fun p : ℝ × EucConfig d N => Φ p.1 p.2))
    (b : ℝ → EucConfig d N → EucConfig d N) {r : ℝ} (hr : r ∈ Set.Icc 0 S) (x : EucConfig d N) :
    deriv (fun r' => Φ r' x) r +
        ν * ∑ k : Fin N × Fin d, iteratedFDeriv ℝ 2 (Φ r) x ![configBasis d N k, configBasis d N k] +
        fderiv ℝ (Φ r) x (b r x) = ssp3_G ν S Φ b r x := by
  have hdiff : DifferentiableAt ℝ (fun r' => Φ r' x) r :=
    ((hΦ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by norm_num)) r
  have hd : derivWithin (fun r' => Φ r' x) (Set.Icc 0 S) r = deriv (fun r' => Φ r' x) r :=
    hdiff.derivWithin (uniqueDiffOn_Icc hS r hr)
  have hσ : ∀ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ (Φ r)) x (ssp3_sigma d N ν k)
      (ssp3_sigma d N ν k) = (2 * ν) * iteratedFDeriv ℝ 2 (Φ r) x
        ![configBasis d N k, configBasis d N k] := by
    intro k
    have h2 : Real.sqrt (2 * ν) * Real.sqrt (2 * ν) = 2 * ν :=
      Real.mul_self_sqrt (by linarith)
    rw [iteratedFDeriv_two_apply]
    simp only [ssp3_sigma, map_smul, smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    linear_combination (fderiv ℝ (fderiv ℝ (Φ r)) x (configBasis d N k) (configBasis d N k)) * h2
  unfold ssp3_G
  rw [hd, Finset.sum_congr rfl (fun k _ => hσ k), ← Finset.mul_sum]
  ring

theorem ss_P3_fke_proof {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    {ν : ℝ} (hν : 0 ≤ ν) {S : ℝ} (hS : 0 < S) {b : ℝ → EucConfig d N → EucConfig d N}
    (hbm : Measurable fun p : ℝ × EucConfig d N => b p.1 p.2)
    (hbc : ContinuousOn (fun p : ℝ × EucConfig d N => b p.1 p.2)
      (Set.Icc 0 S ×ˢ (eucCollisionSet d N)ᶜ))
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N} (hY : SSAddSol P ν b S ℱ W' W Y) :
    SolvesFKEW ν b S (fun r => law P (Y (Real.toNNReal r))) := by
  intro Φ hΦ
  have hS0 : 0 ≤ S := hS.le
  obtain ⟨Tp, hTp, hzero⟩ := hΦ.time_support
  obtain ⟨K, hK, hdisj, hsupp⟩ := hΦ.space_support
  have hΦc : IsC12On S Set.univ Φ := IsC12On.of_contDiff S _ Φ hΦ.smooth
  obtain ⟨Cf, hCf⟩ := ssp3_G_bdd (ν := ν) hbc hΦc hK hdisj hsupp
  have hsubU : Set.Icc 0 S ×ˢ K ⊆ Set.Icc 0 S ×ˢ (Set.univ : Set (EucConfig d N)) :=
    Set.prod_mono subset_rfl (Set.subset_univ _)
  obtain ⟨C1, hC1⟩ := ssp3_bdd_of_supp (S := S) hK (f := fun s x => fderiv ℝ (Φ s) x)
    (hΦc.cont_fderiv.mono hsubU) (fun s x hx => ssp3_fderiv_eq_zero hK.isClosed hsupp s hx)
  obtain ⟨C0, hC0⟩ := ssp3_bdd_of_supp (S := S) hK (f := Φ) (hΦc.cont.mono hsubU)
    (fun s x hx => by simpa using hsupp s x hx)
  have hbrown := hY.filtered.brownian
  set σ : Fin N × Fin d → EucConfig d N := ssp3_sigma d N ν with hσdef
  set bp : ℝ≥0 → Ω → EucConfig d N := fun τ ζ => b (τ : ℝ) (Y τ ζ) with hbpdef
  have hXmeas : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le t) le_rfl
  have hX₀ : ∀ t : ℝ, Measurable[ℱ t] (Y 0) := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · exact (hY.filtered.adapted 0).mono (ℱ.mono (by simpa using hs)) le_rfl
    · have h := hY.filtered.progressive.adapted s
      have e : ofNNRealTime Y s = Y 0 := by
        funext ζ
        simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos hs.le]
      rw [e] at h
      exact h
  have hbprog : IsProgressive ℱ (ofNNRealTime bp) := by
    have h := isProgressive_comp_measurable' (ofNNRealTime Y) hY.filtered.progressive
      (fun s x => b ((Real.toNNReal s : ℝ≥0) : ℝ) x)
      (hbm.comp ((measurable_fst.real_toNNReal.coe_nnreal_real).prodMk measurable_snd))
    exact h
  have hτ : ((Real.toNNReal S : ℝ≥0) : ℝ) = S := Real.coe_toNNReal S hS0
  -- the integrated equation in vector form
  have hbint : ∀ᵐ ζ ∂P, IntegrableOn (fun s : ℝ => bp (Real.toNNReal s) ζ) (Set.Icc 0 S) := by
    filter_upwards [hY.eqn] with ζ h
    have hi := (h (Real.toNNReal S) (le_of_eq hτ)).1
    rw [hτ] at hi
    refine integrable_pi_iff.2 fun i => ?_
    refine (hi i).congr_fun (fun s hs => ?_) measurableSet_Icc
    simp [hbpdef, Real.coe_toNNReal _ hs.1]
  have hXeq : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ S →
      Y t ζ = Y 0 ζ + (∫ s in Set.Icc (0 : ℝ) t, bp (Real.toNNReal s) ζ) +
        ∑ k, (W' t ζ k - W' 0 ζ k) • σ k := by
    filter_upwards [hY.eqn, hY.filtered.coords] with ζ h hc t ht
    obtain ⟨hint, heq⟩ := h t ht
    have hcongr : ∀ i, ∫ s in Set.Icc (0 : ℝ) t, bp (Real.toNNReal s) ζ i =
        ∫ s in Set.Icc (0 : ℝ) t, b s (Y (Real.toNNReal s) ζ) i := fun i =>
      setIntegral_congr_fun measurableSet_Icc fun s hs => by
        simp [hbpdef, Real.coe_toNNReal _ hs.1]
    have hint' : ∀ i, Integrable (fun s => bp (Real.toNNReal s) ζ i)
        (volume.restrict (Set.Icc (0 : ℝ) t)) := fun i =>
      (hint i).congr_fun (fun s hs => by simp [hbpdef, Real.coe_toNNReal _ hs.1]) measurableSet_Icc
    ext i j
    rw [Pi.add_apply, Pi.add_apply, eval_integral hint' i, hcongr i]
    rw [heq i]
    have hn : ((∑ k : Fin N × Fin d, (W' t ζ k - W' 0 ζ k) • ssp3_sigma d N ν k) i).ofLp j =
        Real.sqrt (2 * ν) * (W' t ζ (i, j) - W' 0 ζ (i, j)) :=
      ssp3_noise_sum ν (fun k => W' t ζ k - W' 0 ζ k) i j
    simp only [hσdef, PiLp.add_apply]
    rw [hn]
    simp [hc]
  -- Itô's formula for `Φ(r, Y_r)`
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hbrown (T := S) hS0 Φ hΦc σ Y hXmeas hX₀ bp
    hbprog hbint hXeq
  -- the integrand of the martingale term is bounded and progressive
  have hΨL2 : IsProgressiveL2 P ℱ
      (itoIntegrand S Set.univ Φ (ofNNRealTime Y) (fun _ _ => σ)) := by
    have hk : ∀ k : Fin N × Fin d, IsProgressive ℱ
        (fun s ζ => itoIntegrand S Set.univ Φ (ofNNRealTime Y) (fun _ _ => σ) s ζ k) := by
      intro k
      have hq : Continuous (fun q : ℝ × EucConfig d N => (clampTI S q.1, q.2)) :=
        ((continuous_clampTI S).comp continuous_fst).prodMk continuous_snd
      have hc : Continuous (fun q : ℝ × EucConfig d N =>
          fderiv ℝ (Φ (clampTI S q.1)) q.2 (σ k)) :=
        (ContinuousOn.comp_continuous hΦc.cont_fderiv hq
          (fun q => ⟨clampTI_mem hS0 q.1, Set.mem_univ _⟩)).clm_apply continuous_const
      have hm : Measurable (Function.uncurry (fun (s : ℝ) (y : EucConfig d N) =>
          if s ∈ Set.Icc 0 S then fderiv ℝ (Φ (clampTI S s)) y (σ k) else 0)) :=
        Measurable.ite (measurableSet_Icc.preimage measurable_fst) hc.measurable measurable_const
      have h := isProgressive_comp_measurable' (ofNNRealTime Y) hY.filtered.progressive
        (fun (s : ℝ) (y : EucConfig d N) =>
          if s ∈ Set.Icc 0 S then fderiv ℝ (Φ (clampTI S s)) y (σ k) else 0) hm
      have e : (fun s ζ => itoIntegrand S Set.univ Φ (ofNNRealTime Y) (fun _ _ => σ) s ζ k) =
          fun s ζ => if s ∈ Set.Icc 0 S then
            fderiv ℝ (Φ (clampTI S s)) (ofNNRealTime Y s ζ) (σ k) else 0 := by
        funext s ζ
        unfold itoIntegrand
        by_cases hs : s ∈ Set.Icc 0 S
        · simp [Set.indicator, hs, clampTI_of_mem hs]
        · simp [Set.indicator, hs]
      rw [e]
      exact h
    refine IsProgressiveL2.of_bounded P (isProgressive_pi hk)
      (max C1 0 * ∑ j : Fin N × Fin d, ‖σ j‖) ?_
    intro s ζ k
    unfold itoIntegrand
    by_cases hs : s ∈ Set.Icc 0 S
    · simp only [Set.indicator, hs, if_true, Set.mem_univ, Set.mem_setOf_eq]
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ (Φ s) (ofNNRealTime Y s ζ) (σ k)‖
          ≤ ‖fderiv ℝ (Φ s) (ofNNRealTime Y s ζ)‖ * ‖σ k‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ max C1 0 * ‖σ k‖ :=
            mul_le_mul_of_nonneg_right ((hC1 s hs _).trans (le_max_left _ _)) (norm_nonneg _)
        _ ≤ max C1 0 * ∑ j : Fin N × Fin d, ‖σ j‖ :=
            mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => norm_nonneg (σ j))
              (Finset.mem_univ k)) (le_max_right _ _)
    · simp only [Set.indicator, hs, if_false, abs_zero]
      exact mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  -- the sampled Itô drift
  set Gs : ℝ → Ω → ℝ := fun s ζ => ssp3_G ν S Φ b (clampTI S s) (Y (Real.toNNReal s) ζ) with hGsdef
  have hcore : ∀ᵐ ζ ∂P, Φ 0 (Y 0 ζ) + (∫ s in Set.Icc (0 : ℝ) S, Gs s ζ) +
      itoIntegral P ℱ W' (itoIntegrand S Set.univ Φ (ofNNRealTime Y) (fun _ _ => σ)) S ζ = 0 := by
    filter_upwards [hito, localItoIntegral_eq_itoIntegral hbrown hΨL2] with ζ hζ hloc
    have h := hζ.2 (Real.toNNReal S) (le_of_eq hτ)
    rw [hτ] at h
    have hL : Φ S (Y (Real.toNNReal S) ζ) = 0 := hzero S hTp.le _
    have hint2 : ∫ s in Set.Icc (0 : ℝ) S, itoDrift S Φ (ofNNRealTime Y) (ofNNRealTime bp)
        (fun _ _ => σ) s ζ = ∫ s in Set.Icc (0 : ℝ) S, Gs s ζ := by
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      simp only [itoDrift, ssp3_G, hGsdef, ofNNRealTime_apply, hbpdef, clampTI_of_mem hs,
        Real.coe_toNNReal _ hs.1]
      rfl
    rw [hL, hint2, hloc S] at h
    linarith
  have hMLp := memLp_two_itoIntegral hbrown hΨL2 S
  have hMint := integral_itoIntegral hbrown hΨL2 S
  -- integrability
  have : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) S)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hGcl := ssp3_Gcl_measurable (ν := ν) hS0 hbm hΦc
  have hprodm : Measurable (fun p : ℝ × Ω => Gs p.1 p.2) :=
    hGcl.comp (measurable_fst.prodMk (measurable_of_progressive hY.filtered.progressive))
  have hprodint : Integrable (fun p : ℝ × Ω => Gs p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) S)).prod P) :=
    Integrable.of_bound hprodm.aestronglyMeasurable Cf
      (ae_of_all _ fun p => hCf _ (clampTI_mem hS0 p.1) _)
  have hIint : Integrable (fun ζ => ∫ s in Set.Icc (0 : ℝ) S, Gs s ζ) P :=
    hprodint.integral_prod_right
  have hm0 : Measurable (fun x : EucConfig d N => Φ 0 x) :=
    (hΦ.smooth.continuous.comp (continuous_const.prodMk continuous_id)).measurable
  have hΦ0int : Integrable (fun ζ => Φ 0 (Y 0 ζ)) P :=
    Integrable.of_bound ((hm0.comp (hXmeas 0)).aestronglyMeasurable) C0
      (ae_of_all _ fun ζ => hC0 0 ⟨le_rfl, hS0⟩ _)
  have hMi : Integrable (itoIntegral P ℱ W'
      (itoIntegrand S Set.univ Φ (ofNNRealTime Y) (fun _ _ => σ)) S) P :=
    hMLp.integrable one_le_two
  -- Fubini and the identification with the laws
  have hIeq : ∫ ζ, (∫ s in Set.Icc (0 : ℝ) S, Gs s ζ) ∂P =
      ∫ r in Set.Icc (0 : ℝ) S, ∫ x, (deriv (fun r' => Φ r' x) r +
        ν * ∑ k : Fin N × Fin d, iteratedFDeriv ℝ 2 (Φ r) x ![configBasis d N k, configBasis d N k] +
        fderiv ℝ (Φ r) x (b r x)) ∂(law P (Y (Real.toNNReal r))) := by
    have hswap := integral_integral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) S)) (ν := P)
      (f := fun s ζ => Gs s ζ) hprodint
    rw [← hswap]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hg : Measurable (fun x : EucConfig d N => ssp3_G ν S Φ b r x) := by
      have h2 : Measurable (fun x : EucConfig d N => ssp3_G ν S Φ b (clampTI S r) x) :=
        hGcl.comp (measurable_const.prodMk measurable_id)
      rwa [clampTI_of_mem hr] at h2
    have e : ∀ x : EucConfig d N, deriv (fun r' => Φ r' x) r +
        ν * ∑ k : Fin N × Fin d, iteratedFDeriv ℝ 2 (Φ r) x ![configBasis d N k, configBasis d N k] +
        fderiv ℝ (Φ r) x (b r x) = ssp3_G ν S Φ b r x := fun x =>
      ssp3_G_eq_integrand hν hS hΦ.smooth b hr x
    simp only [e]
    rw [law, integral_map (hXmeas _).aemeasurable hg.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun ζ => ?_)
    simp only [hGsdef, clampTI_of_mem hr]
  have hLHS : ∫ x, Φ 0 x ∂(law P (Y (Real.toNNReal 0))) = ∫ ζ, Φ 0 (Y 0 ζ) ∂P := by
    rw [law, integral_map (hXmeas _).aemeasurable hm0.aestronglyMeasurable, Real.toNNReal_zero]
  have hzeroint : ∫ ζ, (Φ 0 (Y 0 ζ) + (∫ s in Set.Icc (0 : ℝ) S, Gs s ζ) +
      itoIntegral P ℱ W' (itoIntegrand S Set.univ Φ (ofNNRealTime Y) (fun _ _ => σ)) S ζ) ∂P = 0 := by
    rw [integral_congr_ae hcore]
    simp
  have hA : Integrable (fun ζ => Φ 0 (Y 0 ζ) + ∫ s in Set.Icc (0 : ℝ) S, Gs s ζ) P :=
    hΦ0int.add hIint
  rw [integral_add hA hMi, integral_add hΦ0int hIint, hMint, add_zero] at hzeroint
  rw [intervalIntegral.integral_of_le hS0, ← integral_Icc_eq_integral_Ioc, ← hIeq, hLHS]
  linarith

end P3