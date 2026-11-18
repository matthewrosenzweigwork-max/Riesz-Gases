import HRS.PDE.MeanFieldAprioriParaproduct
import HRS.PDE.MeanFieldAprioriVolterraToolsB
import HRS.PDE.MeanFieldAprioriClassicalOn

/-!
# (I3, amended) AP5c2: the `H^K` bound by Volterra bootstrapping (package MF-01)

For a real solution on `[0,T]` with `|ρ| ≤ Λ`:
* `exists_volterra_step`: `H^{j-1}` control on `[v,v+1]` gives `H^j` control at `v+1`;
* `exists_short_time_bound`: `‖ρ̂(v+t)‖_{H^K} ≤ C ‖ρ̂(v)‖_{H^K}` for `t ∈ [0,1]`;
* `exists_hK_bound`: `sup_{[0,T]} ‖ρ̂(t)‖_{H^K} ≤ C` with `C` independent of `T` and `ν ∈ [ν₋,ν₊]`.

Route: modewise Duhamel formula (`mild_eq_Icc`), Minkowski + heat smoothing
(`hsNorm_intervalIntegral_le`, `exists_heat_smoothing`), the nonlinear loss bound
(`exists_nonlinear_loss_bound`) and the singular Gronwall inequalities.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.PDE.MFApriori

variable {d : ℕ}

/-! ### Small helpers -/

theorem hsNorm_mono_idx {a b : ℝ} (hab : a ≤ b) {c : Coeff d} (hc : MemHs b c) :
    hsNorm a c ≤ hsNorm b c :=
  Real.sqrt_le_sqrt (hsNormSq_mono' hab hc)

theorem continuousInHsOn_mono_idx {a b : ℝ} (hab : a ≤ b) {F : ℝ → Coeff d} {S : Set ℝ}
    (h : ContinuousInHsOn b F S) : ContinuousInHsOn a F S := by
  refine ⟨fun τ hτ => memHs_mono' hab (h.1 τ hτ), fun τ0 hτ0 => ?_⟩
  refine squeeze_zero' (Eventually.of_forall fun _ => hsNorm_nonneg' _ _) ?_ (h.2 τ0 hτ0)
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact hsNorm_mono_idx hab (memHs_sub (h.1 τ hτ) (h.1 τ0 hτ0))

/-- Measurability of `σ ↦ ‖F σ‖_{H^m}` from measurability of the modes. -/
theorem aestronglyMeasurable_hsNorm (m : ℝ) (F : ℝ → Coeff d) {μ : Measure ℝ}
    (hmeas : ∀ k, AEStronglyMeasurable (fun σ => F σ k) μ) :
    AEStronglyMeasurable (fun σ => hsNorm m (F σ)) μ := by
  have h1 : ∀ k, AEMeasurable (fun σ => ENNReal.ofReal (sobWeight m k * ‖F σ k‖ ^ 2)) μ :=
    fun k => ENNReal.measurable_ofReal.comp_aemeasurable
      (((hmeas k).norm.aemeasurable.pow_const 2).const_mul _)
  have h2 := (AEMeasurable.ennreal_tsum h1)
  have h3 : AEMeasurable (fun σ => hsNorm m (F σ)) μ := by
    have := (ENNReal.measurable_toReal.comp_aemeasurable h2)
    refine (Real.continuous_sqrt.measurable.comp_aemeasurable this).congr (Eventually.of_forall fun σ => ?_)
    simp only [Function.comp, hsNorm, hsNormSq]
    rw [ENNReal.tsum_toReal_eq (fun k => ENNReal.ofReal_ne_top)]
    congr 1
    refine tsum_congr fun k => ?_
    rw [ENNReal.toReal_ofReal (mul_nonneg (sobWeight_pos m k).le (sq_nonneg _))]
  exact h3.aestronglyMeasurable

/-! ### The nonlinear part, uniformly in `ν` -/

theorem rhs_sub_laplace_eq (s : ℝ) (V : Torus d → ℝ) (ν : ℝ) (c : Coeff d) :
    mfRhsCoeff d s V ν c - (ν : ℂ) • laplaceCoeff c = Aux.nlCoeff d s V c := by
  rw [Aux.mfRhsCoeff_split]
  funext k
  simp

theorem isCk_of_le_nat (K : ℕ) (j : ℝ) (hjK : j ≤ K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) :
    Torus.IsCk (⌈j⌉₊ + 1 : ℕ) V := by
  have hc : ⌈j⌉₊ ≤ K := Nat.ceil_le.mpr hjK
  refine ContDiff.of_le hV ?_
  exact_mod_cast (by omega : ⌈j⌉₊ + 1 ≤ K + 2)

/-- Loss bound for the `ν`-independent part `nlCoeff`. -/
theorem exists_nl_loss (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (b : ℝ)
    (hb : max (s - d + 1) 0 < b) (hb1 : b ≤ 1) (K : ℕ) (j : ℝ) (hj1 : 1 ≤ j) (hjK : j ≤ K)
    (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Continuous f → MemHs j (coeffOf f) →
      MemHs (j - (1 + b)) (Aux.nlCoeff d s V (coeffOf f)) ∧
      hsNorm (j - (1 + b)) (Aux.nlCoeff d s V (coeffOf f)) ≤
        C * (Torus.supNorm f + 1) * hsNorm j (coeffOf f) := by
  obtain ⟨C, hC0, hC⟩ := exists_nonlinear_loss_bound hd s hs0 hsd b hb hb1 j hj1 V
    (isCk_of_le_nat K j hjK V hV) 0
  refine ⟨C, hC0, fun f hf hfj => ?_⟩
  have h := hC f hf hfj
  rwa [rhs_sub_laplace_eq] at h

/-! ### Facts about a real solution on `[0,T]` -/

section SolFacts

variable {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} {ρ₀ : Torus d → ℝ} {ρc : ℝ → Coeff d} {T : ℝ}

theorem MFSolRealOn.summable_norm (hK : (d : ℝ) / 2 < K) (H : MFSolRealOn d s V ν K ρ₀ ρc T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Summable fun k => ‖ρc t k‖ :=
  summable_norm_of_memHs K hK _ (H.sol.cont.1 t ht)

theorem MFSolRealOn.coeffOf_mfPath (hK : (d : ℝ) / 2 < K) (H : MFSolRealOn d s V ν K ρ₀ ρc T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : coeffOf (mfPath ρc t) = ρc t :=
  coeffOf_toFun _ (H.real t ht) (H.summable_norm hK ht)

theorem MFSolRealOn.continuous_mfPath (hK : (d : ℝ) / 2 < K) (H : MFSolRealOn d s V ν K ρ₀ ρc T)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) : Continuous (mfPath ρc t) :=
  continuous_toFun _ (H.summable_norm hK ht)

end SolFacts

/-! ### Elementary kernel estimates -/

/-- `1 + (ν u)^{-γ} ≤ (1 + ν₋^{-γ}) u^{-γ}` for `ν ≥ ν₋ > 0`, `0 < u ≤ 1`, `γ ≥ 0`. -/
theorem kernel_le {νm ν u γ : ℝ} (hνm : 0 < νm) (hν : νm ≤ ν) (hu0 : 0 < u) (hu1 : u ≤ 1)
    (hγ : 0 ≤ γ) : 1 + (ν * u) ^ (-γ) ≤ (1 + νm ^ (-γ)) * u ^ (-γ) := by
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν
  have h1 : (1 : ℝ) ≤ u ^ (-γ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hu0 hu1 (by linarith)
  have h2 : ν ^ (-γ) ≤ νm ^ (-γ) := Real.rpow_le_rpow_of_nonpos hνm hν (by linarith)
  have hu : 0 ≤ u ^ (-γ) := Real.rpow_nonneg hu0.le _
  rw [Real.mul_rpow hν0.le hu0.le]
  nlinarith [mul_le_mul_of_nonneg_right h2 hu]

theorem heatMult_le_one {τ : ℝ} (hτ : 0 ≤ τ) (k : Lattice d) : heatMult τ k ≤ 1 := by
  unfold heatMult
  exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) hτ])

theorem memHs_heat {m : ℝ} {c : Coeff d} (hc : MemHs m c) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemHs m (fun k => (heatMult τ k : ℂ) * c k) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_pos m k).le (sq_nonneg _))
    (fun k => ?_) hc
  refine mul_le_mul_of_nonneg_left ?_ (sobWeight_pos m k).le
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (heatMult_pos τ k).le]
  exact pow_le_pow_left₀ (mul_nonneg (heatMult_pos τ k).le (norm_nonneg _)) (by nlinarith [heatMult_le_one hτ k, heatMult_pos τ k, norm_nonneg (c k)]) 2

theorem continuousOn_hsNorm_path {m : ℝ} {F : ℝ → Coeff d} {S : Set ℝ}
    (h : ContinuousInHsOn m F S) : ContinuousOn (fun τ => hsNorm m (F τ)) S :=
  fun _ hτ => Aux.continuousWithinAt_hsNorm h hτ

/-- The rescaling step for a Volterra inequality that is only known on `(0, s]`. -/
theorem rescale_step_le (γ C : ℝ) (hγ1 : γ < 1) (hC : 0 ≤ C) (ψ : ℝ → ℝ) (A : ℝ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hψ : ∀ t ∈ Set.Icc (0 : ℝ) s, 0 ≤ ψ t)
    (hE : ∀ t ∈ Set.Ioc (0 : ℝ) s, ψ t ≤ A + C * ∫ r in (0 : ℝ)..t, (t - r) ^ (-γ) * ψ r) :
    ∀ u ∈ Set.Ioc (0 : ℝ) 1, ψ (s * u) ≤ A +
      C * ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r) := by
  intro u hu
  have hsu : s * u ∈ Set.Ioc (0 : ℝ) s :=
    ⟨mul_pos hs0 hu.1, by nlinarith [hu.1, hu.2]⟩
  have h1 := hE _ hsu
  rw [integral_rescale_aux γ ψ hs0 hu.1.le] at h1
  have hI : 0 ≤ ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r) := by
    refine intervalIntegral.integral_nonneg hu.1.le fun r hr => ?_
    refine mul_nonneg (Real.rpow_nonneg (by linarith [hr.2]) _) (hψ _ ⟨by nlinarith [hr.1], ?_⟩)
    nlinarith [hr.1, hr.2, hu.2]
  have hs' : s ^ (1 - γ) ≤ 1 := Real.rpow_le_one hs0.le hs1 (by linarith)
  have : C * (s ^ (1 - γ) * ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r)) ≤
      C * ∫ r in (0 : ℝ)..u, (u - r) ^ (-γ) * ψ (s * r) := by
    refine mul_le_mul_of_nonneg_left ?_ hC
    nlinarith
  linarith

/-- The exponent gain `b ∈ (max(θ-1,0), 1)` used throughout. -/
def bExp (d : ℕ) (s : ℝ) : ℝ := (max (s - d + 1) 0 + 1) / 2

theorem bExp_spec (s : ℝ) (hsd : s < d) :
    max (s - d + 1) 0 < bExp d s ∧ bExp d s < 1 ∧ 0 < bExp d s := by
  have h1 : max (s - d + 1) 0 < 1 := max_lt (by linarith) one_pos
  have h2 : 0 ≤ max (s - d + 1) 0 := le_max_right _ _
  unfold bExp
  refine ⟨by linarith, by linarith, by linarith⟩

/-! ### The Duhamel estimate in `H^j` -/

theorem ae_Ioo_of_Ioc (a b : ℝ) :
    ∀ᵐ σ ∂(volume.restrict (Set.Ioc a b)), σ ∈ Set.Ioo a b := by
  have h1 : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∉ ({b} : Set ℝ) :=
    (Set.countable_singleton b).ae_notMem volume
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h1] with σ hσ hσ'
  exact ⟨hσ'.1, lt_of_le_of_ne hσ'.2 (by simpa using hσ)⟩

theorem duhamel_core (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (νm νp : ℝ)
    (hνm : 0 < νm) (Λ : ℝ) (j : ℝ) (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν ∈ Set.Icc νm νp, ∀ (ρ₀ : Torus d → ℝ) (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ v, 0 ≤ v → ∀ t, 0 < t → t ≤ 1 → v + t ≤ T →
        hsNorm j (ρc (v + t)) ≤ hsNorm j (fun k => (heatMult (ν * t) k : ℂ) * ρc v k) +
          C * ∫ σ in (0 : ℝ)..t, (t - σ) ^ (-((1 + bExp d s) / 2)) * hsNorm j (ρc (v + σ)) := by
  obtain ⟨hb, hb1', hb0⟩ := bExp_spec (d := d) s hsd
  set b := bExp d s with hbdef
  have hb1 : b ≤ 1 := hb1'.le
  set γ : ℝ := (1 + b) / 2 with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ < 1 := by rw [hγ]; linarith
  obtain ⟨Cn, hCn0, hCn⟩ := exists_nl_loss hd s hs0 hsd b hb hb1 K j hj1 hjK V hV
  obtain ⟨Ch, hCh0, hCh⟩ := exists_heat_smoothing (d := d) (j - (1 + b)) (1 + b)
    (by linarith) (by linarith)
  set Λ' : ℝ := max Λ 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  refine ⟨Ch * Cn * (Λ' + 1) * (1 + νm ^ (-γ)), ?_, ?_⟩
  · have : 0 ≤ νm ^ (-γ) := Real.rpow_nonneg hνm.le _
    positivity
  intro ν hν ρ₀ T ρc H hΛ v hv t ht0 ht1 hvt
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hKd : (d : ℝ) / 2 < K := by linarith
  have hmem : ∀ σ ∈ Set.Icc (0 : ℝ) t, v + σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨add_nonneg hv hσ.1, by linarith [hσ.2]⟩
  have hcontj : ContinuousInHsOn j ρc (Set.Icc 0 T) := continuousInHsOn_mono_idx (by exact_mod_cast hjK) H.sol.cont
  have hψc : ContinuousOn (fun σ => hsNorm j (ρc (v + σ))) (Set.Icc 0 t) :=
    (continuousOn_hsNorm_path hcontj).comp (continuousOn_const.add continuousOn_id) (fun σ hσ => hmem σ hσ)
  have heq : ∀ k, ∀ u ∈ Set.Icc 0 T,
      ρc u k = ρc 0 k + ∫ σ in (0 : ℝ)..u, mfRhsCoeff d s V ν (ρc σ) k := by
    intro k u hu
    rw [H.sol.eq k u hu, H.sol.init]
  have hmild := fun k => mild_eq_Icc hd s hs0 hsd K (by linarith) V hV ν hν0 ρc T H.sol.cont heq k
    hv ht0.le hvt
  -- the integrand
  set Fc : ℝ → Coeff d := fun σ k => (heatMult (ν * (t - σ)) k : ℂ) *
    Aux.nlCoeff d s V (ρc (v + σ)) k with hFc
  have hsplit : ρc (v + t) = (fun k => (heatMult (ν * t) k : ℂ) * ρc v k) +
      fun k => ∫ σ in (0 : ℝ)..t, Fc σ k := by
    funext k
    rw [hmild k]
    simp only [Pi.add_apply]
    congr 1
    refine intervalIntegral.integral_congr fun σ _ => ?_
    simp only [hFc]
    have := congr_fun (rhs_sub_laplace_eq s V ν (ρc (v + σ))) k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this]
  -- pointwise estimates
  set Cg : ℝ := Ch * Cn * (Λ' + 1) * (1 + νm ^ (-γ)) with hCg
  have hpt : ∀ σ ∈ Set.Ioo (0 : ℝ) t, MemHs j (Fc σ) ∧
      hsNorm j (Fc σ) ≤ Cg * ((t - σ) ^ (-γ) * hsNorm j (ρc (v + σ))) := by
    intro σ hσ
    have hσ' : v + σ ∈ Set.Icc (0 : ℝ) T := hmem σ ⟨hσ.1.le, hσ.2.le⟩
    have hfc := H.continuous_mfPath hKd hσ'
    have hco := H.coeffOf_mfPath hKd hσ'
    have hfj : MemHs j (coeffOf (mfPath ρc (v + σ))) := by
      rw [hco]; exact memHs_mono' (by exact_mod_cast hjK) (H.sol.cont.1 _ hσ')
    have hsup : Torus.supNorm (mfPath ρc (v + σ)) ≤ Λ' :=
      ProdAux.supNorm_le_of_bdd fun x => (hΛ _ hσ' x).trans (le_max_left _ _)
    obtain ⟨hNm, hNb⟩ := hCn _ hfc hfj
    rw [hco] at hNm hNb
    have htσ : 0 < t - σ := by linarith [hσ.2]
    obtain ⟨hHm, hHb⟩ := hCh ν (t - σ) hν0 htσ _ hNm
    rw [sub_add_cancel] at hHm hHb
    refine ⟨hHm, hHb.trans ?_⟩
    have hk := kernel_le hνm hν.1 htσ (by linarith [hσ.1]) hγ0
    have hnn := hsNorm_nonneg' (j - (1 + b)) (Aux.nlCoeff d s V (ρc (v + σ)))
    have hψ0 := hsNorm_nonneg' j (ρc (v + σ))
    have hsn0 : 0 ≤ Torus.supNorm (mfPath ρc (v + σ)) + 1 := by
      have : 0 ≤ Torus.supNorm (mfPath ρc (v + σ)) := by
        unfold Torus.supNorm
        exact Real.iSup_nonneg fun x => norm_nonneg _
      linarith
    have h1 : hsNorm (j - (1 + b)) (Aux.nlCoeff d s V (ρc (v + σ))) ≤
        Cn * (Λ' + 1) * hsNorm j (ρc (v + σ)) :=
      hNb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hCn0) hψ0)
    calc Ch * (1 + (ν * (t - σ)) ^ (-γ)) * hsNorm (j - (1 + b)) (Aux.nlCoeff d s V (ρc (v + σ)))
        ≤ Ch * ((1 + νm ^ (-γ)) * (t - σ) ^ (-γ)) * (Cn * (Λ' + 1) * hsNorm j (ρc (v + σ))) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hk hCh0) h1 hnn ?_
          exact mul_nonneg hCh0 (mul_nonneg (by have := Real.rpow_nonneg hνm.le (-γ); linarith) (Real.rpow_nonneg htσ.le _))
      _ = Cg * ((t - σ) ^ (-γ) * hsNorm j (ρc (v + σ))) := by rw [hCg]; ring
  -- measurability and integrability
  have hcm : ∀ k, ContinuousOn (fun σ => Fc σ k) (Set.Icc 0 t) := by
    intro k
    have hR : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Icc 0 T) :=
      Aux.continuousOn_mode (rhs_continuousInHsOn_vt hd s hs0 hsd K (by linarith) V hV ν ρc _ H.sol.cont) k
    have hy : ContinuousOn (fun σ => ρc σ k) (Set.Icc 0 T) := Aux.continuousOn_mode H.sol.cont k
    have hshift : ContinuousOn (fun σ => v + σ) (Set.Icc (0 : ℝ) t) :=
      continuousOn_const.add continuousOn_id
    have hRs := hR.comp hshift (fun σ hσ => hmem σ hσ)
    have hys := hy.comp hshift (fun σ hσ => hmem σ hσ)
    have hN : ContinuousOn (fun σ => Aux.nlCoeff d s V (ρc (v + σ)) k) (Set.Icc 0 t) := by
      have : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc (v + σ)) k -
          (ν : ℂ) * laplaceCoeff (ρc (v + σ)) k) (Set.Icc 0 t) := by
        refine hRs.sub (continuousOn_const.mul ?_)
        simp only [laplaceCoeff]
        exact continuousOn_const.mul hys
      refine this.congr fun σ _ => ?_
      have := congr_fun (rhs_sub_laplace_eq s V ν (ρc (v + σ))) k
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
      exact this.symm
    have hheat : ContinuousOn (fun σ : ℝ => ((heatMult (ν * (t - σ)) k : ℝ) : ℂ)) (Set.Icc 0 t) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      unfold heatMult
      exact (Real.continuous_exp.comp (by fun_prop)).continuousOn
    exact hheat.mul hN
  have hmeas : ∀ k, AEStronglyMeasurable (fun σ => Fc σ k) (volume.restrict (Set.Ioc 0 t)) :=
    fun k => ((hcm k).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have hgint : IntervalIntegrable
      (fun σ => Cg * ((t - σ) ^ (-γ) * hsNorm j (ρc (v + σ)))) volume 0 t := by
    refine IntervalIntegrable.const_mul ?_ _
    refine (intervalIntegrable_sub_rpow_neg γ hγ1 t).mul_continuousOn ?_
    rwa [Set.uIcc_of_le ht0.le]
  have hae := ae_Ioo_of_Ioc 0 t
  have hint : IntegrableOn (fun σ => hsNorm j (Fc σ)) (Set.Ioc 0 t) := by
    refine Integrable.mono' ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).1 hgint)
      (aestronglyMeasurable_hsNorm j Fc hmeas) ?_
    filter_upwards [hae] with σ hσ
    rw [Real.norm_of_nonneg (hsNorm_nonneg' _ _)]
    exact (hpt σ hσ).2
  obtain ⟨hIm, hIb⟩ := hsNorm_intervalIntegral_le j Fc 0 t ht0.le hmeas (fun σ hσ => (hpt σ hσ).1) hint
  have hmono : ∫ σ in (0 : ℝ)..t, hsNorm j (Fc σ) ≤
      ∫ σ in (0 : ℝ)..t, Cg * ((t - σ) ^ (-γ) * hsNorm j (ρc (v + σ))) := by
    rw [intervalIntegral.integral_of_le ht0.le, intervalIntegral.integral_of_le ht0.le]
    refine integral_mono_ae hint ((intervalIntegrable_iff_integrableOn_Ioc_of_le ht0.le).1 hgint) ?_
    filter_upwards [hae] with σ hσ using (hpt σ hσ).2
  have hdat : MemHs j (fun k => (heatMult (ν * t) k : ℂ) * ρc v k) :=
    memHs_heat (memHs_mono' (by exact_mod_cast hjK) (H.sol.cont.1 v ⟨hv, by linarith⟩))
      (mul_nonneg hν0.le ht0.le)
  rw [hsplit]
  refine (Aux.memHs_add_le j hdat hIm).2.trans ?_
  rw [intervalIntegral.integral_const_mul] at hmono
  linarith

/-! ### Base case: the `L²` norm -/

theorem hsNorm_zero_coeffOf_le (f : Torus d → ℝ) (hf : Continuous f) (A : ℝ)
    (hA : ∀ x, |f x| ≤ A) : hsNorm 0 (coeffOf f) ≤ A := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hm : MemLp (fun x => (f x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hf).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  obtain ⟨-, h2⟩ := hsNormSq_zero_coeffOfC (fun x => (f x : ℂ)) hm
  have h3 : hsNormSq 0 (coeffOf f) = ∫ x, ‖(f x : ℂ)‖ ^ 2 := h2
  have h4 : ∫ x, ‖(f x : ℂ)‖ ^ 2 ≤ A ^ 2 := by
    have hint : Integrable (fun x => ‖(f x : ℂ)‖ ^ 2) volume := by
      have := hm.integrable_norm_pow (p := 2) (by norm_num)
      simpa using this
    calc ∫ x, ‖(f x : ℂ)‖ ^ 2 ≤ ∫ _x : Torus d, A ^ 2 := by
          refine integral_mono hint (integrable_const _) fun x => ?_
          simp only [Complex.norm_real, Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2
      _ = A ^ 2 := by simp
  unfold hsNorm
  rw [h3]
  exact Real.sqrt_le_iff.mpr ⟨hA0, h4⟩

/-! ### The main estimates -/

theorem exists_volterra_step (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (Λ : ℝ) (j : ℝ) (hj1 : 1 ≤ j) (hjK : j ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν ∈ Set.Icc νm νp, ∀ (ρ₀ : Torus d → ℝ) (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ v, 0 ≤ v → v + 1 ≤ T → ∀ B, (∀ r ∈ Set.Icc 0 1, hsNorm (j - 1) (ρc (v + r)) ≤ B) →
        hsNorm j (ρc (v + 1)) ≤ C * B := by
  obtain ⟨hb, hb1', hb0⟩ := bExp_spec (d := d) s hsd
  set γ : ℝ := (1 + bExp d s) / 2 with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ < 1 := by rw [hγ]; linarith
  obtain ⟨C2, hC20, hC2⟩ := duhamel_core hd s hs0 hsd K hK V hV νm νp hνm Λ j hj1 hjK
  obtain ⟨C', hC'0, hC'⟩ := singular_gronwall γ C2 hγ0 hγ1 hC20
  obtain ⟨Ch, hCh0, hCh⟩ := exists_heat_smoothing (d := d) (j - 1) 1 (by norm_num) (by norm_num)
  have hn0 : 0 ≤ νm ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hνm.le _
  refine ⟨C' * (Ch * (1 + νm ^ (-(1 / 2 : ℝ)))), by positivity, ?_⟩
  intro ν hν ρ₀ T ρc H hΛ v hv hvT B hB
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hB0 : 0 ≤ B := (hsNorm_nonneg' _ _).trans (by simpa using hB 0 ⟨le_rfl, zero_le_one⟩)
  have hmem : ∀ σ ∈ Set.Icc (0 : ℝ) 1, v + σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨add_nonneg hv hσ.1, by linarith [hσ.2]⟩
  have hcontj : ContinuousInHsOn j ρc (Set.Icc 0 T) :=
    continuousInHsOn_mono_idx (by exact_mod_cast hjK) H.sol.cont
  have hψc : ContinuousOn (fun σ => hsNorm j (ρc (v + σ))) (Set.Icc 0 1) :=
    (continuousOn_hsNorm_path hcontj).comp (continuousOn_const.add continuousOn_id)
      (fun σ hσ => hmem σ hσ)
  obtain ⟨Bψ, hBψ⟩ := isCompact_Icc.exists_bound_of_continuousOn hψc
  set A : ℝ := Ch * (1 + νm ^ (-(1 / 2 : ℝ))) * B with hA
  have hA0 : 0 ≤ A := by positivity
  have hmv : MemHs (j - 1) (ρc v) :=
    memHs_mono' (by have : (j : ℝ) ≤ K := hjK; linarith) (H.sol.cont.1 v ⟨hv, by linarith⟩)
  have key := hC' (fun σ => hsNorm j (ρc (v + σ))) A Bψ hA0 hψc
    (fun t ht => ⟨hsNorm_nonneg' _ _, (le_abs_self _).trans (by simpa using hBψ t ht)⟩) (by
      intro t ht
      have hcore := hC2 ν hν ρ₀ T ρc H hΛ v hv t ht.1 ht.2 (by linarith [ht.2])
      obtain ⟨-, hh⟩ := hCh ν t hν0 ht.1 (ρc v) hmv
      rw [sub_add_cancel] at hh
      have hk := kernel_le hνm hν.1 ht.1 ht.2 (γ := 1 / 2) (by norm_num)
      have hB' : hsNorm (j - 1) (ρc v) ≤ B := by simpa using hB 0 ⟨le_rfl, zero_le_one⟩
      have hdat : hsNorm j (fun k => (heatMult (ν * t) k : ℂ) * ρc v k) ≤
          A * t ^ (-(1 / 2 : ℝ)) := by
        refine hh.trans ?_
        calc Ch * (1 + (ν * t) ^ (-(1 / 2 : ℝ))) * hsNorm (j - 1) (ρc v)
            ≤ Ch * ((1 + νm ^ (-(1 / 2 : ℝ))) * t ^ (-(1 / 2 : ℝ))) * B := by
              refine mul_le_mul (mul_le_mul_of_nonneg_left hk hCh0) hB' (hsNorm_nonneg' _ _) ?_
              exact mul_nonneg hCh0 (mul_nonneg (by linarith) (Real.rpow_nonneg ht.1.le _))
          _ = A * t ^ (-(1 / 2 : ℝ)) := by rw [hA]; ring
      linarith)
  calc hsNorm j (ρc (v + 1)) ≤ C' * A := key
    _ = C' * (Ch * (1 + νm ^ (-(1 / 2 : ℝ)))) * B := by rw [hA]; ring

theorem exists_short_time_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν ∈ Set.Icc νm νp, ∀ (ρ₀ : Torus d → ℝ) (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ v, 0 ≤ v → ∀ t ∈ Set.Icc 0 1, v + t ≤ T →
        hsNorm K (ρc (v + t)) ≤ C * hsNorm K (ρc v) := by
  obtain ⟨hb, hb1', hb0⟩ := bExp_spec (d := d) s hsd
  set γ : ℝ := (1 + bExp d s) / 2 with hγ
  have hγ0 : 0 ≤ γ := by rw [hγ]; linarith
  have hγ1 : γ < 1 := by rw [hγ]; linarith
  have hK1 : (1 : ℝ) ≤ K := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  obtain ⟨C2, hC20, hC2⟩ := duhamel_core hd s hs0 hsd K hK V hV νm νp hνm Λ K hK1 le_rfl
  obtain ⟨C', hC'0, hC'⟩ := gronwall_Ioc γ C2 hγ0 hγ1 hC20
  obtain ⟨Ch, hCh0, hCh⟩ := exists_heat_smoothing (d := d) (K : ℝ) 0 le_rfl (by norm_num)
  refine ⟨max (C' * (Ch * 2)) 1, le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro ν hν ρ₀ T ρc H hΛ v hv t ht hvt
  have hν0 : 0 < ν := lt_of_lt_of_le hνm hν.1
  have hCge : 1 ≤ max (C' * (Ch * 2)) 1 := le_max_right _ _
  rcases ht.1.eq_or_lt with h0 | hτ0
  · rw [← h0, add_zero]
    nlinarith [hsNorm_nonneg' (K : ℝ) (ρc v)]
  set τ : ℝ := t with hτ
  have hτ1 : τ ≤ 1 := ht.2
  have hmemT : ∀ σ ∈ Set.Icc (0 : ℝ) τ, v + σ ∈ Set.Icc (0 : ℝ) T := fun σ hσ =>
    ⟨add_nonneg hv hσ.1, by linarith [hσ.2]⟩
  have hmv : MemHs (K : ℝ) (ρc v) := H.sol.cont.1 v ⟨hv, by linarith⟩
  set A : ℝ := Ch * 2 * hsNorm K (ρc v) with hA
  have hA0 : 0 ≤ A := by have := hsNorm_nonneg' (K : ℝ) (ρc v); positivity
  set ψ : ℝ → ℝ := fun σ => hsNorm K (ρc (v + σ)) with hψ
  have hψnn : ∀ σ ∈ Set.Icc (0 : ℝ) τ, 0 ≤ ψ σ := fun σ _ => hsNorm_nonneg' _ _
  have hE : ∀ r ∈ Set.Ioc (0 : ℝ) τ, ψ r ≤ A + C2 * ∫ q in (0 : ℝ)..r, (r - q) ^ (-γ) * ψ q := by
    intro r hr
    have hcore := hC2 ν hν ρ₀ T ρc H hΛ v hv r hr.1 (hr.2.trans hτ1) (by linarith [hr.2])
    obtain ⟨-, hh⟩ := hCh ν r hν0 hr.1 (ρc v) hmv
    rw [add_zero] at hh
    simp only [zero_div, neg_zero, Real.rpow_zero] at hh
    have : hsNorm K (fun k => (heatMult (ν * r) k : ℂ) * ρc v k) ≤ A := by
      refine hh.trans (le_of_eq ?_)
      rw [hA]; ring
    show hsNorm K (ρc (v + r)) ≤ _
    linarith
  have hS := rescale_step_le γ C2 hγ1 hC20 ψ A (lt_of_lt_of_le hτ0 le_rfl) hτ1 hψnn hE
  have hcontK : ContinuousOn (fun σ => hsNorm K (ρc σ)) (Set.Icc 0 T) :=
    continuousOn_hsNorm_path H.sol.cont
  have hφc : ContinuousOn (fun u => ψ (τ * u)) (Set.Icc 0 1) := by
    refine hcontK.comp (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) ?_
    intro u hu
    exact hmemT _ ⟨mul_nonneg hτ0.le hu.1, by nlinarith [hu.2]⟩
  obtain ⟨Bφ, hBφ⟩ := isCompact_Icc.exists_bound_of_continuousOn hφc
  have key := hC' (fun u => ψ (τ * u)) A Bφ hA0 hφc
    (fun u hu => ⟨hsNorm_nonneg' _ _, (le_abs_self _).trans (by simpa using hBφ u hu)⟩)
    (fun u hu => hS u hu) 1 ⟨one_pos, le_rfl⟩
  have hfin : hsNorm K (ρc (v + τ)) ≤ C' * A := by
    have : ψ (τ * 1) = hsNorm K (ρc (v + τ)) := by simp [hψ]
    simpa [this] using key
  calc hsNorm K (ρc (v + t)) ≤ C' * A := hfin
    _ = (C' * (Ch * 2)) * hsNorm K (ρc v) := by rw [hA]; ring
    _ ≤ max (C' * (Ch * 2)) 1 * hsNorm K (ρc v) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (hsNorm_nonneg' _ _)

theorem exists_hK_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (νm νp : ℝ)
    (hνm : 0 < νm) (hνν : νm ≤ νp) (ρ₀ : Torus d → ℝ) (hρ₀H : MemSobolev K ρ₀) (Λ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ t ∈ Set.Icc 0 T, hsNorm K (ρc t) ≤ C := by
  have hKd : (d : ℝ) / 2 < K := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  -- Phase 1: large times, by induction on the regularity index
  have phase1 : ∀ n : ℕ, n ≤ K → ∃ B : ℝ, ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ t ∈ Set.Icc 0 T, (n : ℝ) ≤ t → hsNorm (n : ℝ) (ρc t) ≤ B := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨Λ, fun ν hν T ρc H hΛ t ht _ => ?_⟩
      have h := hsNorm_zero_coeffOf_le (mfPath ρc t) (H.continuous_mfPath hKd ht) Λ (hΛ t ht)
      rw [H.coeffOf_mfPath hKd ht] at h
      simpa using h
    | succ n ih =>
      intro hn
      obtain ⟨Bn, hBn⟩ := ih (by omega)
      obtain ⟨C, hC0, hC⟩ := exists_volterra_step hd s hs0 hsd K hK V hV νm νp hνm hνν Λ
        ((n + 1 : ℕ) : ℝ) (by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        (by exact_mod_cast hn)
      refine ⟨C * Bn, fun ν hν T ρc H hΛ t ht htn => ?_⟩
      have hn1 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hn1] at htn
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hv : 0 ≤ t - 1 := by linarith
      have hvT : t - 1 + 1 ≤ T := by linarith [ht.2]
      have := hC ν hν ρ₀ T ρc H hΛ (t - 1) hv hvT Bn (fun r hr => by
        have hmem : t - 1 + r ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hr.1], by linarith [hr.2, ht.2]⟩
        have := hBn ν hν T ρc H hΛ (t - 1 + r) hmem (by linarith [hr.1])
        rwa [show ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) by rw [hn1]; ring])
      rw [sub_add_cancel] at this
      exact this
  obtain ⟨BK, hBK⟩ := phase1 K le_rfl
  -- Phase 2: bounded times, by iterating the short-time bound
  obtain ⟨Cs, hCs0, hCs⟩ := exists_short_time_bound hd s hs0 hsd K hK V hV νm νp hνm hνν Λ
  set Cs' : ℝ := max Cs 1 with hCs'
  have hCs'1 : 1 ≤ Cs' := le_max_right _ _
  have phase2 : ∀ ν ∈ Set.Icc νm νp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V ν K ρ₀ ρc T → (∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ) →
      ∀ m : ℕ, ∀ t ∈ Set.Icc 0 T, t ≤ m → hsNorm K (ρc t) ≤ Cs' ^ (m + 1) * hsNorm K (ρc 0) := by
    intro ν hν T ρc H hΛ m
    have h0 := hsNorm_nonneg' (K : ℝ) (ρc 0)
    induction m with
    | zero =>
      intro t ht htm
      have : t = 0 := le_antisymm (by simpa using htm) ht.1
      subst this
      simpa using mul_le_mul_of_nonneg_right hCs'1 h0
    | succ m ih =>
      intro t ht htm
      have hpow : Cs' ≤ Cs' ^ (m + 1 + 1) := by
        calc Cs' = Cs' ^ 1 := (pow_one _).symm
          _ ≤ Cs' ^ (m + 1 + 1) := pow_le_pow_right₀ hCs'1 (by omega)
      by_cases ht1 : t ≤ 1
      · have := hCs ν hν ρ₀ T ρc H hΛ 0 le_rfl t ⟨ht.1, ht1⟩ (by simpa using ht.2)
        rw [zero_add] at this
        calc hsNorm K (ρc t) ≤ Cs * hsNorm K (ρc 0) := this
          _ ≤ Cs' * hsNorm K (ρc 0) := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
          _ ≤ Cs' ^ (m + 1 + 1) * hsNorm K (ρc 0) := mul_le_mul_of_nonneg_right hpow h0
      · replace ht1 := not_le.mp ht1
        have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        have hv : t - 1 ∈ Set.Icc (0 : ℝ) T := ⟨by linarith, by linarith [ht.2]⟩
        have h1 := ih (t - 1) hv (by push_cast at htm; linarith)
        have h2 := hCs ν hν ρ₀ T ρc H hΛ (t - 1) hv.1 1 ⟨zero_le_one, le_rfl⟩
          (by linarith [ht.2])
        rw [sub_add_cancel] at h2
        calc hsNorm K (ρc t) ≤ Cs * hsNorm K (ρc (t - 1)) := h2
          _ ≤ Cs' * (Cs' ^ (m + 1) * hsNorm K (ρc 0)) :=
              mul_le_mul (le_max_left _ _) h1 (hsNorm_nonneg' _ _) (by linarith)
          _ = Cs' ^ (m + 1 + 1) * hsNorm K (ρc 0) := by ring
  refine ⟨max BK (Cs' ^ (K + 1) * hsNorm K (coeffOf ρ₀)), ?_, ?_⟩
  · exact le_trans (mul_nonneg (pow_nonneg (by linarith) _) (hsNorm_nonneg' _ _)) (le_max_right _ _)
  intro ν hν T ρc H hΛ t ht
  by_cases htK : (K : ℝ) ≤ t
  · exact (hBK ν hν T ρc H hΛ t ht htK).trans (le_max_left _ _)
  · replace htK := not_le.mp htK
    have := phase2 ν hν T ρc H hΛ K t ht htK.le
    rw [H.sol.init] at this
    exact this.trans (le_max_right _ _)

end HRS.PDE.MFApriori
