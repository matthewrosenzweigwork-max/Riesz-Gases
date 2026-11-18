import HRS.MP.FidiDefs

/-!
# Chunk F (`MP:`), finite-dimensional convergence for Theorem A.11: the surrogate laws on the field space

* `fi3c_surr_eq`: the particle-level surrogate law (built with `etaF`) is the field-space law `fieldSurr`;
* `fi3d_converges`: weak convergence of the `fieldSurr` to its limit (Lévy continuity theorem);
* `fi4_identify`: the law of the statistic vector of a linear fluctuation solution is `fieldSurr` of the limit.
-/

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Main HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.FidiDefs
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.MP.FidiLaw

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem fl_eval_meas {γ : ℝ} {ψ : Torus d → ℝ} (h : MemSobolev γ ψ) :
    Measurable fun F : NegSobolev d γ => NegSobolev.eval F ψ := by
  have : (fun F : NegSobolev d γ => NegSobolev.eval F ψ) =
      fun F => inner ℝ F (HRS.Uniform.Q54.lpOf γ h) := by
    funext F; exact HRS.Uniform.Q54.eval_eq_inner γ F h
  rw [this]
  exact (continuous_id.inner continuous_const).measurable

theorem fl_statVec_meas (D : DynData d) (ρ : ℝ → Torus d → ℝ) (A : ℝ) {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Torus d → ℝ) (γ : ℝ)
    (hmem : ∀ a, MemSobolev γ (propagator D ρ 0 (ts a) (φ a))) :
    Measurable (statVec D ρ A ts φ γ) := by
  unfold statVec
  refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
  exact Measurable.of_eval fun a => (fl_eval_meas (hmem a)).const_mul A

theorem fi3c_surr_eq {S : MainData d} {R : ∀ N, Realization d N} {Cin : ℝ} {εf : ℕ → ℝ}
    {ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ)}
    {νin : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hfield : InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin) {N : ℕ} (hN : 1 ≤ N)
    {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Torus d → ℝ)
    (hmem : ∀ a, MemSobolev (gammaIdx d : ℝ) (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a))) :
    surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (etaF R (gammaIdx d) ηF N).P
        (etaF R (gammaIdx d) ηF N).η =
      fieldSurr (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (gammaIdx d : ℝ) νin := by
  classical
  unfold surrogateStatLaw fieldSurr
  have hm := fl_statVec_meas (S.dyn N) (S.ρ N) (S.AN N) ts φ _ hmem
  have hfun : (fun ω => (WithLp.toLp 2 fun a => S.AN N * (etaF R (gammaIdx d) ηF N).η ω
      (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)) : ℝ^p)) =
      statVec (S.dyn N) (S.ρ N) (S.AN N) ts φ (gammaIdx d : ℝ) ∘ ηF N := by
    funext ω
    unfold statVec
    simp only [Function.comp]
    congr 1
    funext a
    show S.AN N * (if MemSobolev (gammaIdx d : ℝ) _ then _ else _) = _
    simp only [hmem a, ↓reduceIte]
  have hlaw : Measure.map (statVec (S.dyn N) (S.ρ N) (S.AN N) ts φ (gammaIdx d : ℝ) ∘ ηF N) (R N).P =
      νin.map (statVec (S.dyn N) (S.ρ N) (S.AN N) ts φ (gammaIdx d : ℝ)) := by
    rw [← Measure.map_map hm (hfield.ηF_meas N)]
    exact congrArg _ (hfield.law_eq N hN)
  rw [hfun]
  congr 1


/-- the Gaussian factor of a characteristic function, as a continuous function of the matrix. -/
theorem fl_charFun_gauss {p : ℕ} {M : Matrix (Fin p) (Fin p) ℝ} (hS : M.PosSemidef) (t : ℝ^p) :
    charFun (multivariateGaussian (0 : ℝ^p) M) t =
      Complex.exp (-(((dotProduct t.ofLp (M.mulVec t.ofLp) : ℝ) : ℂ) / 2)) := by
  rw [charFun_multivariateGaussian hS]
  simp


theorem fl_charFun_map {q : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ^q} 
    (hf : Measurable f) (t : ℝ^q) :
    charFun (μ.map f) t = ∫ x, Complex.exp (((inner ℝ (f x) t : ℝ) : ℂ) * Complex.I) ∂μ := by
  rw [charFun_apply, integral_map hf.aemeasurable]
  exact (by fun_prop : Continuous fun y : ℝ^q => Complex.exp (((inner ℝ y t : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable

theorem fl_eval_sub {γ : ℝ} (F : NegSobolev d γ) {ψ₁ ψ₂ : Torus d → ℝ} (h1 : MemSobolev γ ψ₁)
    (h2 : MemSobolev γ ψ₂) (c1 : Continuous ψ₁) (c2 : Continuous ψ₂) :
    NegSobolev.eval F (fun x => ψ₁ x - ψ₂ x) = NegSobolev.eval F ψ₁ - NegSobolev.eval F ψ₂ := by
  have := A33.a33_eval_lin F c1 c2 (A33.a33_ws_of_memSobolev h1) (A33.a33_ws_of_memSobolev h2) 1 (-1)
  simpa [sub_eq_add_neg] using this

theorem fi3d_converges {Rg : PDE.Regime} {ν₀ MB Λ VB : ℝ} (S : MainData d) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a))
    (hprop : ∀ a, (∀ N : ℕ, 1 ≤ N →
        MemSobolev (gammaIdx d : ℝ) (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)) ∧
          Continuous (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a))) ∧
      (MemSobolev (gammaIdx d : ℝ) (propagator (L.dyn S) L.ρ 0 (ts a) (φ a)) ∧
        Continuous (propagator (L.dyn S) L.ρ 0 (ts a) (φ a))) ∧
      Tendsto (fun N => sobolevNorm (gammaIdx d : ℝ)
        (fun x => propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a) x -
          propagator (L.dyn S) L.ρ 0 (ts a) (φ a) x)) atTop (𝓝 0))
    (hpsdN : ∀ N : ℕ, 1 ≤ N → (surrogateCov (S.dyn N) (S.ρ N) (S.qN N) ts φ).PosSemidef)
    (hpsdL : (surrogateCov (L.dyn S) L.ρ L.invβstar ts φ).PosSemidef)
    (hcov : ∀ a b : Fin p, Tendsto (fun N => surrogateCov (S.dyn N) (S.ρ N) (S.qN N) ts φ a b)
      atTop (𝓝 (surrogateCov (L.dyn S) L.ρ L.invβstar ts φ a b)))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ))) [IsProbabilityMeasure νin] :
    ConvergesInLaw
      (fun N => fieldSurr (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) ts φ (gammaIdx d : ℝ) νin)
      (fieldSurr (L.dyn S) L.ρ L.A L.invβstar ts φ (gammaIdx d : ℝ) νin) := by
  refine (HRS.Main.A9.a9_conv_shift 1).2 ?_
  have hmeas : ∀ n : ℕ, Measurable (statVec (S.dyn (n + 1)) (S.ρ (n + 1)) (S.AN (n + 1)) ts φ
      (gammaIdx d : ℝ)) := fun n =>
    fl_statVec_meas _ _ _ ts φ _ (fun a => ((hprop a).1 (n + 1) (by omega)).1)
  have hmeasL : Measurable (statVec (L.dyn S) L.ρ L.A ts φ (gammaIdx d : ℝ)) :=
    fl_statVec_meas _ _ _ ts φ _ (fun a => (hprop a).2.1.1)
  have hΔ : Tendsto (fun N => S.coeffDiscrepancy L (gammaIdx d) N) atTop (𝓝 0) := hcoef.tendsto
  have hAΔ : Tendsto (fun n : ℕ => S.AN (n + 1)) atTop (𝓝 L.A) := by
    have h0 : Tendsto (fun n : ℕ => S.coeffDiscrepancy L (gammaIdx d) (n + 1)) atTop (𝓝 0) :=
      hΔ.comp (tendsto_add_atTop_nat 1)
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) h0
    obtain ⟨-, -, -, -, hA⟩ := HRS.A34.a34_delta_facts S L (gammaIdx d) (n + 1) Rg ν₀ MB Λ VB
      (hcoef.seq_adjoint (n + 1) (by omega)) hcoef.limit_adjoint
    rw [Real.dist_eq]; exact hA
  -- pointwise convergence of the statistics
  have hpt : ∀ F : NegSobolev d (gammaIdx d : ℝ), Tendsto (fun n : ℕ =>
      statVec (S.dyn (n + 1)) (S.ρ (n + 1)) (S.AN (n + 1)) ts φ (gammaIdx d : ℝ) F) atTop
      (𝓝 (statVec (L.dyn S) L.ρ L.A ts φ (gammaIdx d : ℝ) F)) := by
    intro F
    refine ((PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).tendsto _).comp
      (tendsto_pi_nhds.2 fun a => ?_)
    refine hAΔ.mul ?_
    obtain ⟨hmN, hmL, hdiff⟩ := hprop a
    have hd0 := (hdiff.comp (tendsto_add_atTop_nat 1)).const_mul ‖F‖
    rw [mul_zero] at hd0
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hd0
    have hm1 := hmN (n + 1) (by omega)
    have hsub : MemSobolev (gammaIdx d : ℝ) (fun x =>
        propagator (S.dyn (n + 1)) (S.ρ (n + 1)) 0 (ts a) (φ a) x -
          propagator (L.dyn S) L.ρ 0 (ts a) (φ a) x) :=
      HRS.A34.a34_memSobolev_sub hm1.1 hmL.1 hm1.2 hmL.2
    rw [Real.dist_eq, ← fl_eval_sub F hm1.1 hmL.1 hm1.2 hmL.2]
    exact A33.a33_abs_eval_le F (A33.a33_ws_of_memSobolev hsub)
  -- probability measures
  have hpN : ∀ n : ℕ, IsProbabilityMeasure
      (fieldSurr (S.dyn (n + 1)) (S.ρ (n + 1)) (S.AN (n + 1)) (S.qN (n + 1)) ts φ
        (gammaIdx d : ℝ) νin) := fun n => by
    unfold fieldSurr
    infer_instance
  have hpL : IsProbabilityMeasure
      (fieldSurr (L.dyn S) L.ρ L.A L.invβstar ts φ (gammaIdx d : ℝ) νin) := by
    unfold fieldSurr
    infer_instance
  have key : ∀ t : ℝ^p, Tendsto (fun n : ℕ => charFun (fieldSurr (S.dyn (n + 1)) (S.ρ (n + 1))
      (S.AN (n + 1)) (S.qN (n + 1)) ts φ (gammaIdx d : ℝ) νin) t) atTop
      (𝓝 (charFun (fieldSurr (L.dyn S) L.ρ L.A L.invβstar ts φ (gammaIdx d : ℝ) νin) t)) := by
    intro t
    have e1 : ∀ n : ℕ, charFun (fieldSurr (S.dyn (n + 1)) (S.ρ (n + 1))
        (S.AN (n + 1)) (S.qN (n + 1)) ts φ (gammaIdx d : ℝ) νin) t =
        (∫ F, Complex.exp (((inner ℝ (statVec (S.dyn (n + 1)) (S.ρ (n + 1)) (S.AN (n + 1)) ts φ
          (gammaIdx d : ℝ) F) t : ℝ) : ℂ) * Complex.I) ∂νin) *
        Complex.exp (-(((dotProduct t.ofLp ((surrogateCov (S.dyn (n + 1)) (S.ρ (n + 1))
          (S.qN (n + 1)) ts φ).mulVec t.ofLp) : ℝ) : ℂ) / 2)) := fun n => by
      unfold fieldSurr
      have : IsFiniteMeasure (νin.map (statVec (S.dyn (n + 1)) (S.ρ (n + 1)) (S.AN (n + 1)) ts φ
        (gammaIdx d : ℝ))) := inferInstance
      rw [charFun_conv, fl_charFun_map (hmeas n), fl_charFun_gauss (hpsdN (n + 1) (by omega))]
    have e2 : charFun (fieldSurr (L.dyn S) L.ρ L.A L.invβstar ts φ (gammaIdx d : ℝ) νin) t =
        (∫ F, Complex.exp (((inner ℝ (statVec (L.dyn S) L.ρ L.A ts φ (gammaIdx d : ℝ) F) t : ℝ) : ℂ)
          * Complex.I) ∂νin) *
        Complex.exp (-(((dotProduct t.ofLp ((surrogateCov (L.dyn S) L.ρ L.invβstar ts φ).mulVec
          t.ofLp) : ℝ) : ℂ) / 2)) := by
      unfold fieldSurr
      have : IsFiniteMeasure (νin.map (statVec (L.dyn S) L.ρ L.A ts φ (gammaIdx d : ℝ))) :=
        inferInstance
      rw [charFun_conv, fl_charFun_map hmeasL, fl_charFun_gauss hpsdL]
    simp_rw [e1]
    rw [e2]
    refine Tendsto.mul ?_ ?_
    · refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun n => ?_)
        (integrable_const 1) (fun n => Eventually.of_forall fun F => ?_)
        (Eventually.of_forall fun F => ?_)
      · exact (((by fun_prop : Continuous fun y : ℝ^p =>
          Complex.exp (((inner ℝ y t : ℝ) : ℂ) * Complex.I)).measurable.comp
            (hmeas n)).aestronglyMeasurable)
      · rw [Complex.norm_exp_ofReal_mul_I]
      · exact (((by fun_prop : Continuous fun y : ℝ^p =>
          Complex.exp (((inner ℝ y t : ℝ) : ℂ) * Complex.I))).tendsto _).comp (hpt F)
    · have hSig : Tendsto (fun n : ℕ => surrogateCov (S.dyn (n + 1)) (S.ρ (n + 1)) (S.qN (n + 1)) ts φ)
          atTop (𝓝 (surrogateCov (L.dyn S) L.ρ L.invβstar ts φ)) := by
        refine tendsto_pi_nhds.2 fun a => tendsto_pi_nhds.2 fun b => ?_
        exact (hcov a b).comp (tendsto_add_atTop_nat 1)
      have hc : Continuous (fun M : Matrix (Fin p) (Fin p) ℝ =>
          Complex.exp (-(((dotProduct t.ofLp (M.mulVec t.ofLp) : ℝ) : ℂ) / 2))) := by
        simp only [Matrix.mulVec, dotProduct]
        fun_prop
      exact (hc.tendsto _).comp hSig
  have hT : Tendsto (fun n : ℕ => Measure.toProbabilityMeasure (fieldSurr (S.dyn (n + 1))
      (S.ρ (n + 1)) (S.AN (n + 1)) (S.qN (n + 1)) ts φ (gammaIdx d : ℝ) νin)) atTop
      (𝓝 (Measure.toProbabilityMeasure
        (fieldSurr (L.dyn S) L.ρ L.A L.invβstar ts φ (gammaIdx d : ℝ) νin))) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 key
  intro f
  simpa using ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT f


theorem fl_embed_memℓp {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) :
    Memℓp (fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k) 2 := by
  have hcoord : ∀ k, |Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k| ≤
      |NegSobolev.coord F k| := by
    intro k
    have hj := Torus.jp_pos k.1
    have : Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k =
        Lattice.jp k.1 ^ (m - m') * NegSobolev.coord F k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add hj]
      ring_nf
    rw [this, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hj _)]
    have h1 : Lattice.jp k.1 ^ (m - m') ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by linarith)
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  obtain ⟨h3, -⟩ := NegSobolev.coord_sq F
  rw [Torus.memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) h3
  calc _ = |Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k| ^ 2 := (sq_abs _).symm
    _ ≤ |NegSobolev.coord F k| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
    _ = _ := sq_abs _

theorem fl_eval_embed {m m' : ℝ} (hmm' : m ≤ m') (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (NegSobolev.embed m' F) φ = NegSobolev.eval F φ := by
  unfold NegSobolev.eval
  refine tsum_congr fun k => ?_
  have h : NegSobolev.coord (NegSobolev.embed m' F) k =
      Lattice.jp k.1 ^ (-m') * NegSobolev.fourierCoeff F k :=
    NegSobolev.coord_ofSeq_of_mem _ (fl_embed_memℓp hmm' F) k
  have h2 : NegSobolev.fourierCoeff (NegSobolev.embed m' F) k = NegSobolev.fourierCoeff F k := by
    unfold NegSobolev.fourierCoeff at h ⊢
    rw [h, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
    simp
  rw [h2]

theorem fi4_identify {Rg : PDE.Regime} {ν₀ MB Λ VB T : ℝ} (S : MainData d) (L : LimitCoeffs d)
    (hT : S.T = T)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (νin : Measure (NegSobolev d (gammaIdx d : ℝ))) [IsProbabilityMeasure νin]
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y₀ : Ω' → NegSobolev d ((qT d : ℕ) : ℝ)) (Y : ℝ → Ω' → NegSobolev d ((qT d : ℕ) : ℝ))
    (hY₀ : Measurable Y₀) (hlaw : law P' Y₀ = νin.map (NegSobolev.embed ((qT d : ℕ) : ℝ)))
    (hY : HRS.IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((qT d : ℕ) : ℝ) L.invβstar T
        (fun ζ => L.A • Y₀ ζ) Y)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
    (φ : Fin p → Torus d → ℝ) (hφ : ∀ a, Torus.IsSmooth (φ a))
    (hmemq : ∀ a, MemSobolev ((qT d : ℕ) : ℝ) (propagator (L.dyn S) L.ρ 0 (ts a) (φ a))) :
    law P' (fun ζ => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ζ) (φ a) : ℝ^p)) =
      fieldSurr (L.dyn S) L.ρ L.A L.invβstar ts φ (gammaIdx d : ℝ) νin := by
  classical
  obtain ⟨hind, hG⟩ := hY.gaussian_part p ts φ hts hφ
  set G : Ω' → ℝ^p := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Y (ts a) ω) (φ a) -
        NegSobolev.eval (L.A • Y₀ ω) (propagator (L.dyn S) L.ρ 0 (ts a) (φ a)) with hGdef
  set h : NegSobolev d ((qT d : ℕ) : ℝ) → ℝ^p := fun F => WithLp.toLp 2 fun a =>
      NegSobolev.eval F (propagator (L.dyn S) L.ρ 0 (ts a) (φ a)) with hhdef
  have hhm : Measurable h := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
    exact Measurable.of_eval fun a => fl_eval_meas (hmemq a)
  have hVm : Measurable (h ∘ fun ζ => L.A • Y₀ ζ) := hhm.comp (hY₀.const_smul L.A)
  have hGm : Measurable G := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
    refine Measurable.of_eval fun a => ?_
    exact ((fl_eval_meas (A33.a33_memSob _ (hφ a))).comp (hY.meas (ts a))).sub
      ((fl_eval_meas (hmemq a)).comp (hY₀.const_smul L.A))
  have hind' : IndepFun (h ∘ fun ζ => L.A • Y₀ ζ) G P' :=
    (hind.comp measurable_id hhm).symm
  have hsum : (fun ζ => (WithLp.toLp 2 fun a => NegSobolev.eval (Y (ts a) ζ) (φ a) : ℝ^p)) =
      (h ∘ fun ζ => L.A • Y₀ ζ) + G := by
    funext ζ
    ext a
    simp [hhdef, hGdef]
  have hmap := hind'.map_add_eq_map_conv_map hVm hGm
  -- the law of the initial block
  have hv : Measurable fun F : NegSobolev d ((qT d : ℕ) : ℝ) =>
      (WithLp.toLp 2 fun a => L.A * NegSobolev.eval F (propagator (L.dyn S) L.ρ 0 (ts a) (φ a)) : ℝ^p) := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin p => ℝ)).measurable.comp ?_
    exact Measurable.of_eval fun a => (fl_eval_meas (hmemq a)).const_mul L.A
  have hemb : Measurable (NegSobolev.embed (d := d) (m := (gammaIdx d : ℝ)) ((qT d : ℕ) : ℝ)) :=
    (A9.a9EmbCLM (d := d) (m := (gammaIdx d : ℝ)) (m' := ((qT d : ℕ) : ℝ))
      (by unfold qT; push_cast; linarith)).continuous.measurable
  have hVlaw : Measure.map (h ∘ fun ζ => L.A • Y₀ ζ) P' =
      νin.map (statVec (L.dyn S) L.ρ L.A ts φ (gammaIdx d : ℝ)) := by
    have e1 : (h ∘ fun ζ => L.A • Y₀ ζ) = (fun F : NegSobolev d ((qT d : ℕ) : ℝ) =>
        (WithLp.toLp 2 fun a => L.A * NegSobolev.eval F
          (propagator (L.dyn S) L.ρ 0 (ts a) (φ a)) : ℝ^p)) ∘ Y₀ := by
      funext ζ; ext a; simp [hhdef, A9.a9_eval_smul]
    have e2 : (fun F : NegSobolev d ((qT d : ℕ) : ℝ) =>
        (WithLp.toLp 2 fun a => L.A * NegSobolev.eval F
          (propagator (L.dyn S) L.ρ 0 (ts a) (φ a)) : ℝ^p)) ∘
        NegSobolev.embed (d := d) (m := (gammaIdx d : ℝ)) ((qT d : ℕ) : ℝ) =
        statVec (L.dyn S) L.ρ L.A ts φ (gammaIdx d : ℝ) := by
      funext F
      unfold statVec
      simp only [Function.comp]
      congr 1
      funext a
      rw [fl_eval_embed (by unfold qT; push_cast; linarith)]
    rw [e1, ← Measure.map_map hv hY₀]
    have : Measure.map Y₀ P' = νin.map (NegSobolev.embed ((qT d : ℕ) : ℝ)) := hlaw
    rw [this, Measure.map_map hv hemb, e2]
  have hGlaw : Measure.map G P' = multivariateGaussian 0 (surrogateCov (L.dyn S) L.ρ L.invβstar ts φ) :=
    hG
  show Measure.map _ P' = _
  rw [hsum, hmap, hVlaw, hGlaw]
  rfl

end HRS.MP.FidiLaw
