import HRS.MC.E213N1

/-!
# E213N2 (e4): the global linear fluctuation solution on the product space

On `E_m × Ω_G` with `P' = ν ⊗ P_G`, `Y₀ = pr₁`, `η^t = Vev^{t,0} Y₀ + Zs^t` is an
`IsLinearFluctuationSolution` on every horizon `T` (the last bullet of `thermlin_preparedLinear_exists`
with `T' = n ≥ T`, `t25p_Zb_gaussian`, `t25p_cov_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213N

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.ThermLin

variable {d : ℕ}

theorem e213n_linearSolution {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}
    (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m)
    {Cr : ℝ} {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {G Zs : ℝ → Ω → NegSobolev d m}
    (hCr : 0 ≤ Cr) (hdual : IsDualEvolution htr.dyn ρ m Vev)
    (hplain : ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T)
    (hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → ‖Vev t r‖ ≤ Cr)
    (hN : IsGlobalNoise m β⁻¹ ρ Vev P ℱ G Zs)
    (ν : Measure (NegSobolev d m)) [IsProbabilityMeasure ν] (T : ℝ) :
    IsLinearFluctuationSolution (ν.prod P) htr.dyn ρ m β⁻¹ T (fun p => p.1)
      (fun t p => Vev t 0 p.1 + Zs t p.2) := by
  have hd1 : 1 ≤ d := by omega
  set n : ℕ := ⌈T⌉₊ + 1 with hn
  have hnpos : (0 : ℝ) < n := by rw [hn]; push_cast; positivity
  have hTn : T ≤ (n : ℝ) := by
    rw [hn]; push_cast; exact (Nat.le_ceil T).trans (le_add_of_nonneg_right zero_le_one)
  have hq : (0 : ℝ) ≤ β⁻¹ := inv_nonneg.2 htr.hβ.le
  have hVc : ∀ y : NegSobolev d m, ContinuousOn (fun p : ℝ × ℝ => Vev p.1 p.2 y)
      {p | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ (n : ℝ)} := (hplain n hnpos.le).2.2
  have h0n : (0 : ℝ) ∈ Icc (0 : ℝ) n := ⟨le_rfl, hnpos.le⟩
  have hV00 : Vev 0 0 = 1 := (hplain n hnpos.le).1 0 h0n
  have hVcont : ∀ x : NegSobolev d m, ContinuousOn (fun t => Vev t 0 x) (Icc 0 (n : ℝ)) := fun x => by
    have := (hVc x).comp (f := fun t : ℝ => ((t, 0) : ℝ × ℝ)) (by fun_prop) (s := Icc 0 (n : ℝ))
      (fun t ht => ⟨le_rfl, ht.1, ht.2⟩)
    exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- init
    have h1 : ∀ᵐ p ∂(ν.prod P), Zs 0 p.2 = 0 := (Measure.quasiMeasurePreserving_snd).ae hN.zero_Zs
    filter_upwards [h1] with p hp
    show Vev 0 0 p.1 + Zs 0 p.2 = p.1
    rw [hV00, hp]; simp
  · -- continuity
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := P)).ae (hN.contOn n)
    filter_upwards [h2] with p hp
    exact ((hVcont p.1).add hp).mono (Icc_subset_Icc_right hTn)
  · -- measurability
    intro t
    exact (((Vev t 0).continuous.measurable).comp measurable_fst).add ((hN.meas t).comp measurable_snd)
  · -- Gaussian part
    intro p ts φ hts hφ Gv
    have hts' : ∀ a, ts a ∈ Icc (0 : ℝ) n := fun a => ⟨(hts a).1, (hts a).2.trans hTn⟩
    have hmemφ : ∀ a, MemSobolev m (φ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) m
    set Gz : Ω → EuclideanSpace ℝ (Fin p) := fun ω => WithLp.toLp 2 fun a =>
      NegSobolev.eval (Zs (ts a) ω) (φ a) with hGz_def
    have hGzm : Measurable Gz :=
      HRS.Uniform.Q54c.measurable_toLp_eval fun a =>
        (HRS.Uniform.Q54c.continuous_eval_const (hmemφ a)).measurable.comp (hN.meas _)
    have hGeq : Gv = fun q => Gz q.2 := by
      funext q
      ext a
      show NegSobolev.eval (Vev (ts a) 0 q.1 + Zs (ts a) q.2) (φ a) -
        NegSobolev.eval q.1 (propagator htr.dyn ρ 0 (ts a) (φ a)) = NegSobolev.eval (Zs (ts a) q.2) (φ a)
      rw [HRS.A33.a33_eval_add_left _ _ (HRS.A33.a33_ws_smooth m (hφ a)),
        hdual 0 (ts a) le_rfl (hts a).1 q.1 (φ a) (hφ a)]
      ring
    refine ⟨?_, ?_⟩
    · rw [hGeq]
      exact (indepFun_prod (μ := ν) (ν := P) (X := (id : NegSobolev d m → NegSobolev d m)) (Y := Gz)
        measurable_id hGzm).symm
    · have hlaw : law (ν.prod P) Gv = P.map Gz := by
        rw [hGeq]
        show (ν.prod P).map (Gz ∘ Prod.snd) = P.map Gz
        rw [← Measure.map_map hGzm measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
      rw [hlaw]
      have hmain := t25p_Zb_gaussian hCr hnpos (d := d) Vev hVc
        (fun r t hr hrt htn => hKb r t hr hrt) P G (noiseDens m β⁻¹ ρ)
        (hN.mart n hnpos.le) hN.cont hN.zero Zs (fun t ht => hN.conv t ht.1) hN.meas ts hts' φ hmemφ
      rw [hmain]
      congr 1
      ext a b
      simp only [Matrix.of_apply]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Icc (fun σ hσ => ?_)
      have hσn : σ ∈ Icc (0 : ℝ) n := ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hts' a).2)⟩
      have hκ : noiseDens m β⁻¹ ρ σ = covDensT m β⁻¹ n ρ σ :=
        (E213K.e213k_covDensT_eq m β⁻¹ n ρ hσn).symm
      rw [hκ]
      exact t25p_cov_eq hd htr hm hnpos hdual hCr (fun r t hr hrt htn => hKb r t hr hrt) hq
        (hts' a) (hts' b) hσ (hφ a) (hφ b)

end HRS.MC.E213N

end
