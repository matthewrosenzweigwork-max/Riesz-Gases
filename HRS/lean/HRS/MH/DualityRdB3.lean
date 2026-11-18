import HRS.MH.DualityRdB3Aux

/-!
# DualityRd packet B3: `mf_time_dependent` (the time-dependent weak form on `ℝ^d`)

Proof scheme: with `g_r = ⟨ρ_r, ∂_r f_r + β⁻¹Δf_r - ∇V·∇f_r⟩ + B_{f_r}(ρ_r,ρ_r) = ⟨ρ_r, ∂_r f_r⟩ + mfGen(f_r, ρ_r)`
(continuous on `[0,t]`, by `mf_continuity`), the function `H_r = ⟨ρ_r, f_r⟩ - ∫_0^r g` satisfies the local bound
`|H_b - H_a| ≤ 2ε (b-a)` for `b - a ≤ s(ε)`: the increment identity (`db3_incr`: `B1` for the fixed test `f_a`, FTC and
Fubini for the time-derivative part) differs from `∫_a^b g` by two integrals whose integrands are small by uniform continuity
of `(u,r) ↦ ⟨ρ_r, ∂f_u⟩` and `(a,r) ↦ mfGen(f_a, ρ_r)` on `[0,t]²`.  Telescoping (`db3_telescope`) then gives `H_t = H_0`.
Helper names carry the prefix `db3_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.DualityRd

open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-- The integrand of the time-dependent weak form. -/
def db3_g (D : WholeDyn d) (f ft : ℝ → Euc d → ℝ) (ρ : ℝ → Euc d → ℝ) (r : ℝ) : ℝ :=
  Whole.pair (Whole.withDensityReal (ρ r)) (driftTestRd D f ft r)
    + interactionPairingW D (f r) (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r))

/-- The drift part `β⁻¹Δf - ∇V·∇f` of the test function has linear growth, uniformly in the time. -/
theorem db3_phi_growth {ΛV G₀ : ℝ} {D : WholeDyn d} (hV : VHypRd 2 ΛV G₀ D.V) {t : ℝ}
    {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft) :
    ∃ K : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) t, ∀ x : Euc d,
      |D.invβ * Laplacian.laplacian (f u) x - inner ℝ (gradient D.V x) (gradient (f u) x)|
        ≤ K * (1 + ‖x‖) := by
  obtain ⟨CL, hCL⟩ := db2_lap_unif hf
  obtain ⟨A, hA⟩ := db2_grad_unif hf
  refine ⟨|D.invβ| * |CL| + (|G₀| + |ΛV|) * |A|, fun u hu x => ?_⟩
  have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hΔ : |Laplacian.laplacian (f u) x| ≤ |CL| := (hCL u hu x).trans (le_abs_self _)
  have hg : ‖gradient (f u) x‖ ≤ |A| := (hA u hu x).trans (le_abs_self _)
  have hVg := Q09B.q09b_gradV_bound (le_refl 2) hV x
  have hV0 : 0 ≤ G₀ + ΛV * ‖x‖ := (norm_nonneg _).trans hVg
  have hb1 : |D.invβ * Laplacian.laplacian (f u) x| ≤ |D.invβ| * |CL| * (1 + ‖x‖) := by
    rw [abs_mul]
    have e1 : |D.invβ| * |Laplacian.laplacian (f u) x| ≤ |D.invβ| * |CL| :=
      mul_le_mul_of_nonneg_left hΔ (abs_nonneg _)
    have e2 : |D.invβ| * |CL| ≤ |D.invβ| * |CL| * (1 + ‖x‖) :=
      le_mul_of_one_le_right (by positivity) (by linarith)
    linarith
  have hb2 : |inner ℝ (gradient D.V x) (gradient (f u) x)| ≤ (|G₀| + |ΛV|) * |A| * (1 + ‖x‖) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have e1 : ‖gradient D.V x‖ * ‖gradient (f u) x‖ ≤ (G₀ + ΛV * ‖x‖) * |A| :=
      mul_le_mul hVg hg (norm_nonneg _) hV0
    have e2 : G₀ + ΛV * ‖x‖ ≤ (|G₀| + |ΛV|) * (1 + ‖x‖) := by
      nlinarith [le_abs_self G₀, le_abs_self ΛV, abs_nonneg G₀, abs_nonneg ΛV,
        mul_nonneg (abs_nonneg G₀) hx0, mul_le_mul_of_nonneg_right (le_abs_self ΛV) hx0]
    have e3 : (G₀ + ΛV * ‖x‖) * |A| ≤ (|G₀| + |ΛV|) * (1 + ‖x‖) * |A| :=
      mul_le_mul_of_nonneg_right e2 (abs_nonneg _)
    nlinarith [e1, e3]
  calc |D.invβ * Laplacian.laplacian (f u) x - inner ℝ (gradient D.V x) (gradient (f u) x)|
      ≤ |D.invβ * Laplacian.laplacian (f u) x| + |inner ℝ (gradient D.V x) (gradient (f u) x)| :=
        abs_sub _ _
    _ ≤ |D.invβ| * |CL| * (1 + ‖x‖) + (|G₀| + |ΛV|) * |A| * (1 + ‖x‖) := add_le_add hb1 hb2
    _ = (|D.invβ| * |CL| + (|G₀| + |ΛV|) * |A|) * (1 + ‖x‖) := by ring

/-- The increment identity: `⟨ρ_b, f_b⟩ - ⟨ρ_a, f_a⟩ = ∫_a^b ⟨ρ_b, ∂_u f_u⟩ du + ∫_a^b mfGen(f_a, ρ_r) dr`. -/
theorem db3_incr {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) :
    Whole.pair (Whole.withDensityReal (ρ b)) (f b) - Whole.pair (Whole.withDensityReal (ρ a)) (f a)
      = (∫ u in a..b, Whole.pair (Whole.withDensityReal (ρ b)) (ft u))
        + ∫ r in a..b, mfGen D (f a) (ρ r) := by
  have hbT : b ∈ Set.Icc (0 : ℝ) T := ⟨ha.trans hab, hbt.trans ht.2⟩
  have haI : a ∈ Set.Icc (0 : ℝ) t := ⟨ha, hab.trans hbt⟩
  have hbI : b ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans hab, hbt⟩
  have hρb := h.hρ.density b hbT
  have hWeak := (mf_weak_integrable_proof h (hf.memCb haI)).2.2 a b ha hab (hbt.trans ht.2)
  have hm2 : Integrable (fun x => ρ b x * ‖x‖ ^ 2) := (db1_slice h hbT).2.2.1
  obtain ⟨B, hB⟩ := hf.lin_growth
  have hfb_cont : Continuous (f b) := (hf.c2 b hbI).continuous
  have hfa_cont : Continuous (f a) := (hf.c2 a haI).continuous
  have hi1 : Integrable (fun x => ρ b x * f b x) :=
    db3_int_bdd hρb hfb_cont (C := HRS.cbNorm 2 (f b)) fun x => db1_abs_le_cbNorm (hf.memCb hbI) x
  have hi2 : Integrable (fun x => ρ b x * f a x) :=
    db3_int_bdd hρb hfa_cont (C := HRS.cbNorm 2 (f a)) fun x => db1_abs_le_cbNorm (hf.memCb haI) x
  have hfirst : Whole.pair (Whole.withDensityReal (ρ b)) (f b)
      - Whole.pair (Whole.withDensityReal (ρ b)) (f a)
      = ∫ x, ρ b x * (∫ u in a..b, ft u x) := by
    rw [Q09A.pair_withDensityReal hρb, Q09A.pair_withDensityReal hρb, ← integral_sub hi1 hi2]
    congr 1
    funext x
    rw [db3_ftc hf ha hab hbt x]
    ring
  have hsplit : Whole.pair (Whole.withDensityReal (ρ b)) (f b) - Whole.pair (Whole.withDensityReal (ρ a)) (f a)
      = (Whole.pair (Whole.withDensityReal (ρ b)) (f b) - Whole.pair (Whole.withDensityReal (ρ b)) (f a))
        + (Whole.pair (Whole.withDensityReal (ρ b)) (f a) - Whole.pair (Whole.withDensityReal (ρ a)) (f a)) := by
    ring
  rw [hsplit, hfirst, hWeak, db3_fubini hρb hm2 ht.1 hf.cont_time_deriv hB ha hab hbt]

/-- The pointwise form of the integrand: `g_r = ⟨ρ_r, ∂_r f_r⟩ + mfGen(f_r, ρ_r)` on `[0,t]`. -/
theorem db3_g_eq {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ} (h : MFData s Λ T ΛV G₀ D ρ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {f ft : ℝ → Euc d → ℝ} (hf : IsC12TestRd t f ft)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) :
    db3_g D f ft ρ r = Whole.pair (Whole.withDensityReal (ρ r)) (ft r) + mfGen D (f r) (ρ r) := by
  have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
  have hρr := h.hρ.density r hrT
  have hm2 : Integrable (fun x => ρ r x * ‖x‖ ^ 2) := (db1_slice h hrT).2.2.1
  obtain ⟨Bt, hBt⟩ := hf.lin_growth
  obtain ⟨K, hK⟩ := db3_phi_growth h.hV hf
  have hV2 : ContDiff ℝ 2 D.V := h.hV.1.of_le (by norm_num)
  have hftc : Continuous (ft r) := db2_slice_cont (φ := ft) (db2_contOn_subtype hf.cont_time_deriv) hr
  have hφcont : Continuous (fun x => D.invβ * Laplacian.laplacian (f r) x
      - inner ℝ (gradient D.V x) (gradient (f r) x)) :=
    (continuous_const.mul (db1_laplacian_continuous (hf.c2 r hr))).sub
      ((db1_gradient_continuous hV2).inner (db1_gradient_continuous (hf.c2 r hr)))
  have hint1 : Integrable (fun x => ρ r x * ft r x) := db3_int_lin hρr hm2 hftc (hBt r hr)
  have hint2 : Integrable (fun x => ρ r x * (D.invβ * Laplacian.laplacian (f r) x
      - inner ℝ (gradient D.V x) (gradient (f r) x))) := db3_int_lin hρr hm2 hφcont (hK r hr)
  have hdrift : driftTestRd D f ft r = fun x => ft r x + (D.invβ * Laplacian.laplacian (f r) x
      - inner ℝ (gradient D.V x) (gradient (f r) x)) := by
    funext x
    unfold driftTestRd
    ring
  unfold db3_g
  rw [hdrift, db3_pair_add hint1 hint2 hρr]
  unfold mfGen
  ring

/-- Abstract local estimate: an increment identity with two "diagonal" integrals whose integrands are close on
short intervals, by uniform continuity of `(u,b) ↦ A u b` and `(a,r) ↦ B a r` on `[0,t]²`. -/
theorem db3_local {t : ℝ} {H : ℝ → ℝ} {A B : ℝ → ℝ → ℝ} {g : ℝ → ℝ}
    (hA : ContinuousOn (fun p : ℝ × ℝ => A p.1 p.2) (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t))
    (hB : ContinuousOn (fun p : ℝ × ℝ => B p.1 p.2) (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t))
    (hgd : ∀ r ∈ Set.Icc (0 : ℝ) t, g r = A r r + B r r)
    (hinc : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ t →
      H b - H a = (∫ u in a..b, A u b) + (∫ r in a..b, B a r) - ∫ u in a..b, g u) :
    ∀ ε' > 0, ∃ s > 0, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ t → b - a ≤ s →
      |H b - H a| ≤ 2 * ε' * (b - a) := by
  intro ε' hε'
  have hS : IsCompact (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨η1, hη1, hU1⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hA) ε' hε'
  obtain ⟨η2, hη2, hU2⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hB) ε' hε'
  have hcd : ContinuousOn (fun r : ℝ => ((r, r) : ℝ × ℝ)) (Set.Icc (0 : ℝ) t) :=
    (continuous_id.prodMk continuous_id).continuousOn
  have hdA : ContinuousOn (fun u : ℝ => A u u) (Set.Icc (0 : ℝ) t) :=
    hA.comp hcd (fun r hr => ⟨hr, hr⟩)
  have hdB : ContinuousOn (fun u : ℝ => B u u) (Set.Icc (0 : ℝ) t) :=
    hB.comp hcd (fun r hr => ⟨hr, hr⟩)
  have hgC : ContinuousOn g (Set.Icc (0 : ℝ) t) :=
    (hdA.add hdB).congr (fun r hr => hgd r hr)
  refine ⟨min η1 η2 / 2, half_pos (lt_min hη1 hη2), fun a b ha hab hbt hba => ?_⟩
  have hs1 : min η1 η2 / 2 < η1 := by linarith [min_le_left η1 η2]
  have hs2 : min η1 η2 / 2 < η2 := by linarith [min_le_right η1 η2]
  have haI : a ∈ Set.Icc (0 : ℝ) t := ⟨ha, hab.trans hbt⟩
  have hbI : b ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans hab, hbt⟩
  have hab' : |b - a| = b - a := abs_of_nonneg (sub_nonneg.2 hab)
  -- slices at the endpoints `a` and `b`
  have hcu : ContinuousOn (fun u : ℝ => ((u, b) : ℝ × ℝ)) (Set.Icc (0 : ℝ) t) :=
    (continuous_id.prodMk continuous_const).continuousOn
  have hca : ContinuousOn (fun u : ℝ => ((a, u) : ℝ × ℝ)) (Set.Icc (0 : ℝ) t) :=
    (continuous_const.prodMk continuous_id).continuousOn
  have hAb : ContinuousOn (fun u : ℝ => A u b) (Set.Icc (0 : ℝ) t) :=
    hA.comp hcu (fun u hu => ⟨hu, hbI⟩)
  have hBa : ContinuousOn (fun u : ℝ => B a u) (Set.Icc (0 : ℝ) t) :=
    hB.comp hca (fun u hu => ⟨haI, hu⟩)
  have hI1 : IntervalIntegrable (fun u => A u b) MeasureTheory.volume a b :=
    (hAb.mono (Set.uIcc_subset_Icc haI hbI)).intervalIntegrable
  have hI2 : IntervalIntegrable (fun u => B a u) MeasureTheory.volume a b :=
    (hBa.mono (Set.uIcc_subset_Icc haI hbI)).intervalIntegrable
  have hIdA : IntervalIntegrable (fun u => A u u) MeasureTheory.volume a b :=
    (hdA.mono (Set.uIcc_subset_Icc haI hbI)).intervalIntegrable
  have hIdB : IntervalIntegrable (fun u => B u u) MeasureTheory.volume a b :=
    (hdB.mono (Set.uIcc_subset_Icc haI hbI)).intervalIntegrable
  have hgint : ∫ u in a..b, g u = (∫ u in a..b, A u u) + ∫ u in a..b, B u u := by
    calc ∫ u in a..b, g u = ∫ u in a..b, (A u u + B u u) :=
          intervalIntegral.integral_congr (fun u hu => by
            have hu' : u ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hu
            exact hgd u ⟨ha.trans hu'.1, hu'.2.trans hbt⟩)
      _ = _ := intervalIntegral.integral_add hIdA hIdB
  have e1 : ∫ u in a..b, (A u b - A u u) = (∫ u in a..b, A u b) - ∫ u in a..b, A u u :=
    intervalIntegral.integral_sub hI1 hIdA
  have e2 : ∫ r in a..b, (B a r - B r r) = (∫ r in a..b, B a r) - ∫ r in a..b, B r r :=
    intervalIntegral.integral_sub hI2 hIdB
  have hdiff : H b - H a
      = (∫ u in a..b, (A u b - A u u)) + ∫ r in a..b, (B a r - B r r) := by
    rw [e1, e2, hinc a b ha hab hbt, hgint]
    ring
  -- first integral
  have hb1 : |∫ u in a..b, (A u b - A u u)| ≤ ε' * (b - a) := by
    rw [← Real.norm_eq_abs, ← hab']
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => ?_)
    show ‖A u b - A u u‖ ≤ ε'
    rw [Set.uIoc_of_le hab] at hu
    have hu0 : u ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans hu.1.le, hu.2.trans hbt⟩
    have hdist : dist ((u, b) : ℝ × ℝ) (u, u) < η1 := by
      rw [Prod.dist_eq]
      show max (dist u u) (dist b u) < η1
      rw [dist_self, Real.dist_eq, max_lt_iff]
      refine ⟨hη1, ?_⟩
      rw [abs_of_nonneg (sub_nonneg.2 hu.2)]
      linarith [hu.1]
    have hd := hU1 (u, b) ⟨hu0, hbI⟩ (u, u) ⟨hu0, hu0⟩ hdist
    rw [← dist_eq_norm]
    exact hd.le
  -- second integral
  have hb2 : |∫ r in a..b, (B a r - B r r)| ≤ ε' * (b - a) := by
    rw [← Real.norm_eq_abs, ← hab']
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun r hr => ?_)
    show ‖B a r - B r r‖ ≤ ε'
    rw [Set.uIoc_of_le hab] at hr
    have hr0 : r ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans hr.1.le, hr.2.trans hbt⟩
    have hdist : dist ((a, r) : ℝ × ℝ) (r, r) < η2 := by
      rw [Prod.dist_eq]
      show max (dist a r) (dist r r) < η2
      rw [dist_self, Real.dist_eq, max_lt_iff]
      refine ⟨?_, hη2⟩
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hr.1.le)]
      linarith [hr.2]
    have hd := hU2 (a, r) ⟨haI, hr0⟩ (r, r) ⟨hr0, hr0⟩ hdist
    rw [← dist_eq_norm]
    exact hd.le
  rw [hdiff]
  calc |(∫ u in a..b, (A u b - A u u)) + ∫ r in a..b, (B a r - B r r)|
      ≤ |∫ u in a..b, (A u b - A u u)| + |∫ r in a..b, (B a r - B r r)| := abs_add_le _ _
    _ ≤ ε' * (b - a) + ε' * (b - a) := add_le_add hb1 hb2
    _ = 2 * ε' * (b - a) := by ring

/-- The primitive of the integrand: its continuity on `[0,t]`, and the local estimate, give the claim. -/
theorem mf_time_dependent_proof {s Λ T ΛV G₀ : ℝ} {D : WholeDyn d} {ρ : ℝ → Euc d → ℝ}
    (h : MFData s Λ T ΛV G₀ D ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) {f ft : ℝ → Euc d → ℝ}
    (hf : IsC12TestRd t f ft) :
    ∀ τ ∈ Set.Icc (0 : ℝ) t,
      IntegrableOn (fun r => Whole.pair (Whole.withDensityReal (ρ r)) (driftTestRd D f ft r)
        + interactionPairingW D (f r) (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r)))
        (Set.Icc 0 τ) ∧
      Whole.pair (Whole.withDensityReal (ρ τ)) (f τ)
        = Whole.pair (Whole.withDensityReal (ρ 0)) (f 0)
          + ∫ r in Set.Icc (0 : ℝ) τ, (Whole.pair (Whole.withDensityReal (ρ r)) (driftTestRd D f ft r)
              + interactionPairingW D (f r) (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r))) := by
  intro τ hτ
  have hftJ : ContinuousOn (Function.uncurry ft) (Set.Icc (0 : ℝ) t ×ˢ Set.univ) :=
    db2_contOn_subtype hf.cont_time_deriv
  obtain ⟨Bt, hBt⟩ := hf.lin_growth
  have hPft : ContinuousOn (fun p : ℝ × ℝ => Whole.pair (Whole.withDensityReal (ρ p.2)) (ft p.1))
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) :=
    (mf_continuity_proof h).2.1 t ht ft hftJ ⟨Bt, hBt⟩
  have hMf : ContinuousOn (fun p : ℝ × ℝ => mfGen D (f p.1) (ρ p.2))
      (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) :=
    (mf_continuity_proof h).2.2 t ht f ft hf
  have hdiag : ∀ F : ℝ × ℝ → ℝ, ContinuousOn F (Set.Icc (0 : ℝ) t ×ˢ Set.Icc (0 : ℝ) t) →
      ContinuousOn (fun r => F (r, r)) (Set.Icc (0 : ℝ) t) := fun F hF =>
    hF.comp (continuousOn_id.prodMk continuousOn_id) (fun r hr => ⟨hr, hr⟩)
  have hPd : ContinuousOn (fun r => Whole.pair (Whole.withDensityReal (ρ r)) (ft r)) (Set.Icc (0 : ℝ) t) :=
    hdiag _ hPft
  have hMd : ContinuousOn (fun r => mfGen D (f r) (ρ r)) (Set.Icc (0 : ℝ) t) := hdiag _ hMf
  have hgC : ContinuousOn (db3_g D f ft ρ) (Set.Icc (0 : ℝ) t) :=
    (hPd.add hMd).congr (fun r hr => db3_g_eq h ht hf hr)
  have hgI : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) t → b ∈ Set.Icc (0 : ℝ) t →
      IntervalIntegrable (db3_g D f ft ρ) MeasureTheory.volume a b := fun a b ha hb =>
    (hgC.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  -- the primitive `H_r = ⟨ρ_r, f_r⟩ - ∫_0^r g`
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, ∀ r, H r = Whole.pair (Whole.withDensityReal (ρ r)) (f r)
      - ∫ u in (0 : ℝ)..r, db3_g D f ft ρ u := ⟨_, fun r => rfl⟩
  -- the increment identity, in the form used by the local estimate
  have hinc : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ t →
      H b - H a = (∫ u in a..b, Whole.pair (Whole.withDensityReal (ρ b)) (ft u))
        + (∫ r in a..b, mfGen D (f a) (ρ r)) - ∫ u in a..b, db3_g D f ft ρ u := by
    intro a b ha hab hbt
    have haI : a ∈ Set.Icc (0 : ℝ) t := ⟨ha, hab.trans hbt⟩
    have hbI : b ∈ Set.Icc (0 : ℝ) t := ⟨ha.trans hab, hbt⟩
    have h0I : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.1⟩
    have hincr := db3_incr h ht hf ha hab hbt
    have hadd : ∫ u in (0 : ℝ)..b, db3_g D f ft ρ u
        = (∫ u in (0 : ℝ)..a, db3_g D f ft ρ u) + ∫ u in a..b, db3_g D f ft ρ u :=
      (intervalIntegral.integral_add_adjacent_intervals (hgI 0 a h0I haI) (hgI a b haI hbI)).symm
    rw [hH b, hH a]
    linarith [hincr, hadd]
  have hloc := db3_local (t := t) (H := H) (A := fun u b => Whole.pair (Whole.withDensityReal (ρ b)) (ft u))
    (B := fun a r => mfGen D (f a) (ρ r)) (g := db3_g D f ft ρ) hPft hMf
    (fun r hr => db3_g_eq h ht hf hr) hinc
  -- telescoping: `H_τ = H_0`
  have hkey : ∀ ε' > 0, |H τ - H 0| ≤ 2 * ε' * τ := by
    intro ε' hε'
    obtain ⟨s, hs, hlo⟩ := hloc ε' hε'
    obtain ⟨n, hn⟩ := exists_nat_ge (τ / s)
    have hτn : τ ≤ n * s := (div_le_iff₀ hs).1 hn
    exact db3_telescope hs hlo n τ hτ.1 hτ.2 hτn
  have hzero : H τ = H 0 := by
    by_contra hne
    have hc : 0 < |H τ - H 0| := abs_pos.2 (sub_ne_zero.2 hne)
    have ht0 : 0 ≤ t := le_trans hτ.1 hτ.2
    have ht1 : t + 1 ≠ 0 := (by linarith : (0 : ℝ) < t + 1).ne'
    have hpos : 0 < |H τ - H 0| / (4 * (t + 1)) := div_pos hc (by linarith)
    have h1 := hkey _ hpos
    have hτt : τ ≤ t + 1 := by linarith [hτ.2]
    have e : 2 * (|H τ - H 0| / (4 * (t + 1))) * (t + 1) = |H τ - H 0| / 2 := by
      field_simp
      ring
    have h2 : 2 * (|H τ - H 0| / (4 * (t + 1))) * τ ≤ 2 * (|H τ - H 0| / (4 * (t + 1))) * (t + 1) :=
      mul_le_mul_of_nonneg_left hτt (mul_nonneg (by norm_num) hpos.le)
    linarith
  have hH0 : H 0 = Whole.pair (Whole.withDensityReal (ρ 0)) (f 0) := by
    rw [hH 0, intervalIntegral.integral_same, sub_zero]
  have hτ' : H τ = Whole.pair (Whole.withDensityReal (ρ τ)) (f τ) - ∫ u in (0 : ℝ)..τ, db3_g D f ft ρ u :=
    hH τ
  refine ⟨?_, ?_⟩
  · exact (hgC.mono (Set.Icc_subset_Icc le_rfl hτ.2)).integrableOn_Icc
  · have hint : ∫ u in (0 : ℝ)..τ, db3_g D f ft ρ u = ∫ r in Set.Icc (0 : ℝ) τ, db3_g D f ft ρ r := by
      rw [intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]
    have hfin : Whole.pair (Whole.withDensityReal (ρ τ)) (f τ)
        = Whole.pair (Whole.withDensityReal (ρ 0)) (f 0) + ∫ u in (0 : ℝ)..τ, db3_g D f ft ρ u := by
      linarith [hzero, hτ', hH0]
    rw [hint] at hfin
    exact hfin

end HRS.MH.DualityRd
