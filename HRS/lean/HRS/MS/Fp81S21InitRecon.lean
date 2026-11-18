import HRS.MS.Fp81S21CosRecon2
import HRS.MS.Fp81S21InitialWindow2
import HRS.MS.Fp81S21InitialIid

/-!
# S2.1(iii): reconstruction of the transported initial particle window

The exact definitions used here are:

```lean
def initialWindow (R : Trajectory p δ) (N : ℕ) (b : ℝ)
    (X : EucConfig p.d N) : Window p :=
  windowPathOf (wholeSpaceIndex p.d) p.T b (fun t =>
    r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) t 0
      (initialFunctional R N X))

def r26t3_W (R : Trajectory p δ) (q : ℕ → Euc p.d → ℝ)
    (N : ℕ) : EucConfig p.d N → SeqL2 :=
  featureVec q (r26t3_marg R N)

def meanEmpirical (P : Measure (EucConfig d N)) : Measure (Euc d) :=
  P.bind empirical

def firstMarginal (P : Measure (EucConfig d N)) : Measure (Euc d) :=
  if h : 0 < N then P.map (fun X => X ⟨0, h⟩) else 0

def r26t3_Q (R : Trajectory p δ) (N : ℕ) : Measure (EucConfig p.d N) :=
  HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d p.s) N p.γ
    (r26t3_mu R 0)
```

Thus `meanEmpirical` is `Q.bind empirical`, while `r26t3_marg` is the first
coordinate pushforward of `Q` (for positive `N`). The actual `Q` is the
modulated Gibbs law above. Its kernel is even, hence `Q` is exchangeable; when
`Q` is a probability measure, `meanEmpirical_eq_firstMarginal` identifies the
two measures. For `0 < p.γ`, `r26t3_static_pressure` supplies that probability
instance. For `p.γ = 0`, `fp81s21_initial_iid_Q` identifies `Q` with the
product of the actual initial marginal, which is a probability measure by the
reference-density data.

The reconstruction in this file concerns this transported initial window.
It does not identify it with the full evolving fluctuation path.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3
open HRS.MS.S21
open HRS.MS.CovMeas HRS.MS.R2Interp

variable {p : Parameters} {δ : ℝ}

/-- The actual preparation is exchangeable, so its empirical mean is its
first marginal. This includes the independent `γ = 0` endpoint. -/
theorem fp81s21_initRecon_meanEmpirical_marg
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ ∨ p.γ = 0) (N : ℕ) (hN : 2 ≤ N) :
    HRS.Whole.meanEmpirical (r26t3_Q R N) = r26t3_marg R N := by
  have hdens := (r26t3_reference_data p δ hδ hδhalf R).2.2.1 0 le_rfl
  have hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    s11iid_prob hdens.1.nonneg hdens.1.integral_one
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rcases hγ with hpos | hzero
    · exact (r26t3_static_pressure hδ hδhalf R hpos).1 N hN
    · letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
      rw [fp81s21_initial_iid_Q hδ hδhalf R hzero N]
      infer_instance
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hEx : HRS.Whole.IsExchangeable (r26t3_Q R N) := by
    change HRS.Whole.IsExchangeable
      (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d p.s) N p.γ
        (r26t3_mu R 0))
    exact HRS.Whole.modulatedGibbs_isExchangeable _ _ _
      (S45.s45_rieszKernel_even p.s)
  change HRS.Whole.meanEmpirical (r26t3_Q R N) =
    HRS.Whole.firstMarginal (r26t3_Q R N)
  rcases hγ with hpos | hzero
  · exact HRS.Whole.meanEmpirical_eq_firstMarginal _ hEx (by omega)
  · change HRS.Whole.meanEmpirical (r26t3_Q R N) = r26t3_marg R N
    calc HRS.Whole.meanEmpirical (r26t3_Q R N) =
          HRS.Whole.meanEmpirical (Measure.pi fun _ : Fin N => r26t3_mu R 0) := by
            rw [fp81s21_initial_iid_Q hδ hδhalf R hzero N]
      _ = r26t3_mu R 0 :=
        HRS.Whole.s11iid_meanEmpirical_pi N (by omega) (r26t3_mu R 0)
      _ = r26t3_marg R N :=
        (fp81s21_initial_iid_marg hδ hδhalf R hzero N (by omega)).symm

/-- The concrete sequence coordinates of `r26t3_W`, with the actual
first marginal as its centering measure. -/
theorem fp81s21_initRecon_W_coordinate
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ ∨ p.γ = 0) (N : ℕ) (hN : 2 ≤ N)
    (q : ℕ → Euc p.d → ℝ)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) q)
    (X : EucConfig p.d N) (j : ℕ) :
    SeqL2.coord (r26t3_W R q N X) j =
      Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (q j) -
        HRS.Whole.pair (r26t3_marg R N) (q j)) := by
  have hN1 : 1 ≤ N := by omega
  have hdens := (r26t3_reference_data p δ hδ hδhalf R).2.2.1 0 le_rfl
  have hμ : IsProbabilityMeasure (r26t3_mu R 0) :=
    s11iid_prob hdens.1.nonneg hdens.1.integral_one
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rcases hγ with hpos | hzero
    · exact (r26t3_static_pressure hδ hδhalf R hpos).1 N hN
    · letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
      rw [fp81s21_initial_iid_Q hδ hδhalf R hzero N]
      infer_instance
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  haveI : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  unfold r26t3_W
  exact S45.s45_coord_ofSeq (S45.s45_feature_memℓp hN1 hq X) j

private theorem fp81s21_initRecon_zero_initialCoord
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : p.γ = 0) (N : ℕ) (hN : 2 ≤ N) (a : ℝ) (ha : 0 ≤ a)
    {c : MultiIndex p.d → ℝ}
    (hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
      (a + p.T) (2 * p.d + 8) c)
    (X : EucConfig p.d N) :
    ∀ t : Set.Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
      OscDual.coord (OscPath.at' (initialWindow R N a X) t) α =
        Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X)
              (r26t3_U R 0 (a + (t : ℝ))
                (oscTestFun (wholeSpaceIndex p.d) α)) -
            HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
              (r26t3_U R 0 (a + (t : ℝ))
                (oscTestFun (wholeSpaceIndex p.d) α))) := by
  classical
  let H : ℝ := a + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT, ha]
  obtain ⟨M, c, S, hc, hTc⟩ :=
    (r26t3_reference_data p δ hδ hδhalf R).2.2.2 (wholeSpaceIndex p.d)
  have hgauss : HRS.Whole.HasR2GaussianUpper M c (R.ρ 0) :=
    ⟨hc, hTc.gauss⟩
  obtain ⟨CM, hCM⟩ := HRS.MS.R2Chaos.s94_moment_rpow hTc.prob hgauss
    (a := (wholeSpaceIndex p.d : ℝ)) (by positivity)
  let μ : Measure (Euc p.d) := r26t3_mu R 0
  let f : Euc p.d → ℝ := fun x => jbracket x ^ (wholeSpaceIndex p.d : ℝ)
  haveI hμ : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hfmeas : Measurable f := by
    dsimp [f]
    exact (((by
      unfold jbracket
      fun_prop : Continuous fun x : Euc p.d => jbracket x).rpow_const
        (fun x => Or.inl (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne')).measurable)
  have hfnonneg : ∀ x, 0 ≤ f x := by
    intro x
    exact Real.rpow_nonneg (by
      have := HRS.MS.R2Poly.s95_one_le_jb x
      positivity) _
  have hfμ : Integrable f μ := by
    refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hfnonneg)]
    exact lt_of_le_of_lt hCM ENNReal.ofReal_lt_top
  have hmean : HRS.Whole.meanEmpirical (r26t3_Q R N) = μ := by
    change HRS.Whole.meanEmpirical (r26t3_Q R N) = r26t3_mu R 0
    rw [fp81s21_initial_iid_Q hδ hδhalf R hγ N]
    exact HRS.Whole.s11iid_meanEmpirical_pi N (by omega) (r26t3_mu R 0)
  have hMoment : Integrable
      (fun x : Euc p.d => jbracket x ^ (wholeSpaceIndex p.d : ℝ))
      (HRS.Whole.meanEmpirical (r26t3_Q R N)) := by
    simpa only [μ, f] using hmean ▸ hfμ
  have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
  have hP0 : 0 ≤ (wholeSpaceIndex p.d : ℝ) := by positivity
  have hdreal : 0 ≤ (p.d : ℝ) := Nat.cast_nonneg _
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 8 : ℕ) := by
    push_cast
    nlinarith [hdreal]
  have hNpos : 0 < N := by omega
  have hZ : ∀ Y : EucConfig p.d N,
      S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ)
        (initialFunctional R N Y) := by
    intro Y
    change S102Z (2 * p.d + 8) (wholeSpaceIndex p.d : ℝ)
      (fun f => Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical Y) f -
          HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N)) f))
    exact s102_Z_fluct hd1 hP0 (2 * p.d + 8) hr hNpos Y
      (HRS.Whole.meanEmpirical (r26t3_Q R N)) hMoment (Real.sqrt N)
  have hlin : S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H := by
    intro u t hu hut _htT φ ψ c hφ hψ
    have h := fp81s21_U_linear_of_hermite_combo p R hφ hψ c
      (t := t) (r := u) (le_trans hu hut) ⟨hu, hut⟩
    have hfun : φ + c • ψ = (fun x => φ x + c * ψ x) := by
      funext x
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    funext x
    change propagatorW (r26t3_coeff R) u t (φ + c • ψ) x = _
    rw [hfun]
    exact congrFun h x
  have hPw : (p.d : ℝ) < 2 * (wholeSpaceIndex p.d : ℝ) := by
    dsimp [HRS.Whole.wholeSpaceIndex]
    push_cast
    nlinarith [p.hd]
  let z : (Euc p.d → ℝ) → ℝ := initialFunctional R N X
  have hVcont : ContinuousOn
      (fun s => r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) s 0 z)
      (Icc (0 : ℝ) H) :=
    s102_Vprop_continuousOn hPw hD (hZ X) hlin
      (u := 0) ⟨le_rfl, hH.le⟩
  let θ : Icc (0 : ℝ) p.T → Icc (0 : ℝ) H := fun t =>
    ⟨a + (t : ℝ), ⟨add_nonneg ha t.2.1, by
      dsimp [H]
      linarith [t.2.2]⟩⟩
  have hθ : Continuous θ := by
    change Continuous (fun t : Icc (0 : ℝ) p.T =>
      (⟨a + (t : ℝ), _⟩ : Icc (0 : ℝ) H))
    fun_prop
  have hpath : Continuous (fun t : Icc (0 : ℝ) p.T =>
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (a + (t : ℝ)) 0 z) := by
    change Continuous (fun t =>
      r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) (θ t) 0 z)
    exact (continuousOn_iff_continuous_restrict.mp hVcont).comp hθ
  have hWindow : initialWindow R N a X =
      (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (a + (t : ℝ)) 0 (initialFunctional R N X), hpath⟩ : Window p) := by
    unfold initialWindow windowPathOf
    change (if h : Continuous (fun t : Icc (0 : ℝ) p.T =>
        r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
          (a + (t : ℝ)) 0 (initialFunctional R N X)) then
        (⟨fun t : Icc (0 : ℝ) p.T =>
          r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
            (a + (t : ℝ)) 0 (initialFunctional R N X), h⟩ : Window p)
      else 0) = _
    exact dif_pos hpath
  intro t α
  rw [hWindow]
  change OscDual.coord
      (r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d)
        (a + (t : ℝ)) 0 (initialFunctional R N X)) α = _
  have hs : a + (t : ℝ) ∈ Icc (0 : ℝ) H := by
    constructor
    · linarith [ha, t.2.1]
    · dsimp [H]
      linarith [t.2.2]
  have hcoord := s102_Vprop_coord hPw hD (hZ X) hlin
    (u := 0) ⟨le_rfl, hH.le⟩ hs α
  rw [hcoord]
  exact fp81s21_initial_functional_formula R N X (a + (t : ℝ)) α

private theorem fp81s21_initRecon_path_eq_of_data
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ ∨ p.γ = 0) (N : ℕ) (hN : 2 ≤ N)
    (a : ℝ) (ha : 0 ≤ a) (X : EucConfig p.d N)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a))
    (hshift : ∀ u : Set.Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
      ∀ x : Euc p.d,
        HasSum (fun n => r26t3_cosine p.T n u * s21f_w n *
          r26t3_qwin R a ((r26t3_feature_enum p.d).symm (n, α)) x)
          (r26t3_U R 0 (a + (u : ℝ))
            (oscTestFun (wholeSpaceIndex p.d) α) x))
    (hinitCoord : ∀ t : Set.Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
      OscDual.coord (OscPath.at' (initialWindow R N a X) t) α =
        Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X)
              (r26t3_U R 0 (a + (t : ℝ))
                (oscTestFun (wholeSpaceIndex p.d) α)) -
            HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
              (r26t3_U R 0 (a + (t : ℝ))
                (oscTestFun (wholeSpaceIndex p.d) α)))) :
    s21gPhi (r26t3_feature_enum p.d) p.hT
        ((wholeSpaceIndex p.d : ℕ) : ℝ)
        (r26t3_W R (r26t3_qwin R a) N X) = initialWindow R N a X := by
  let σ := r26t3_feature_enum p.d
  let U : MultiIndex p.d → ℝ → Euc p.d → ℝ := fun α t x =>
    r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d) α) x
  let D : HRS.Whole.S11pData p.d := {
    f := fun q x => r26t3_qwin R a (σ.symm q) x
    w := fun q => 2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a (σ.symm q))
    hw := by
      have hsum := (hq.2.mul_left 2).comp_injective σ.symm.injective
      change Summable (fun q : FeatureIndex p.d =>
        2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a (σ.symm q)))
      change Summable (fun q : FeatureIndex p.d =>
        (fun i : ℕ => 2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a i))
          (σ.symm q)) at hsum
      exact hsum
    hfw := by
      intro q x
      have h := HRS.MS.Tc5.tc5_cb_sup_le (hq.1 (σ.symm q)) x
      rw [Real.norm_eq_abs] at h
      exact h.trans (by
        have hn := HRS.MS.Tc5.tc5_cb_nonneg (r26t3_J p.d)
          (r26t3_qwin R a (σ.symm q))
        linarith)
    hfc := by
      intro q
      exact (hq.1 (σ.symm q)).1.continuous
  }
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rcases hγ with hpos | hzero
    · exact (r26t3_static_pressure hδ hδhalf R hpos).1 N hN
    · have hdens := (r26t3_reference_data p δ hδ hδhalf R).2.2.1 0 le_rfl
      haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
        s11iid_prob hdens.1.nonneg hdens.1.integral_one
      rw [fp81s21_initial_iid_Q hδ hδhalf R hzero N]
      infer_instance
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  have hmeanMarg := fp81s21_initRecon_meanEmpirical_marg
    hδ hδhalf R hγ N hN
  letI : IsProbabilityMeasure (HRS.Whole.empirical X) :=
    HRS.Whole.empirical_isProbabilityMeasure (by omega) X
  letI : IsProbabilityMeasure (HRS.Whole.meanEmpirical (r26t3_Q R N)) :=
    HRS.Whole.meanEmpirical_isProbabilityMeasure (r26t3_Q R N) (by omega)
  have hU : HRS.Whole.S11pSeries D p.T U := by
    intro α t ht x
    have hcos (n : ℕ) (v : ℝ) : r26t3_cosine p.T n v = r2CosBasis p.T n v := by
      unfold r26t3_cosine r2CosBasis
      split_ifs <;> simp [one_div]
    have hkap (n : ℕ) : HRS.Whole.s11p_kap n = s21f_w n := by
      unfold HRS.Whole.s11p_kap HRS.MS.R26T3.s21f_w
      congr 1
      norm_num
    have hterms : ∀ n : ℕ,
        HRS.Whole.s11p_kap n * r2CosBasis p.T n t * D.f (n, α) x =
          r26t3_cosine p.T n t * s21f_w n *
            r26t3_qwin R a (σ.symm (n, α)) x := by
      intro n
      rw [hkap, hcos]
      dsimp [D]
      ring
    simpa only [U, hterms] using hshift ⟨t, ht⟩ α x
  have hN1 : 1 ≤ N := by omega
  have hcoord : ∀ t : Set.Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
      OscDual.coord (OscPath.at' (s21gPhi σ p.hT
        ((wholeSpaceIndex p.d : ℕ) : ℝ)
        (r26t3_W R (r26t3_qwin R a) N X)) t) α =
        OscDual.coord (OscPath.at' (initialWindow R N a X) t) α := by
    intro t α
    let hEmp := HRS.Whole.s11p_mu_series p.hT hU α (t : ℝ) t.2
      (μ := HRS.Whole.empirical X)
    let hMean := HRS.Whole.s11p_mu_series p.hT hU α (t : ℝ) t.2
      (μ := HRS.Whole.meanEmpirical (r26t3_Q R N))
    have hSeries := (hEmp.sub hMean).mul_left (Real.sqrt N)
    have hTheta : ∀ n : ℕ,
        (s21gTheta σ (r26t3_W R (r26t3_qwin R a) N X)).c (n, α) =
          SeqL2.coord (r26t3_W R (r26t3_qwin R a) N X) (σ.symm (n, α)) := by
      intro n
      have h := s21gTheta_c σ
        (r26t3_W R (r26t3_qwin R a) N X) (σ.symm (n, α))
      simpa using h
    have hTerms : ∀ n : ℕ,
        HRS.Whole.s11p_kap n * r2CosBasis p.T n (t : ℝ) *
            SeqL2.coord (r26t3_W R (r26t3_qwin R a) N X) (σ.symm (n, α)) =
          Real.sqrt N *
            (HRS.Whole.s11p_kap n * r2CosBasis p.T n (t : ℝ) *
                HRS.Whole.pair (HRS.Whole.empirical X)
                  (r26t3_qwin R a (σ.symm (n, α))) -
              HRS.Whole.s11p_kap n * r2CosBasis p.T n (t : ℝ) *
                HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
                  (r26t3_qwin R a (σ.symm (n, α)))) := by
      intro n
      rw [fp81s21_initRecon_W_coordinate hδ hδhalf R hγ N hN
        (r26t3_qwin R a) hq X (σ.symm (n, α))]
      rw [← hmeanMarg]
      simp only [HRS.Whole.pair]
      ring
    have hSynth := s21gPhi_coord σ p.hT
      ((wholeSpaceIndex p.d : ℕ) : ℝ)
      (r26t3_W R (r26t3_qwin R a) N X) t α
    rw [hSynth]
    calc (∑' n : ℕ, HRS.Whole.s11p_kap n * r2CosBasis p.T n (t : ℝ) *
          (s21gTheta σ (r26t3_W R (r26t3_qwin R a) N X)).c (n, α))
        = ∑' n : ℕ, Real.sqrt N *
            (HRS.Whole.s11p_kap n * r2CosBasis p.T n (t : ℝ) *
                HRS.Whole.pair (HRS.Whole.empirical X)
                  (r26t3_qwin R a (σ.symm (n, α))) -
              HRS.Whole.s11p_kap n * r2CosBasis p.T n (t : ℝ) *
                HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
                  (r26t3_qwin R a (σ.symm (n, α)))) := by
            apply tsum_congr
            intro n
            rw [hTheta n, hTerms n]
        _ = Real.sqrt N *
            (HRS.Whole.pair (HRS.Whole.empirical X) (U α (t : ℝ)) -
              HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
                (U α (t : ℝ))) := by
            simpa only [HRS.Whole.pair, U, D] using hSeries.tsum_eq
        _ = OscDual.coord (OscPath.at' (initialWindow R N a X) t) α := by
            rw [hinitCoord t α]
  refine ContinuousMap.ext fun t => ?_
  exact HRS.MS.CovMeas.s101_ellVec_ext fun α => hcoord t α

/-- The synthesis of the transported initial feature vector is the actual
initial particle window, for every configuration and including γ = 0. -/
theorem fp81s21_initRecon_path (p : Parameters) :
    ∃ δrec : ℝ, 0 < δrec ∧ δrec ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δrec → ∀ (R : Trajectory p δ),
        (0 < p.γ ∨ p.γ = 0) → ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
          ∀ X : EucConfig p.d N,
            s21gPhi (r26t3_feature_enum p.d) p.hT
              ((wholeSpaceIndex p.d : ℕ) : ℝ)
              (r26t3_W R (r26t3_qwin R a) N X) =
            initialWindow R N a X := by
  obtain ⟨δc, hδc, hδchalf, hcos⟩ := fp81s21_cosRecon_radius p
  obtain ⟨δg, hδg, hδghalf, hgenuine⟩ := fp81s21_initialWindow_genuine p
  obtain ⟨δu, hδu, hδuhalf, hOrbit⟩ := fp81s21_uniform_orbit_amplitudes p
  let δrec := min δc (min δg δu)
  have hδrec : 0 < δrec := by
    dsimp [δrec]
    exact lt_min hδc (lt_min hδg hδu)
  have hδrechalf : δrec ≤ 1 / 2 := by
    dsimp [δrec]
    exact (min_le_left _ _).trans hδchalf
  refine ⟨δrec, hδrec, hδrechalf, ?_⟩
  intro δ hδ hδrec' R hγ N hN a ha X
  have hδc' : δ ≤ δc := hδrec'.trans (by
    dsimp [δrec]
    exact min_le_left _ _)
  have hδg' : δ ≤ δg := hδrec'.trans (by
    dsimp [δrec]
    exact (min_le_right _ _).trans (min_le_left _ _))
  have hδu' : δ ≤ δu := hδrec'.trans (by
    dsimp [δrec]
    exact (min_le_right _ _).trans (min_le_right _ _))
  have hδhalf : δ ≤ 1 / 2 := hδrec'.trans hδrechalf
  obtain ⟨Cobs, hCobs, hcosR⟩ := hcos δ hδ hδc' R
  obtain ⟨hq, _hbound, _hobs, hshift⟩ := hcosR a ha
  have hinitCoord : ∀ t : Set.Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d,
      OscDual.coord (OscPath.at' (initialWindow R N a X) t) α =
        Real.sqrt N *
          (HRS.Whole.pair (HRS.Whole.empirical X)
              (r26t3_U R 0 (a + (t : ℝ))
                (oscTestFun (wholeSpaceIndex p.d) α)) -
            HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
              (r26t3_U R 0 (a + (t : ℝ))
                (oscTestFun (wholeSpaceIndex p.d) α))) := by
    rcases hγ with hpos | hzero
    · obtain ⟨_, _, hcoords, _, _⟩ :=
        hgenuine δ hδ hδg' R hpos N hN a ha X
      exact hcoords
    · obtain ⟨Co, co, hco, hcsum, horbits⟩ :=
        hOrbit δ hδ hδu' R
      have hH : 0 < a + p.T := by linarith [p.hT, ha]
      have hD : S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (a + p.T) (2 * p.d + 8)
          (fp81s21_uniform_orbit_coefficient p Co) := horbits (a + p.T) hH
      exact fp81s21_initRecon_zero_initialCoord hδ hδhalf R hzero N hN a ha hD X
  exact fp81s21_initRecon_path_eq_of_data hδ hδhalf R hγ N hN a ha X
    hq hshift hinitCoord

/-- Cosine coordinates of the genuine initial window recover the transported
feature vector coordinates. -/
theorem fp81s21_initRecon_obs_coordinate (p : Parameters) :
    ∃ δrec : ℝ, 0 < δrec ∧ δrec ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δrec → ∀ (R : Trajectory p δ),
        (0 < p.γ ∨ p.γ = 0) → ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
          ∀ X : EucConfig p.d N, ∀ j : ℕ,
            fp81s21_cosRecon_obs26 p (initialWindow R N a X) j =
              SeqL2.coord (r26t3_W R (r26t3_qwin R a) N X) j := by
  obtain ⟨δrec, hδrec, hδrechalf, hpath⟩ := fp81s21_initRecon_path p
  refine ⟨δrec, hδrec, hδrechalf, ?_⟩
  intro δ hδ hδle R hγ N hN a ha X j
  rw [← hpath δ hδ hδle R hγ N hN a ha X]
  exact fp81s21_cosRecon_obs26_synthesis p
    (r26t3_W R (r26t3_qwin R a) N X) j

/-- The two pointwise equal initial-window maps induce the same law under the
actual prepared particle measure. -/
theorem fp81s21_initRecon_law (p : Parameters) :
    ∃ δrec : ℝ, 0 < δrec ∧ δrec ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δrec → ∀ (R : Trajectory p δ),
        (0 < p.γ ∨ p.γ = 0) → ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
          Measure.map (initialWindow R N a) (r26t3_Q R N) =
            Measure.map
              (fun X => s21gPhi (r26t3_feature_enum p.d) p.hT
                ((wholeSpaceIndex p.d : ℕ) : ℝ)
                (r26t3_W R (r26t3_qwin R a) N X))
              (r26t3_Q R N) := by
  obtain ⟨δrec, hδrec, hδrechalf, hpath⟩ := fp81s21_initRecon_path p
  refine ⟨δrec, hδrec, hδrechalf, ?_⟩
  intro δ hδ hδle R hγ N hN a ha
  apply Measure.map_congr
  exact Filter.Eventually.of_forall fun X =>
    (hpath δ hδ hδle R hγ N hN a ha X).symm

/-- For a particle realization with the actual initial law, the synthesized
initial window has the pushforward law of `initialWindow`. -/
theorem fp81s21_initRecon_particle_law (p : Parameters) :
    ∃ δrec : ℝ, 0 < δrec ∧ δrec ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δrec → ∀ (R : Trajectory p δ),
        (0 < p.γ ∨ p.γ = 0) → ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
          ∀ A : Particle R N,
            law A.P (fun ζ => s21gPhi (r26t3_feature_enum p.d) p.hT
              ((wholeSpaceIndex p.d : ℕ) : ℝ)
              (r26t3_W R (r26t3_qwin R a) N (A.X₀ ζ))) =
            Measure.map (initialWindow R N a) (r26t3_Q R N) := by
  obtain ⟨δpath, hδpath, hδpathhalf, hpath⟩ := fp81s21_initRecon_path p
  obtain ⟨δcos, hδcos, hδcoshalf, hcos⟩ := fp81s21_cosRecon_radius p
  let δrec := min δpath δcos
  have hδrec : 0 < δrec := by
    dsimp [δrec]
    exact lt_min hδpath hδcos
  have hδrechalf : δrec ≤ 1 / 2 := by
    dsimp [δrec]
    exact (min_le_left _ _).trans hδpathhalf
  refine ⟨δrec, hδrec, hδrechalf, ?_⟩
  intro δ hδ hδrec' R hγ N hN a ha A
  have hδpath' : δ ≤ δpath := hδrec'.trans (by
    dsimp [δrec]
    exact min_le_left _ _)
  have hδcos' : δ ≤ δcos := hδrec'.trans (by
    dsimp [δrec]
    exact min_le_right _ _)
  have hδhalf : δ ≤ 1 / 2 := hδrec'.trans hδrechalf
  obtain ⟨Cobs, hCobs, hcosR⟩ := hcos δ hδ hδcos' R
  obtain ⟨hq, _hbound, _hobs, _hshift⟩ := hcosR a ha
  have hpathX : ∀ ζ : A.Ω,
      s21gPhi (r26t3_feature_enum p.d) p.hT
        ((wholeSpaceIndex p.d : ℕ) : ℝ)
        (r26t3_W R (r26t3_qwin R a) N (A.X₀ ζ)) =
      initialWindow R N a (A.X₀ ζ) := fun ζ =>
        hpath δ hδ hδpath' R hγ N hN a ha (A.X₀ ζ)
  have hN1 : 1 ≤ N := by omega
  have hQ : IsProbabilityMeasure (r26t3_Q R N) := by
    rcases hγ with hpos | hzero
    · exact (r26t3_static_pressure hδ hδhalf R hpos).1 N hN
    · have hdens := (r26t3_reference_data p δ hδ hδhalf R).2.2.1 0 le_rfl
      letI : IsProbabilityMeasure (r26t3_mu R 0) :=
        s11iid_prob hdens.1.nonneg hdens.1.integral_one
      rw [fp81s21_initial_iid_Q hδ hδhalf R hzero N]
      infer_instance
  letI : IsProbabilityMeasure (r26t3_Q R N) := hQ
  haveI : IsProbabilityMeasure (r26t3_marg R N) := S99.s99_nu_prob hN1
  have hWmeas : Measurable
      (r26t3_W R (r26t3_qwin R a) N : EucConfig p.d N → SeqL2) := by
    unfold r26t3_W
    exact S45.s45_feature_measurable hN1 hq
  have hSynthMeas : Measurable (fun X : EucConfig p.d N =>
      s21gPhi (r26t3_feature_enum p.d) p.hT
        ((wholeSpaceIndex p.d : ℕ) : ℝ)
        (r26t3_W R (r26t3_qwin R a) N X)) :=
    (s21gPhi (r26t3_feature_enum p.d) p.hT
      ((wholeSpaceIndex p.d : ℕ) : ℝ)).continuous.measurable.comp hWmeas
  have hInitMeas : Measurable (initialWindow R N a) := by
    change ∀ s, MeasurableSet s →
      MeasurableSet ((initialWindow R N a) ⁻¹' s)
    intro s hs
    have hpre : (initialWindow R N a) ⁻¹' s =
        (fun X : EucConfig p.d N =>
          s21gPhi (r26t3_feature_enum p.d) p.hT
            ((wholeSpaceIndex p.d : ℕ) : ℝ)
            (r26t3_W R (r26t3_qwin R a) N X)) ⁻¹' s := by
      ext X
      change (initialWindow R N a X ∈ s) ↔
        (s21gPhi (r26t3_feature_enum p.d) p.hT
          ((wholeSpaceIndex p.d : ℕ) : ℝ)
          (r26t3_W R (r26t3_qwin R a) N X) ∈ s)
      rw [← hpath δ hδ hδpath' R hγ N hN a ha X]
    rw [hpre]
    exact hSynthMeas hs
  have hX₀ : AEMeasurable A.X₀ A.P :=
    ((A.strong 0).adapted 0).aemeasurable.congr (A.strong 0).init
  have hmap : A.P.map (fun ζ => initialWindow R N a (A.X₀ ζ)) =
      (A.P.map A.X₀).map (initialWindow R N a) := by
    simpa only [Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable hInitMeas.aemeasurable hX₀).symm
  calc
    law A.P (fun ζ => s21gPhi (r26t3_feature_enum p.d) p.hT
        ((wholeSpaceIndex p.d : ℕ) : ℝ)
        (r26t3_W R (r26t3_qwin R a) N (A.X₀ ζ))) =
      law A.P (fun ζ => initialWindow R N a (A.X₀ ζ)) := by
        rw [HRS.law, HRS.law]
        exact Measure.map_congr (Filter.Eventually.of_forall hpathX)
    _ = (law A.P A.X₀).map (initialWindow R N a) := by
        simpa only [HRS.law] using hmap
    _ = Measure.map (initialWindow R N a) (r26t3_Q R N) := by
        rw [A.initial]

#print axioms fp81s21_initRecon_meanEmpirical_marg
#print axioms fp81s21_initRecon_W_coordinate
#print axioms fp81s21_initRecon_path
#print axioms fp81s21_initRecon_obs_coordinate
#print axioms fp81s21_initRecon_law
#print axioms fp81s21_initRecon_particle_law

end HRS.Fp81.S21

end
