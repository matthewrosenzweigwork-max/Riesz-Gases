import HRS.Energy.Commutator.SmearAuxC

/-!
# Auxiliary lemmas for `Smear.lean` (packet CM-S2), part D: periodisation and Newton for the Yukawa kernel

* `periodization_vec`: `𝒢_l^{full}(mk v) = ∑_m Γ_l(|v - m|)` for every `v ∈ ℝ^d` with `mk v ≠ 0`,
  together with summability (positivity of `𝒢_l^{full}`);
* `newton_yukawa`: Euclidean Newton's theorem `∫ Γ_l(|y - z|) dν(y) = Γ_l(max(|z|, η))`
  for a finite measure `ν` with the weak form of `(l - Δ) u_{l,η} = σ_{l,η}`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators Pointwise
noncomputable section
namespace HRS.Commutator.SmearAux
variable {d : ℕ}

theorem centeredRep_mem_Box (z : Torus d) : (fun i => KernelGrad.centeredRep z i) ∈ KernelAux.Box d := by
  intro i
  obtain ⟨h0, h1⟩ := KernelGrad.rep_mem z i
  simp only [mem_Ioc]
  rw [KernelGrad.centeredRep_apply]
  split_ifs with h
  · constructor <;> linarith
  · push Not at h
    constructor <;> linarith

theorem sliceGfull_pos {l : ℝ} (hl : 0 < l) {y : Fin d → ℝ} (hy : y ∈ KernelAux.Box d) (hy0 : y ≠ 0) :
    0 < sliceGfull d l (KernelAux.boxPt y) := by
  have hx : KernelAux.boxPt y ≠ 0 := SliceAux.boxPt_ne_zero hy hy0
  have hI := SliceAux.integrableOn_slice_psi hl.le hx
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
    exact this
  have hE' : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) = 1 / l := by
    rw [integral_exp_mul_Ioi (by linarith : -l < 0)]
    simp
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-l * t) * (1 + psiFn (KernelAux.boxPt y) (4 * Real.pi ^ 2 * t)))
      (Ioi 0) := by
    have := hE.add hI
    refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.add_apply]; ring
  have hsplit : sliceGfull d l (KernelAux.boxPt y) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * (1 + psiFn (KernelAux.boxPt y) (4 * Real.pi ^ 2 * t)) := by
    unfold sliceGfull sliceG
    have : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * (1 + psiFn (KernelAux.boxPt y) (4 * Real.pi ^ 2 * t)) =
        1 / l + ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn (KernelAux.boxPt y) (4 * Real.pi ^ 2 * t) := by
      rw [← hE', ← integral_add hE hI]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      ring
    rw [this]; ring
  rw [hsplit]
  refine SliceAux.pos_integral_of_pos (fun t ht => ?_) hg
  rw [SliceAux.heat_pointwise y l ht]
  refine Summable.tsum_pos (SliceAux.summable_heatTerm y l ht) (fun m => SliceAux.heatTerm_nonneg y m l ht) 0 ?_
  unfold SliceAux.heatTerm
  positivity


theorem toEuc_sub (m m' : Lattice d) : Lattice.toEuc (m - m') = Lattice.toEuc m - Lattice.toEuc m' := by
  ext i; simp [Lattice.toEuc]

theorem periodization_vec {l : ℝ} (hl : 0 < l) {v : Euc d} (hv : Torus.mk v ≠ 0) :
    Summable (fun m : Lattice d => yukawa d l ‖v - Lattice.toEuc m‖) ∧
    sliceGfull d l (Torus.mk v) = ∑' m : Lattice d, yukawa d l ‖v - Lattice.toEuc m‖ := by
  set w : Euc d := KernelGrad.centeredRep (Torus.mk v) with hw
  have hmk : Torus.mk w = Torus.mk v := KernelGrad.mk_centeredRep _
  have hbox : (fun i => w i) ∈ KernelAux.Box d := centeredRep_mem_Box _
  have hy0 : (fun i => w i) ≠ 0 := by
    intro h
    apply hv
    rw [← hmk]
    have : w = 0 := by ext i; exact congrFun h i
    rw [this]; funext i; simp [Torus.mk]
  have hbp : KernelAux.boxPt (fun i => w i) = Torus.mk v := by
    rw [← hmk]; rfl
  have hper := sliceGfull_periodization hl hbox hy0
  rw [hbp] at hper
  have hpos : 0 < sliceGfull d l (Torus.mk v) := by
    have := sliceGfull_pos hl hbox hy0
    rwa [hbp] at this
  have e : ∀ m : Lattice d, (WithLp.toLp 2 (fun i => w i - (m i : ℝ)) : Euc d) = w - Lattice.toEuc m := by
    intro m; ext i; simp [Lattice.toEuc]
  simp_rw [e] at hper
  have hsum : Summable (fun m : Lattice d => yukawa d l ‖w - Lattice.toEuc m‖) := by
    by_contra h
    rw [tsum_eq_zero_of_not_summable h] at hper
    linarith
  obtain ⟨m₀, hm₀⟩ := SliceAux.exists_lattice_of_mk_eq hmk.symm
  have hre : ∀ m : Lattice d, v - Lattice.toEuc m = w - Lattice.toEuc (m - m₀) := by
    intro m; rw [toEuc_sub, hm₀]; abel
  have hfun : (fun m : Lattice d => yukawa d l ‖v - Lattice.toEuc m‖) =
      (fun m : Lattice d => yukawa d l ‖w - Lattice.toEuc m‖) ∘ (Equiv.subRight m₀) := by
    funext m; simp only [Function.comp, hre, Equiv.subRight_apply]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (Equiv.summable_iff _).2 hsum
  · rw [hper, hfun]
    exact ((Equiv.subRight m₀).tsum_eq (fun m => yukawa d l ‖w - Lattice.toEuc m‖)).symm


theorem lintegral_yukawa' {l r : ℝ}
    (h : IntegrableOn (fun s : ℝ => Real.exp (-l * s) * SliceAux.gprof d s r) (Ioi 0)) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-l * s) * SliceAux.gprof d s r) =
      ENNReal.ofReal (yukawa d l r) := by
  have e : yukawa d l r = ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * SliceAux.gprof d t r := rfl
  rw [e, ofReal_integral_eq_lintegral_ofReal h]
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun s hs => ?_)
  exact mul_nonneg (Real.exp_pos _).le (SliceAux.gprof_pos d hs r).le

theorem lintegral_yukawa (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-l * s) * SliceAux.gprof d s r) =
      ENNReal.ofReal (yukawa d l r) :=
  lintegral_yukawa' (SliceAux.integrableOn_yk hl hd hr)

theorem newton_yukawa' (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (z : Euc d)
    (ν : Measure (Euc d)) [IsFiniteMeasure ν]
    (hW : ∀ s : ℝ, 0 < s → ∫ y, gφ d s z y ∂ν =
      l * yukawa d l η * (∫ y in closedBall (0 : Euc d) η, gφ d s z y) -
        η ^ (d - 1) * deriv (yukawa d l) η * Phi (gφ d s z) η)
    (hint : ∀ᵐ y ∂ν, IntegrableOn (fun s : ℝ => Real.exp (-l * s) * SliceAux.gprof d s ‖y - z‖) (Ioi 0)) :
    ∫⁻ y, ENNReal.ofReal (yukawa d l ‖y - z‖) ∂ν = ENNReal.ofReal (yukawa d l (max ‖z‖ η)) := by
  have hyk := yukawa_ode hd hl
  have hΓ : ∀ r, 0 < r → HasDerivAt (yukawa d l) (deriv (yukawa d l) r) r :=
    fun r hr => hasDerivAt_yukawa hd hl hr
  obtain ⟨C, hC⟩ := bound_deriv_yukawa hd hl hη
  set M := yukawa d l η with hM
  have hu : Continuous fun y : Euc d => yukawa d l (max ‖y‖ η) := continuous_Γmax hη hΓ
  have hbd : ∀ y : Euc d, |yukawa d l (max ‖y‖ η)| ≤ M := by
    intro y
    have hpos := hyk.1 _ (lt_of_lt_of_le hη (le_max_right ‖y‖ η))
    rw [abs_of_pos hpos]
    rcases eq_or_lt_of_le (le_max_right ‖y‖ η) with h | h
    · rw [← h]
    · exact (hyk.2.1 η _ hη h).le
  have hmain := newton_lintegral hd hl z hu hbd ν (fun s hs => by
    rw [core_weak hd hη hΓ (measurable_deriv _) (fun r hr => hasDerivAt_flux hd hl hr) hC (TF_gφ hd hs z)]
    exact (hW s hs).symm)
  rw [← hmain]
  refine lintegral_congr_ae ?_
  filter_upwards [hint] with y hy
  rw [← lintegral_yukawa' hy]
  rfl

theorem newton_yukawa (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (z : Euc d)
    (ν : Measure (Euc d)) [IsFiniteMeasure ν]
    (hW : ∀ s : ℝ, 0 < s → ∫ y, gφ d s z y ∂ν =
      l * yukawa d l η * (∫ y in closedBall (0 : Euc d) η, gφ d s z y) -
        η ^ (d - 1) * deriv (yukawa d l) η * Phi (gφ d s z) η)
    (hnull : ∀ᵐ y ∂ν, y ≠ z) :
    ∫⁻ y, ENNReal.ofReal (yukawa d l ‖y - z‖) ∂ν = ENNReal.ofReal (yukawa d l (max ‖z‖ η)) :=
  newton_yukawa' hd hl hη z ν hW (hnull.mono fun y hy =>
    SliceAux.integrableOn_yk hl hd (norm_pos_iff.2 (sub_ne_zero.2 hy)))

theorem toSphere_singleton (hd : 2 ≤ d) (ω : sphere (0 : Euc d) 1) :
    (volume : Measure (Euc d)).toSphere {ω} = 0 := by
  rw [Measure.toSphere_apply' _ (measurableSet_singleton ω)]
  have hsub : Ioo (0:ℝ) 1 • (Subtype.val '' ({ω} : Set (sphere (0 : Euc d) 1))) ⊆
      (Submodule.span ℝ {(ω : Euc d)} : Submodule ℝ (Euc d)) := by
    rintro x ⟨t, ht, y, ⟨ω', hω', rfl⟩, rfl⟩
    have : ω' = ω := hω'
    subst this
    exact Submodule.smul_mem _ t (Submodule.subset_span rfl)
  have hne : (Submodule.span ℝ {(ω : Euc d)} : Submodule ℝ (Euc d)) ≠ ⊤ := by
    intro h
    have hω0 : (ω : Euc d) ≠ 0 := by
      intro h0
      have : ‖(ω : Euc d)‖ = 1 := by simp
      rw [h0] at this; simp at this
    have h1 := finrank_span_singleton (K := ℝ) hω0
    rw [h] at h1
    simp at h1
    omega
  have := Measure.addHaar_submodule (volume : Measure (Euc d)) _ hne
  rw [measure_mono_null hsub this]
  simp



theorem measurable_psiFn_uncurry' :
    Measurable fun p : Torus d × ℝ => psiFn p.1 p.2 := by
  unfold psiFn
  refine Measurable.tsum fun k => ?_
  by_cases hk : k = 0
  · simp [hk]
  · simp only [hk, ite_false]
    have h1 : Continuous fun p : Torus d × ℝ => Real.exp (-p.2 * Lattice.enorm k ^ 2) :=
      Real.continuous_exp.comp (continuous_snd.neg.mul continuous_const)
    have h2 : Continuous fun p : Torus d × ℝ => Torus.cosMode k p.1 :=
      (Torus.continuous_cosMode k).comp continuous_fst
    exact (h1.mul h2).measurable

theorem measurable_sliceG (l : ℝ) : Measurable (sliceG d l) := by
  unfold sliceG
  have hm : Measurable fun p : Torus d × ℝ => Real.exp (-l * p.2) * psiFn p.1 (4 * Real.pi ^ 2 * p.2) := by
    have h2 : Measurable fun p : Torus d × ℝ => 4 * Real.pi ^ 2 * p.2 := measurable_const.mul measurable_snd
    have := (measurable_psiFn_uncurry' (d := d)).comp (measurable_fst.prodMk h2)
    exact (by fun_prop : Measurable fun p : Torus d × ℝ => Real.exp (-l * p.2)).mul this
  exact (hm.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ).restrict (Ioi 0))).measurable

theorem measurable_sliceGfull (l : ℝ) : Measurable (sliceGfull d l) := by
  unfold sliceGfull
  exact (measurable_sliceG l).add measurable_const

theorem measurable_yukawa (l : ℝ) : Measurable (yukawa d l) := by
  have hm : Measurable fun p : ℝ × ℝ => Real.exp (-l * p.2) * SliceAux.gprof d p.2 p.1 := by
    unfold SliceAux.gprof; fun_prop
  exact (hm.stronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ).restrict (Ioi 0))).measurable



theorem mk_zero' : Torus.mk (0 : Euc d) = 0 := by
  funext i; simp [Torus.mk]

theorem mk_sub_eq (a b : Euc d) : Torus.mk (a - b) = Torus.mk a - Torus.mk b := by
  have h : Torus.mk a = Torus.mk (a - b) + Torus.mk b := by rw [← Torus.mk_add]; congr 1; abel
  rw [h]; abel

theorem one_half_le_norm_sub (m : Lattice d) (hm : m ≠ 0) {x : Euc d} (hx : ∀ i, |x i| ≤ 1 / 2) :
    1 / 2 ≤ ‖x - Lattice.toEuc m‖ := by
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra h
    push Not at h
    exact hm (funext h)
  have h1 : (1:ℝ) ≤ |(m i : ℝ)| := by
    have : (1:ℤ) ≤ |m i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 := hx i
  have h3 : |(x - Lattice.toEuc m) i| ≥ 1 / 2 := by
    simp only [PiLp.sub_apply, Lattice.toEuc]
    have := abs_sub_abs_le_abs_sub (m i : ℝ) (x i)
    rw [abs_sub_comm] at this
    linarith
  exact h3.trans (abs_apply_le_norm _ i)

theorem toEuc_zero : Lattice.toEuc (0 : Lattice d) = 0 := by
  ext i; simp [Lattice.toEuc]

theorem yukawa_max_eq (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    yukawa d l (max r η) = yukawa d l r - max (yukawa d l r - yukawa d l η) 0 := by
  have hyk := yukawa_ode hd hl
  rcases le_total r η with h | h
  · rw [max_eq_right h]
    rcases eq_or_lt_of_le h with h' | h'
    · rw [h']; simp
    · have := hyk.2.1 r η hr h'
      rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_left h]
    rcases eq_or_lt_of_le h with h' | h'
    · rw [← h']; simp
    · have := hyk.2.1 η r hη h'
      rw [max_eq_right (by linarith)]; ring



theorem yukawa_nonneg (d : ℕ) (l r : ℝ) : 0 ≤ yukawa d l r := by
  unfold yukawa
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have : (0:ℝ) < t := ht
  have := gφ_pos d this (0 : Euc d) (0 : Euc d)
  positivity

theorem heatTerm_zero (m : Lattice d) (l t : ℝ) :
    SliceAux.heatTerm d (0 : Fin d → ℝ) m l t = Real.exp (-l * t) * SliceAux.gprof d t ‖Lattice.toEuc m‖ := by
  unfold SliceAux.heatTerm SliceAux.gprof
  have : (WithLp.toLp 2 (fun i => (0 : Fin d → ℝ) i - (m i : ℝ)) : Euc d) = -Lattice.toEuc m := by
    ext i; simp [Lattice.toEuc]
  rw [this, norm_neg]

theorem periodization_zero {l : ℝ} (hl : 0 < l)
    (hint : ∀ m : Lattice d, IntegrableOn (fun t : ℝ => Real.exp (-l * t) * SliceAux.gprof d t ‖Lattice.toEuc m‖) (Ioi 0))
    (hsum : Summable (fun m : Lattice d => yukawa d l ‖Lattice.toEuc m‖)) :
    sliceGfull d l 0 = ∑' m : Lattice d, yukawa d l ‖Lattice.toEuc m‖ := by
  have hb0 : (KernelAux.boxPt (0 : Fin d → ℝ)) = 0 := by funext i; simp [KernelAux.boxPt]
  set f : ℝ → ℝ := fun t => Real.exp (-l * t) * (1 + psiFn (0 : Torus d) (4 * Real.pi ^ 2 * t)) with hf
  have hfpt : ∀ t ∈ Ioi (0 : ℝ), f t = ∑' m : Lattice d, SliceAux.heatTerm d (0 : Fin d → ℝ) m l t :=
    fun t ht => by
      have := SliceAux.heat_pointwise (0 : Fin d → ℝ) l ht
      rw [hb0] at this
      exact this
  have hmeas : ∀ m : Lattice d, AEStronglyMeasurable (SliceAux.heatTerm d (0 : Fin d → ℝ) m l)
      (volume.restrict (Ioi (0 : ℝ))) :=
    fun m => (SliceAux.continuousOn_heatTerm 0 m l).aestronglyMeasurable measurableSet_Ioi
  have hi : ∀ m : Lattice d, IntegrableOn (SliceAux.heatTerm d (0 : Fin d → ℝ) m l) (Ioi 0) := by
    intro m
    refine (hint m).congr_fun (fun t _ => ?_) measurableSet_Ioi
    exact (heatTerm_zero m l t).symm
  have hval : ∀ m : Lattice d, ∫ t in Ioi (0 : ℝ), SliceAux.heatTerm d (0 : Fin d → ℝ) m l t =
      yukawa d l ‖Lattice.toEuc m‖ := by
    intro m
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    exact heatTerm_zero m l t
  have hlint : ∀ m : Lattice d, ∫⁻ t in Ioi (0 : ℝ), ‖SliceAux.heatTerm d (0 : Fin d → ℝ) m l t‖ₑ =
      ENNReal.ofReal (yukawa d l ‖Lattice.toEuc m‖) := by
    intro m
    rw [← hval m, ofReal_integral_eq_lintegral_ofReal (hi m)]
    · refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
      show ‖SliceAux.heatTerm d (0 : Fin d → ℝ) m l t‖ₑ = ENNReal.ofReal (SliceAux.heatTerm d (0 : Fin d → ℝ) m l t)
      rw [Real.enorm_of_nonneg (SliceAux.heatTerm_nonneg 0 m l ht)]
    · exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => SliceAux.heatTerm_nonneg 0 m l ht)
  have hfin : ∑' m : Lattice d, ∫⁻ t in Ioi (0 : ℝ), ‖SliceAux.heatTerm d (0 : Fin d → ℝ) m l t‖ₑ ≠ ∞ := by
    simp_rw [hlint]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => yukawa_nonneg d l _) hsum]
    exact ENNReal.ofReal_ne_top
  have hint_f : ∫ t in Ioi (0 : ℝ), f t = ∑' m : Lattice d, yukawa d l ‖Lattice.toEuc m‖ := by
    rw [setIntegral_congr_fun measurableSet_Ioi hfpt, integral_tsum hmeas hfin]
    exact tsum_congr hval
  have hfc : ContinuousOn f (Ioi 0) := by
    refine (by fun_prop : Continuous fun t : ℝ => Real.exp (-l * t)).continuousOn.mul ?_
    refine continuousOn_const.add ?_
    refine (psi_continuousOn _).comp (continuousOn_const.mul continuousOn_id) fun t ht => ?_
    have : (0:ℝ) < t := ht
    show 0 < 4 * Real.pi ^ 2 * t
    positivity
  have hfnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ f t := by
    intro t ht
    rw [hfpt t ht]
    exact tsum_nonneg fun m => SliceAux.heatTerm_nonneg 0 m l ht
  have hfI : IntegrableOn f (Ioi 0) := by
    refine ⟨hfc.aestronglyMeasurable measurableSet_Ioi, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hfnn))]
    have e1 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (f t) =
        ∫⁻ t in Ioi (0 : ℝ), ∑' m : Lattice d, ENNReal.ofReal (SliceAux.heatTerm d (0 : Fin d → ℝ) m l t) := by
      refine lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_))
      show ENNReal.ofReal (f t) = _
      rw [hfpt t ht, ENNReal.ofReal_tsum_of_nonneg (fun m => SliceAux.heatTerm_nonneg 0 m l ht)
        (SliceAux.summable_heatTerm 0 l ht)]
    rw [e1, lintegral_tsum (fun m => (hmeas m).aemeasurable.ennreal_ofReal)]
    have e2 : ∀ m : Lattice d, ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (SliceAux.heatTerm d (0 : Fin d → ℝ) m l t) =
        ENNReal.ofReal (yukawa d l ‖Lattice.toEuc m‖) := by
      intro m
      rw [← hval m, ofReal_integral_eq_lintegral_ofReal (hi m)]
      exact (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => SliceAux.heatTerm_nonneg 0 m l ht)
    simp_rw [e2]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => yukawa_nonneg d l _) hsum]
    exact ENNReal.ofReal_lt_top
  have hE : IntegrableOn (fun t : ℝ => Real.exp (-l * t)) (Ioi 0) := by
    have := integrableOn_exp_mul_Ioi (a := -l) (by linarith) (0 : ℝ)
    exact this
  have hE' : ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) = 1 / l := by
    rw [integral_exp_mul_Ioi (by linarith : -l < 0)]
    simp
  have hI : IntegrableOn (fun t : ℝ => Real.exp (-l * t) * psiFn (0 : Torus d) (4 * Real.pi ^ 2 * t)) (Ioi 0) := by
    refine (hfI.sub hE).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [hf, Pi.sub_apply]; ring
  rw [← hint_f]
  unfold sliceGfull sliceG
  have : ∫ t in Ioi (0 : ℝ), f t = 1 / l + ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * psiFn (0 : Torus d) (4 * Real.pi ^ 2 * t) := by
    rw [← hE', ← integral_add hE hI]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [hf]; ring
  rw [this]
  ring



theorem integrableOn_yk_zero_d1 {l : ℝ} (hl : 0 < l) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) * SliceAux.gprof 1 t 0) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := -(1:ℝ) / 2) (b := l) (by norm_num)
    one_pos hl
  have h2 : IntegrableOn (fun x : ℝ => (4 * Real.pi) ^ (-(1:ℝ) / 2) * (x ^ (-(1:ℝ) / 2) * Real.exp (-l * x ^ (1:ℝ)))) (Ioi 0) :=
    h.const_mul ((4 * Real.pi) ^ (-(1:ℝ) / 2))
  refine h2.congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0:ℝ) < t := ht
  unfold SliceAux.gprof
  simp only [Real.rpow_one, Nat.cast_one, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, Real.exp_zero, mul_one]
  rw [Real.mul_rpow (by positivity) ht0.le]
  ring_nf

theorem integrableOn_yk_d1 {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 ≤ r) :
    IntegrableOn (fun t : ℝ => Real.exp (-l * t) * SliceAux.gprof 1 t r) (Ioi 0) := by
  rcases eq_or_lt_of_le hr with h | h
  · rw [← h]; exact integrableOn_yk_zero_d1 hl
  · exact SliceAux.integrableOn_yk hl le_rfl h


theorem yukawa_d1_le {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 ≤ r) :
    yukawa 1 l r ≤ yukawa 1 (l / 2) 0 * Real.exp (-Real.sqrt (l / 2) * r) := by
  have hc : 0 ≤ Real.sqrt (l / 2) := Real.sqrt_nonneg _
  have hc2 : Real.sqrt (l / 2) ^ 2 = l / 2 := Real.sq_sqrt (by positivity)
  have h1 := integrableOn_yk_d1 hl hr
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-(l / 2) * t) * SliceAux.gprof 1 t 0) (Ioi 0) :=
    integrableOn_yk_zero_d1 (by positivity)
  have h3 : yukawa 1 l r = ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * SliceAux.gprof 1 t r := rfl
  have h4 : yukawa 1 (l / 2) 0 = ∫ t in Ioi (0 : ℝ), Real.exp (-(l / 2) * t) * SliceAux.gprof 1 t 0 := rfl
  have h5 : IntegrableOn (fun t : ℝ => Real.exp (-Real.sqrt (l / 2) * r) *
      (Real.exp (-(l / 2) * t) * SliceAux.gprof 1 t 0)) (Ioi 0) := h2.const_mul _
  have hmono := setIntegral_mono_on h1 h5 measurableSet_Ioi (fun t ht => by
    have ht0 : (0:ℝ) < t := ht
    unfold SliceAux.gprof
    simp only [Nat.cast_one, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
      Real.exp_zero, mul_one]
    have hq : Real.sqrt (l / 2) * r ≤ l * t / 2 + r ^ 2 / (4 * t) := by
      have : 0 ≤ (r - 2 * t * Real.sqrt (l / 2)) ^ 2 := sq_nonneg _
      have h6 : 4 * t * (Real.sqrt (l / 2) * r) ≤ 4 * t * (l * t / 2 + r ^ 2 / (4 * t)) := by
        have e1 : 4 * t * (r ^ 2 / (4 * t)) = r ^ 2 := by field_simp
        have e2 : (2 * t * Real.sqrt (l / 2)) ^ 2 = 2 * l * t ^ 2 := by
          rw [mul_pow, mul_pow, hc2]; ring
        have e3 : 4 * t * (l * t / 2 + r ^ 2 / (4 * t)) = 2 * l * t ^ 2 + r ^ 2 := by
          rw [mul_add, e1]; ring
        rw [e3]
        nlinarith [e2, this]
      exact le_of_mul_le_mul_left h6 (by positivity)
    have hE : Real.exp (-l * t) * Real.exp (-r ^ 2 / (4 * t)) ≤
        Real.exp (-Real.sqrt (l / 2) * r) * Real.exp (-(l / 2) * t) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have : -r ^ 2 / (4 * t) = -(r ^ 2 / (4 * t)) := by ring
      rw [this]
      nlinarith [hq]
    have hp : 0 ≤ (4 * Real.pi * t) ^ (-(1:ℝ) / 2) := by positivity
    calc Real.exp (-l * t) * ((4 * Real.pi * t) ^ (-(1:ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t)))
        = (4 * Real.pi * t) ^ (-(1:ℝ) / 2) * (Real.exp (-l * t) * Real.exp (-r ^ 2 / (4 * t))) := by ring
      _ ≤ (4 * Real.pi * t) ^ (-(1:ℝ) / 2) * (Real.exp (-Real.sqrt (l / 2) * r) * Real.exp (-(l / 2) * t)) :=
          mul_le_mul_of_nonneg_left hE hp
      _ = _ := by ring)
  rw [h3, h4]
  calc ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * SliceAux.gprof 1 t r
      ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-Real.sqrt (l / 2) * r) *
        (Real.exp (-(l / 2) * t) * SliceAux.gprof 1 t 0) := hmono
    _ = _ := by rw [integral_const_mul]; ring


theorem summable_yukawa_d1 {l : ℝ} (hl : 0 < l) :
    Summable (fun m : Lattice 1 => yukawa 1 l ‖Lattice.toEuc m‖) := by
  set c : ℝ := Real.sqrt (l / 2) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hg : Summable (fun n : ℤ => Real.exp (-c * |(n : ℝ)|)) := by
    rw [summable_int_iff_summable_nat_and_neg]
    have h1 : Summable (fun n : ℕ => (Real.exp (-c)) ^ n) :=
      summable_geometric_of_lt_one (Real.exp_pos _).le (by rw [Real.exp_lt_one_iff]; linarith)
    have h2 : (fun n : ℕ => Real.exp (-c * |((n : ℤ) : ℝ)|)) = fun n : ℕ => (Real.exp (-c)) ^ n := by
      funext n
      rw [← Real.exp_nat_mul]; congr 1
      simp [abs_of_nonneg]; ring
    have h3 : (fun n : ℕ => Real.exp (-c * |((-(n : ℤ) : ℤ) : ℝ)|)) = fun n : ℕ => (Real.exp (-c)) ^ n := by
      funext n
      rw [← Real.exp_nat_mul]; congr 1
      simp [abs_of_nonneg]; ring
    exact ⟨by rw [h2]; exact h1, by rw [h3]; exact h1⟩
  have hnorm : ∀ m : Lattice 1, ‖Lattice.toEuc m‖ = |((m 0 : ℤ) : ℝ)| := by
    intro m
    simp [EuclideanSpace.norm_eq, Lattice.toEuc, Fin.sum_univ_one, Real.sqrt_sq_eq_abs]
  have hg' : Summable (fun m : Lattice 1 => yukawa 1 (l / 2) 0 * Real.exp (-c * ‖Lattice.toEuc m‖)) := by
    have := (Equiv.funUnique (Fin 1) ℤ).summable_iff.2 (hg.mul_left (yukawa 1 (l / 2) 0))
    refine this.congr (fun m => ?_)
    simp only [Function.comp, hnorm]
    simp [Equiv.funUnique]
  refine Summable.of_nonneg_of_le (fun m => yukawa_nonneg 1 l _) (fun m => ?_) hg'
  exact yukawa_d1_le hl (norm_nonneg _)


theorem periodization_zero_d1 {l : ℝ} (hl : 0 < l) :
    sliceGfull 1 l 0 = ∑' m : Lattice 1, yukawa 1 l ‖Lattice.toEuc m‖ :=
  periodization_zero hl (fun m => integrableOn_yk_d1 hl (norm_nonneg _)) (summable_yukawa_d1 hl)


end HRS.Commutator.SmearAux
