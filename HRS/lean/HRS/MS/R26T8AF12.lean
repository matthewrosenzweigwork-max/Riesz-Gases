import HRS.MS.R26T8AD00
import HRS.MS.R26T8AF10
import HRS.MS.R26T8AF11

/-!
# S8.2 observed-time layer, packet T8A.F12: projected iterates, time shift, norm continuity and derivatives of the feature orbits
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

/-- one-sided derivative from uniform difference quotients -/
theorem r26t8a_f12_hasDerivWithinAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : ℝ → E) (G' : E) (t : ℝ)
    (hq : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ → 0 ≤ t + h →
      ‖h⁻¹ • (G (t + h) - G t) - G'‖ ≤ ε) :
    HasDerivWithinAt G G' (Set.Ici 0) t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδ'⟩ := hq c hc
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds t hδ)] with s hs hball
  by_cases hst : s = t
  · subst hst; simp
  · set h : ℝ := s - t with hh
    have hh0 : h ≠ 0 := sub_ne_zero.2 hst
    have hs' : s = t + h := by rw [hh]; ring
    have hab : |h| < δ := by
      have := Metric.mem_ball.1 hball
      rwa [Real.dist_eq] at this
    have h0 : 0 ≤ t + h := by rw [← hs']; exact hs
    have key := hδ' h hh0 hab h0
    have e : G s - G t - (s - t) • G' = h • (h⁻¹ • (G (t + h) - G t) - G') := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hh0, one_smul, hs']
      simp [hh]
    rw [e, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left key (abs_nonneg h)).trans (le_of_eq (by ring))

theorem r26t8a_f12_quot_eq {d : ℕ} (G1 G2 G3 : Euc d → ℝ) (h1 : ContDiff ℝ ∞ G1) (h2 : ContDiff ℝ ∞ G2)
    (h3 : ContDiff ℝ ∞ G3) (c : ℝ) (ℓ : ℕ) (x : Euc d) :
    iteratedFDeriv ℝ ℓ (fun y => c * (G1 y - G2 y) - G3 y) x =
      c • (iteratedFDeriv ℝ ℓ G1 x - iteratedFDeriv ℝ ℓ G2 x) - iteratedFDeriv ℝ ℓ G3 x := by
  have e : (fun y => c * (G1 y - G2 y) - G3 y) = (c • (G1 - G2)) - G3 := by
    funext y; simp
  have c1 : ContDiffAt ℝ ℓ (c • (G1 - G2)) x :=
    ((h1.sub h2).const_smul c).contDiffAt.of_le (by exact_mod_cast le_top)
  have c3 : ContDiffAt ℝ ℓ G3 x := h3.contDiffAt.of_le (by exact_mod_cast le_top)
  have c1' : ContDiffAt ℝ ℓ G1 x := h1.contDiffAt.of_le (by exact_mod_cast le_top)
  have c2' : ContDiffAt ℝ ℓ G2 x := h2.contDiffAt.of_le (by exact_mod_cast le_top)
  have c12 : ContDiffAt ℝ ℓ (G1 - G2) x := c1'.sub c2'
  rw [e, iteratedFDeriv_sub_apply c1 c3, iteratedFDeriv_const_smul_apply c12,
    iteratedFDeriv_sub_apply c1' c2']

/-- all jets of the orbits are differentiable in the observed time (from the F11 quotients) -/
theorem r26t8a_f12_jet_deriv {d : ℕ} (F : Fin 4 → ℝ → Euc d → ℝ)
    (hsm : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → ContDiff ℝ ∞ (F j t))
    (hq : ∀ (j : Fin 4) (hj : (j : ℕ) < 3), ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ eps : ℝ, 0 < eps →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, h ≠ 0 → |h| < delta → 0 ≤ t + h →
          ∀ ell ≤ k, ∀ x, ‖iteratedFDeriv ℝ ell
            (fun y => h⁻¹ * (F j (t + h) y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) x‖ ≤ eps)
    (j : Fin 4) (hj : (j : ℕ) < 3) (ℓ : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Euc d) :
    HasDerivWithinAt (fun v => iteratedFDeriv ℝ ℓ (F j v) x)
      (iteratedFDeriv ℝ ℓ (F ⟨(j : ℕ) + 1, by omega⟩ t) x) (Set.Ici 0) t := by
  refine r26t8a_f12_hasDerivWithinAt _ _ t fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := hq j hj ℓ t ht ε hε
  refine ⟨δ, hδ, fun h' hh0 hh h0 => ?_⟩
  have := h h' hh0 hh h0 ℓ le_rfl x
  rwa [r26t8a_f12_quot_eq _ _ _ (hsm j (t + h') h0) (hsm j t ht) (hsm _ t ht)] at this

/-- scalar version: the value of the orbit is differentiable in the observed time -/
theorem r26t8a_f12_val_deriv {d : ℕ} (F : Fin 4 → ℝ → Euc d → ℝ)
    (hsm : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → ContDiff ℝ ∞ (F j t))
    (hq : ∀ (j : Fin 4) (hj : (j : ℕ) < 3), ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ eps : ℝ, 0 < eps →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, h ≠ 0 → |h| < delta → 0 ≤ t + h →
          ∀ ell ≤ k, ∀ x, ‖iteratedFDeriv ℝ ell
            (fun y => h⁻¹ * (F j (t + h) y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) x‖ ≤ eps)
    (j : Fin 4) (hj : (j : ℕ) < 3) (t : ℝ) (ht : 0 ≤ t) (x : Euc d) :
    HasDerivWithinAt (fun v => F j v x) (F ⟨(j : ℕ) + 1, by omega⟩ t x) (Set.Ici 0) t := by
  refine r26t8a_f12_hasDerivWithinAt _ _ t fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := hq j hj 0 t ht ε hε
  refine ⟨δ, hδ, fun h' hh0 hh h0 => ?_⟩
  have := h h' hh0 hh h0 0 le_rfl x
  rw [norm_iteratedFDeriv_zero] at this
  simpa [smul_eq_mul] using this

/-- the actual classical solution is the shifted orbit -/
theorem r26t8a_f12_gen_orbit (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f : SchwartzMap (Euc d) ℝ) (F : Fin 4 → ℝ → Euc d → ℝ)
    (hFp : ∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t →
      F j t = propagatorW (critCoeff d a beta rho) 0 t (r26t8a_LIter a beta rho j f))
    (hsol : ∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ∃ u,
      IsClassicalAdjointW (critCoeff d a beta rho) t (r26t8a_LIter a beta rho j f) u ∧ F j t = u 0)
    (hsm : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → ContDiff ℝ ∞ (F j t))
    (hq : ∀ (j : Fin 4) (hj : (j : ℕ) < 3), ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ eps : ℝ, 0 < eps →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, h ≠ 0 → |h| < delta → 0 ≤ t + h →
          ∀ ell ≤ k, ∀ x, ‖iteratedFDeriv ℝ ell
            (fun y => h⁻¹ * (F j (t + h) y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) x‖ ≤ eps)
    (j : Fin 4) (hj : (j : ℕ) < 3) (t : ℝ) (ht : 0 ≤ t) (x : Euc d) :
    generatorW (critCoeff d a beta rho) 0 (F j t) x = F ⟨(j : ℕ) + 1, by omega⟩ t x := by
  obtain ⟨θ, Q, c, hθ, hC, O, hρS, huniq⟩ := r26t8a_f11_setup d hd a beta ha hbeta rho hrho
  have hLsucc : r26t8a_LIter a beta rho ((j : ℕ) + 1) f =
      fun x => generatorW (critCoeff d a beta rho) 0 (r26t8a_LIter a beta rho (j : ℕ) f) x := by
    unfold r26t8a_LIter
    rw [Function.iterate_succ_apply']
  rcases ht.eq_or_lt with h0 | hpos
  · -- t = 0: F j 0 is the terminal datum
    subst h0
    have hterm : ∀ i : Fin 4, F i 0 = r26t8a_LIter a beta rho i f := by
      intro i
      obtain ⟨u, hu, hFu⟩ := hsol i 0 le_rfl
      rw [hFu]; exact hu.terminal
    rw [hterm j, hterm ⟨(j : ℕ) + 1, by omega⟩, show ((⟨(j : ℕ) + 1, by omega⟩ : Fin 4) : ℕ) = (j : ℕ) + 1 from rfl,
      hLsucc]
  · -- t > 0: time derivative of the classical solution on the horizon t + 1
    set T : ℝ := t + 1 with hT
    obtain ⟨u, hu, -⟩ := hsol j T (by linarith)
    have huniqC : ∀ r ∈ Set.Icc (0 : ℝ) T, u r = propagatorW (critCoeff d a beta rho) r T
        (r26t8a_LIter a beta rho j f) := by
      intro r hr
      have hprop := HRS.MS.S52B.s52b_prop_isClassical (C := critCoeff d a beta rho) ⟨_, hu⟩
      have hU : HRS.MS.S52B.S52bUniq (critCoeff d a beta rho) T := by rw [hC]; exact huniq T
      exact hU T ⟨by linarith, le_rfl⟩ _ _ _ hu hprop r hr
    have hshift : ∀ r ∈ Set.Icc (0 : ℝ) T, u r = F j (T - r) := by
      intro r hr
      rw [huniqC r hr, r26t8a_prop_shift d hd a beta ha hbeta rho hrho f j r T hr.1 hr.2,
        hFp j (T - r) (by linarith [hr.2])]
    have h1 : (1 : ℝ) ∈ Set.Ioo 0 T := ⟨one_pos, by rw [hT]; linarith⟩
    have hd1 := hu.time_deriv x 1 h1
    have hgen : generatorW (critCoeff d a beta rho) 1 (u 1) = generatorW (critCoeff d a beta rho) 0 (u 1) := by
      rw [hC]; rfl
    rw [hgen] at hd1
    have heq : (fun r' => u r' x) =ᶠ[𝓝 1] fun r' => F j (T - r') x := by
      filter_upwards [Ioo_mem_nhds h1.1 h1.2] with r hr
      exact congrFun (hshift r ⟨hr.1.le, hr.2.le⟩) x
    have hd2 := hd1.congr_of_eventuallyEq heq.symm
    -- derivative of the orbit
    have hψ : HasDerivAt (fun s => F j s x) (F ⟨(j : ℕ) + 1, by omega⟩ t x) t :=
      (r26t8a_f12_val_deriv F hsm hq j hj t ht x).hasDerivAt (Ici_mem_nhds hpos)
    have hlin : HasDerivAt (fun r' : ℝ => T - r') (-1) 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).const_sub T
    have hψ' : HasDerivAt (fun s => F j s x) (F ⟨(j : ℕ) + 1, by omega⟩ t x) ((fun r' : ℝ => T - r') 1) := by
      simpa [hT] using hψ
    have hd3 := hψ'.comp 1 hlin
    have huq := hd2.unique hd3
    have hu1 : u 1 = F j t := by
      rw [hshift 1 ⟨zero_le_one, h1.2.le⟩]; congr 1; rw [hT]; ring
    rw [hu1] at huq
    linarith

theorem r26t8a_f12_gen_sub_const {d : ℕ} (C : WholeCoeff d) (t : ℝ) (g : Euc d → ℝ) (hg : ContDiff ℝ 2 g)
    (c : ℝ) (x : Euc d) :
    generatorW C t (fun y => g y - c) x = generatorW C t g x := by
  have hgrad : gradient (fun y => g y - c) = gradient g := by
    funext y
    apply (InnerProductSpace.toDual ℝ (Euc d)).injective
    rw [toDual_gradient, toDual_gradient, fderiv_sub_const]
  have hlap : Laplacian.laplacian (fun y => g y - c) x = Laplacian.laplacian g x := by
    have := (hg.contDiffAt (x := x)).laplacian_sub (contDiffAt_const (c := c))
    have e : (fun y => g y - c) = g - fun _ => c := rfl
    rw [e]
    simpa using this
  unfold generatorW
  rw [hgrad, hlap]

theorem r26t8a_f12_projected (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (f : SchwartzMap (Euc d) ℝ) (F : Fin 4 → ℝ → Euc d → ℝ)
    (hFp : ∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t →
      F j t = propagatorW (critCoeff d a beta rho) 0 t (r26t8a_LIter a beta rho j f))
    (hsm : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → ContDiff ℝ ∞ (F j t))
    (hgen : ∀ (j : Fin 4) (hj : (j : ℕ) < 3) (t : ℝ), 0 ≤ t → ∀ x,
      generatorW (critCoeff d a beta rho) 0 (F j t) x = F ⟨(j : ℕ) + 1, by omega⟩ t x)
    (j : ℕ) (hj : j ≤ 3) (v : ℝ) (hv : 0 ≤ v) :
    r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
      (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v ⇑f) =
    HRS.Whole.projMean (HRS.Whole.withDensityReal rho) (F ⟨j, by omega⟩ v) := by
  induction j with
  | zero =>
    have h0 := hFp ⟨0, by omega⟩ v hv
    have e : r26t8a_LIter a beta rho 0 f = ⇑f := rfl
    simp only [r26t8a_genPower, r26t8a_projectedOrbit, Nat.rec_zero]
    rw [h0, show ((⟨0, by omega⟩ : Fin 4) : ℕ) = 0 from rfl, e]
  | succ n ih =>
    have ih' := ih (by omega)
    have e : r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (n + 1)
        (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v ⇑f) =
        projGeneratorW (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) 0
          (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) n
            (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v ⇑f)) := rfl
    rw [e, ih']
    funext x
    have hn : (⟨n, by omega⟩ : Fin 4).val < 3 := by simp; omega
    have hL : ∀ y, generatorW (critCoeff d a beta rho) 0 (HRS.Whole.projMean (HRS.Whole.withDensityReal rho) (F ⟨n, by omega⟩ v)) y =
        F ⟨n + 1, by omega⟩ v y := by
      intro y
      unfold HRS.Whole.projMean HRS.Whole.pair
      rw [r26t8a_f12_gen_sub_const _ _ _ (contDiff_infty.1 (hsm _ v hv) 2) _ y]
      exact hgen ⟨n, by omega⟩ hn v hv y
    have hI : ∫ y, generatorW (critCoeff d a beta rho) 0
        (HRS.Whole.projMean (HRS.Whole.withDensityReal rho) (F ⟨n, by omega⟩ v)) y
          ∂(HRS.Whole.withDensityReal rho) =
        HRS.Whole.pair (HRS.Whole.withDensityReal rho) (F ⟨n + 1, by omega⟩ v) := by
      unfold HRS.Whole.pair
      exact integral_congr_ae (Filter.Eventually.of_forall hL)
    show generatorW (critCoeff d a beta rho) 0
        (HRS.Whole.projMean (HRS.Whole.withDensityReal rho) (F ⟨n, by omega⟩ v)) x -
      ∫ y, generatorW (critCoeff d a beta rho) 0
        (HRS.Whole.projMean (HRS.Whole.withDensityReal rho) (F ⟨n, by omega⟩ v)) y
          ∂(HRS.Whole.withDensityReal rho) =
      HRS.Whole.projMean (HRS.Whole.withDensityReal rho) (F ⟨n + 1, by omega⟩ v) x
    rw [hL x, hI]
    rfl

/-- constants do not change derivatives of positive order -/
theorem r26t8a_f12_iter_sub_const {d : ℕ} (G : Euc d → ℝ) (hG : ContDiff ℝ ∞ G) (c : ℝ) (n : ℕ) (x : Euc d) :
    iteratedFDeriv ℝ (n + 1) (fun y => G y - c) x = iteratedFDeriv ℝ (n + 1) G x := by
  have h1 : ContDiffAt ℝ (n + 1 : ℕ) G x := hG.contDiffAt.of_le (by exact_mod_cast le_top)
  have h2 : ContDiffAt ℝ (n + 1 : ℕ) (fun _ : Euc d => c) x := contDiffAt_const
  have e : (fun y => G y - c) = G - fun _ => c := rfl
  rw [e, iteratedFDeriv_sub_apply h1 h2, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
  simp

/-- continuity of the projected orbit in the positive-jet norm -/
theorem r26t8a_f12_cont {d : ℕ} (F : Fin 4 → ℝ → Euc d → ℝ) (cc : Fin 4 → ℝ → ℝ)
    (hsm : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → ContDiff ℝ ∞ (F j t))
    (hcb : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → ∀ k : ℕ, MemCb k (F j t))
    (hq : ∀ (j : Fin 4) (hj : (j : ℕ) < 3), ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ eps : ℝ, 0 < eps →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, h ≠ 0 → |h| < delta → 0 ≤ t + h →
          ∀ ell ≤ k, ∀ x, ‖iteratedFDeriv ℝ ell
            (fun y => h⁻¹ * (F j (t + h) y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) x‖ ≤ eps)
    (j : Fin 4) (hj : (j : ℕ) < 3) (K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun v => testSizeE K (fun x => (F j v x - cc j v) - (F j t x - cc j t)))
      (𝓝[Set.Ici 0] t) (𝓝 0) := by
  -- a common bound for the derivatives of order at most `K` of the derivative orbit
  have hB : ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ K, ∀ x, ‖iteratedFDeriv ℝ i (F ⟨(j : ℕ) + 1, by omega⟩ t) x‖ ≤ B := by
    have hb : ∀ i : Fin (K + 1), ∃ b : ℝ, ∀ x, ‖iteratedFDeriv ℝ i (F ⟨(j : ℕ) + 1, by omega⟩ t) x‖ ≤ b := by
      intro i
      obtain ⟨b, hb⟩ := (hcb ⟨(j : ℕ) + 1, by omega⟩ t ht K).2 i (by omega)
      exact ⟨b, fun x => hb ⟨x, rfl⟩⟩
    choose b hb using hb
    refine ⟨∑ i, |b i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i hi x => ?_⟩
    calc _ ≤ b ⟨i, by omega⟩ := hb ⟨i, by omega⟩ x
      _ ≤ |b ⟨i, by omega⟩| := le_abs_self _
      _ ≤ ∑ i, |b i| := Finset.single_le_sum (f := fun i => |b i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _)
  obtain ⟨B, hB0, hB⟩ := hB
  obtain ⟨δ₀, hδ₀, hq1⟩ := hq j hj K t ht 1 one_pos
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεt
  · exact Filter.Eventually.of_forall fun _ => le_top
  set ε' : ℝ := ε.toReal with hε'
  have hε'0 : 0 < ε' := ENNReal.toReal_pos hε.ne' hεt
  set δ : ℝ := min δ₀ (ε' / (1 + B)) with hδ
  have hδ0 : 0 < δ := lt_min hδ₀ (by positivity)
  have hmem : Set.Ici (0 : ℝ) ∩ Metric.ball t δ ∈ 𝓝[Set.Ici 0] t :=
    inter_mem_nhdsWithin _ (Metric.ball_mem_nhds t hδ0)
  filter_upwards [hmem] with v hv
  obtain ⟨hv0, hvb⟩ := hv
  have hvt : |v - t| < δ := by rwa [Metric.mem_ball, Real.dist_eq] at hvb
  have hv0' : 0 ≤ v := hv0
  unfold testSizeE
  refine iSup_le fun i => iSup_le fun x => ?_
  -- the derivative of order `i + 1`
  have hfun : (fun x => (F j v x - cc j v) - (F j t x - cc j t)) =
      fun x => (F j v x - F j t x) - (cc j v - cc j t) := by funext y; ring
  have hsmd : ContDiff ℝ ∞ (fun x => F j v x - F j t x) := (hsm j v hv0').sub (hsm j t ht)
  rw [hfun, r26t8a_f12_iter_sub_const _ hsmd]
  have hsub : iteratedFDeriv ℝ ((i : ℕ) + 1) (fun x => F j v x - F j t x) x =
      iteratedFDeriv ℝ ((i : ℕ) + 1) (F j v) x - iteratedFDeriv ℝ ((i : ℕ) + 1) (F j t) x := by
    have c1 : ContDiffAt ℝ ((i : ℕ) + 1 : ℕ) (F j v) x :=
      (hsm j v hv0').contDiffAt.of_le (by exact_mod_cast le_top)
    have c2 : ContDiffAt ℝ ((i : ℕ) + 1 : ℕ) (F j t) x :=
      (hsm j t ht).contDiffAt.of_le (by exact_mod_cast le_top)
    exact iteratedFDeriv_sub_apply c1 c2
  rw [hsub]
  by_cases hvt0 : v = t
  · subst hvt0; simp
  · set h : ℝ := v - t with hh
    have hh0 : h ≠ 0 := sub_ne_zero.2 hvt0
    have hvh : v = t + h := by rw [hh]; ring
    have hhd : |h| < δ₀ := lt_of_lt_of_le hvt (min_le_left _ _)
    have h0 : 0 ≤ t + h := by rw [← hvh]; exact hv0'
    have key := hq1 h hh0 hhd h0 ((i : ℕ) + 1) (by omega) x
    rw [r26t8a_f12_quot_eq _ _ _ (hsm j (t + h) h0) (hsm j t ht) (hsm _ t ht)] at key
    rw [← hvh] at key
    have hDF := hB ((i : ℕ) + 1) (by omega) x
    have hn : ‖iteratedFDeriv ℝ ((i : ℕ) + 1) (F j v) x - iteratedFDeriv ℝ ((i : ℕ) + 1) (F j t) x‖ ≤
        |h| * (1 + B) := by
      have e : iteratedFDeriv ℝ ((i : ℕ) + 1) (F j v) x - iteratedFDeriv ℝ ((i : ℕ) + 1) (F j t) x =
          h • (h⁻¹ • (iteratedFDeriv ℝ ((i : ℕ) + 1) (F j v) x - iteratedFDeriv ℝ ((i : ℕ) + 1) (F j t) x)) := by
        rw [smul_smul, mul_inv_cancel₀ hh0, one_smul]
      rw [e, norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg h)
      calc ‖h⁻¹ • (iteratedFDeriv ℝ ((i : ℕ) + 1) (F j v) x - iteratedFDeriv ℝ ((i : ℕ) + 1) (F j t) x)‖
          = ‖(h⁻¹ • (iteratedFDeriv ℝ ((i : ℕ) + 1) (F j v) x - iteratedFDeriv ℝ ((i : ℕ) + 1) (F j t) x) -
              iteratedFDeriv ℝ ((i : ℕ) + 1) (F ⟨(j : ℕ) + 1, by omega⟩ t) x) +
              iteratedFDeriv ℝ ((i : ℕ) + 1) (F ⟨(j : ℕ) + 1, by omega⟩ t) x‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ ≤ 1 + B := add_le_add key hDF
    have hlt : |h| * (1 + B) ≤ ε' := by
      have h1 : |h| ≤ ε' / (1 + B) := (hvt.trans_le (min_le_right _ _)).le
      have hp : 0 < 1 + B := by linarith
      calc |h| * (1 + B) ≤ ε' / (1 + B) * (1 + B) := mul_le_mul_of_nonneg_right h1 hp.le
        _ = ε' := by field_simp
    calc ENNReal.ofReal ‖iteratedFDeriv ℝ ((i : ℕ) + 1) (F j v) x - iteratedFDeriv ℝ ((i : ℕ) + 1) (F j t) x‖
        ≤ ENNReal.ofReal ε' := ENNReal.ofReal_le_ofReal (hn.trans hlt)
      _ = ε := ENNReal.ofReal_toReal hεt

/-- the mean of the orbit is differentiable in the observed time (uniform difference quotients, probability measure) -/
theorem r26t8a_f12_mean_deriv {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (F : Fin 4 → ℝ → Euc d → ℝ)
    (hint : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → Integrable (F j t) μ)
    (hq : ∀ (j : Fin 4) (hj : (j : ℕ) < 3), ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ eps : ℝ, 0 < eps →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, h ≠ 0 → |h| < delta → 0 ≤ t + h →
          ∀ ell ≤ k, ∀ x, ‖iteratedFDeriv ℝ ell
            (fun y => h⁻¹ * (F j (t + h) y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) x‖ ≤ eps)
    (j : Fin 4) (hj : (j : ℕ) < 3) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun v => ∫ y, F j v y ∂μ) (∫ y, F ⟨(j : ℕ) + 1, by omega⟩ t y ∂μ) (Set.Ici 0) t := by
  refine r26t8a_f12_hasDerivWithinAt _ _ t fun ε hε => ?_
  obtain ⟨δ, hδ, h⟩ := hq j hj 0 t ht ε hε
  refine ⟨δ, hδ, fun h' hh0 hh h0 => ?_⟩
  have i1 := hint j (t + h') h0
  have i2 := hint j t ht
  have i3 := hint ⟨(j : ℕ) + 1, by omega⟩ t ht
  have e : h'⁻¹ • (∫ y, F j (t + h') y ∂μ - ∫ y, F j t y ∂μ) - ∫ y, F ⟨(j : ℕ) + 1, by omega⟩ t y ∂μ =
      ∫ y, (h'⁻¹ * (F j (t + h') y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) ∂μ := by
    have i12 : Integrable (fun y => F j (t + h') y - F j t y) μ := i1.sub i2
    have i13 : Integrable (fun y => h'⁻¹ * (F j (t + h') y - F j t y)) μ := i12.const_mul h'⁻¹
    rw [integral_sub i13 i3, integral_const_mul, integral_sub i1 i2, smul_eq_mul]
  rw [e]
  have := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun y => h'⁻¹ * (F j (t + h') y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) (C := ε)
    (Filter.Eventually.of_forall fun y => by
      have := h h' hh0 hh h0 0 le_rfl y
      rwa [norm_iteratedFDeriv_zero] at this)
  simpa using this

theorem r26t8a_f12_deriv_clause {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (F : Fin 4 → ℝ → Euc d → ℝ)
    (hsm : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → ContDiff ℝ ∞ (F j t))
    (hint : ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → Integrable (F j t) μ)
    (hq : ∀ (j : Fin 4) (hj : (j : ℕ) < 3), ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ eps : ℝ, 0 < eps →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, h ≠ 0 → |h| < delta → 0 ≤ t + h →
          ∀ ell ≤ k, ∀ x, ‖iteratedFDeriv ℝ ell
            (fun y => h⁻¹ * (F j (t + h) y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) x‖ ≤ eps)
    (j : Fin 4) (hj : (j : ℕ) < 3) (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (x : Euc d) :
    HasDerivWithinAt (fun v => iteratedFDeriv ℝ k (HRS.Whole.projMean μ (F j v)) x)
      (iteratedFDeriv ℝ k (HRS.Whole.projMean μ (F ⟨(j : ℕ) + 1, by omega⟩ t)) x) (Set.Ici 0) t := by
  cases k with
  | succ n =>
    have eq : ∀ (i : Fin 4) (v : ℝ), 0 ≤ v →
        iteratedFDeriv ℝ (n + 1) (HRS.Whole.projMean μ (F i v)) x = iteratedFDeriv ℝ (n + 1) (F i v) x :=
      fun i v hv => r26t8a_f12_iter_sub_const _ (hsm i v hv) _ n x
    rw [eq _ t ht]
    exact (r26t8a_f12_jet_deriv F hsm hq j hj (n + 1) t ht x).congr (fun v hv => eq j v hv) (eq j t ht)
  | zero =>
    have hs : HasDerivWithinAt (fun v => HRS.Whole.projMean μ (F j v) x)
        (HRS.Whole.projMean μ (F ⟨(j : ℕ) + 1, by omega⟩ t) x) (Set.Ici 0) t := by
      have h1 := r26t8a_f12_val_deriv F hsm hq j hj t ht x
      have h2 := r26t8a_f12_mean_deriv μ F hint hq j hj t ht
      exact h1.sub h2
    have e0 : ∀ (g : Euc d → ℝ), iteratedFDeriv ℝ 0 g x =
        (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (g x) := fun g => by
      rw [iteratedFDeriv_zero_eq_comp]; rfl
    simp only [e0]
    exact ((continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
      |>.hasFDerivAt.comp_hasDerivWithinAt t hs)

theorem r26t8a_f12_mu_prob {d : ℕ} (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := by
  have hrho_eq := critical_thermal_eq d hd a beta ha hbeta hrho
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cth, cth, BU, hT⟩ := _root_.S45.s45_thermal_data hd hs0 hsd ha hbeta
  rw [hrho_eq]
  exact HRS.Whole.Q09A.measure_isProb hT.prob

theorem r26t8a_projected_orbit_regularity (d : ℕ) (hd : 2 ≤ d) (a beta m : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) :
    (∀ alpha : MultiIndex d, ∀ t : ℝ, 0 ≤ t → ∃ f,
      IsClassicalAdjointW (critCoeff d a beta rho) t (oscTestFun m alpha) f) ∧
    (∀ alpha : MultiIndex d, ∀ r t : ℝ, 0 ≤ r → r ≤ t →
      propagatorW (critCoeff d a beta rho) r t (oscTestFun m alpha) =
        propagatorW (critCoeff d a beta rho) 0 (t - r) (oscTestFun m alpha)) ∧
    (∀ alpha : MultiIndex d, ∀ j : ℕ, j ≤ 2 → ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun v => testSizeE (testOrder d)
        (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
          (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha)) -
         r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
          (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) t (oscTestFun m alpha))))
        (𝓝[Set.Ici 0] t) (𝓝 0)) ∧
    (∀ alpha : MultiIndex d, ∀ j : ℕ, j ≤ 1 → ∀ k : ℕ, k ≤ testOrder d → ∀ t : ℝ, 0 ≤ t → ∀ x,
      HasDerivWithinAt (fun v => iteratedFDeriv ℝ k
        (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
          (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha))) x)
        (iteratedFDeriv ℝ k (r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (j + 1)
          (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) t (oscTestFun m alpha))) x)
        (Set.Ici 0) t) ∧
    (∀ alpha : MultiIndex d, ∀ j : ℕ, j ≤ 2 → ∀ v : ℝ, 0 ≤ v →
      r26t8a_genPower (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) j
        (r26t8a_projectedOrbit (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha)) =
      HRS.Whole.projMean (HRS.Whole.withDensityReal rho) (propagatorW (critCoeff d a beta rho) 0 v
        (r26t8a_LIter a beta rho j (oscTestFun m alpha)))) := by
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) := r26t8a_f12_mu_prob hd ha hbeta hrho
  -- the orbit data for the Schwartz feature `φ_α`
  have horb : ∀ alpha : MultiIndex d, ∃ (f : SchwartzMap (Euc d) ℝ) (F : Fin 4 → ℝ → Euc d → ℝ),
      (⇑f = oscTestFun m alpha) ∧
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t →
        F j t = propagatorW (critCoeff d a beta rho) 0 t (r26t8a_LIter a beta rho j f)) ∧
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ∃ u,
        IsClassicalAdjointW (critCoeff d a beta rho) t (r26t8a_LIter a beta rho j f) u ∧ F j t = u 0) ∧
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, MemCb k (F j t)) ∧
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ContDiff ℝ ∞ (F j t)) ∧
      (∀ (j : Fin 4) (hj : (j : ℕ) < 3), ∀ k : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ eps : ℝ, 0 < eps →
        ∃ delta : ℝ, 0 < delta ∧ ∀ h : ℝ, h ≠ 0 → |h| < delta → 0 ≤ t + h →
          ∀ ell ≤ k, ∀ x, ‖iteratedFDeriv ℝ ell
            (fun y => h⁻¹ * (F j (t + h) y - F j t y) - F ⟨(j : ℕ) + 1, by omega⟩ t y) x‖ ≤ eps) := by
    intro alpha
    obtain ⟨f, hf, -⟩ := r26t8a_feature_weight d m alpha
    obtain ⟨F, h1, h2, h3, h4, h5⟩ := r26t8a_four_orbits d hd a beta ha hbeta rho hrho f
    exact ⟨f, F, hf, h1, h2, h3, h4, h5⟩
  have hint : ∀ (F : Fin 4 → ℝ → Euc d → ℝ),
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ∀ k : ℕ, MemCb k (F j t)) →
      (∀ j : Fin 4, ∀ t : ℝ, 0 ≤ t → ContDiff ℝ ∞ (F j t)) →
      ∀ (j : Fin 4) (t : ℝ), 0 ≤ t → Integrable (F j t) (HRS.Whole.withDensityReal rho) := by
    intro F hcb hsm j t ht
    obtain ⟨B, hB⟩ := (hcb j t ht 0).2 0 le_rfl
    refine Integrable.of_bound (hsm j t ht).continuous.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => ?_)
    have := hB ⟨x, rfl⟩
    simp only [norm_iteratedFDeriv_zero] at this
    exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro alpha t ht
    obtain ⟨f, F, hf, hFp, hsol, -⟩ := horb alpha
    obtain ⟨u, hu, -⟩ := hsol 0 t ht
    exact ⟨u, by rw [← hf]; exact hu⟩
  · intro alpha r t hr hrt
    obtain ⟨f, F, hf, -⟩ := horb alpha
    rw [← hf]
    exact r26t8a_prop_shift d hd a beta ha hbeta rho hrho f 0 r t hr hrt
  · intro alpha j hj t ht
    obtain ⟨f, F, hf, hFp, hsol, hcb, hsm, hq⟩ := horb alpha
    have hgen := r26t8a_f12_gen_orbit d hd a beta ha hbeta rho hrho f F hFp hsol hsm hq
    have hE := r26t8a_f12_projected d hd a beta ha hbeta rho f F hFp hsm
      (fun j hj t ht x => hgen j hj t ht x)
    have hjF : (j : ℕ) < 3 := by omega
    rw [← hf]
    have hlim := r26t8a_f12_cont F (fun i v => HRS.Whole.pair (HRS.Whole.withDensityReal rho) (F i v)) hsm hcb hq
      ⟨j, by omega⟩ hjF (testOrder d) t ht
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    have e1 := hE j (by omega) v hv
    have e2 := hE j (by omega) t ht
    rw [e1, e2]
    rfl
  · intro alpha j hj k hk t ht x
    obtain ⟨f, F, hf, hFp, hsol, hcb, hsm, hq⟩ := horb alpha
    have hgen := r26t8a_f12_gen_orbit d hd a beta ha hbeta rho hrho f F hFp hsol hsm hq
    have hE := r26t8a_f12_projected d hd a beta ha hbeta rho f F hFp hsm
      (fun j hj t ht x => hgen j hj t ht x)
    have hjF : (j : ℕ) < 3 := by omega
    have hd1 := r26t8a_f12_deriv_clause (HRS.Whole.withDensityReal rho) F hsm (hint F hcb hsm) hq
      ⟨j, by omega⟩ hjF k t ht x
    rw [← hf]
    have e2 := hE (j + 1) (by omega) t ht
    rw [e2]
    refine hd1.congr (fun v hv => ?_) ?_
    · have e1 := hE j (by omega) v hv
      rw [e1]
    · have e1 := hE j (by omega) t ht
      rw [e1]
  · intro alpha j hj v hv
    obtain ⟨f, F, hf, hFp, hsol, hcb, hsm, hq⟩ := horb alpha
    have hgen := r26t8a_f12_gen_orbit d hd a beta ha hbeta rho hrho f F hFp hsol hsm hq
    have hE := r26t8a_f12_projected d hd a beta ha hbeta rho f F hFp hsm
      (fun j hj t ht x => hgen j hj t ht x)
    rw [← hf, hE j (by omega) v hv, hFp ⟨j, by omega⟩ v hv]

end HRS.MS.R26T8A

end
