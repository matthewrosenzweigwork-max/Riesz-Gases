import HRS.MS.MfeConfAux43

/-!
# S.B.1, packet F6 (part 6): the time-integrated cut-off inequality with a tilted reference

`sb1_time_ineq`: the transplant of `P4MolData.time_ineq` (HRS/MP/SelfSimP4MolE5.lean) with the source `u S`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {θ T : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Ψ : ℝ → EucConfig d N → ℝ} {w : ℝ → EucConfig d N → EucConfig d N} {Wψ : ℝ → EucConfig d N → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem sb1_time_ineq (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV) (hv : 0 < v) (hθ : 0 < θ)
    (hΨc : Continuous (Function.uncurry Ψ)) (hΨg : ∀ r x, HasFDerivAt (Ψ r) (p4InnerL (w r x)) x)
    (hwc : Continuous (Function.uncurry w)) (hw1 : ∀ r, ContDiff ℝ 1 (w r))
    (hdwc : Continuous (Function.uncurry fun r x => sb1div (w r) x))
    (hWc : Continuous (Function.uncurry Wψ))
    (hWd : ∀ r ∈ Set.Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => Ψ s x) (Wψ r x) r)
    {χ : EucConfig d N → ℝ} (hχ : ContDiff ℝ 1 χ) (hχs : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ x, χ x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) t x ≤
      (∫ x, χ x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) 0 x) +
      (∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) +
      t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ)) -
      (∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x *
        (w s x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))) -
      ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x *
        fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) := by
  have ht0 : 0 ≤ t := ht.1
  have hcu := hP.cont_u hv
  have hca := hP.cont_a hv
  have hcΛ : Continuous (fun p : ℝ × EucConfig d N =>
      p4m_Lam v θ (μ p.1) (fun y => H y + Ψ p.1 y) p.2) := by
    unfold p4m_Lam
    refine ((hcu.log fun p => (hP.pos_u hv p.1 p.2).ne').add continuous_const).add ?_
    exact ((hP.Vc.comp (Continuous.prodMk continuous_fst continuous_snd)).add hΨc).div_const θ
  have hcχ : Continuous χ := hχ.continuous
  have hdχ : ∀ k : Fin N × Fin d, Continuous (fun x => fderiv ℝ χ x (configBasis d N k)) := fun k =>
    (hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdχs : ∀ k : Fin N × Fin d, HasCompactSupport (fun x => fderiv ℝ χ x (configBasis d N k)) :=
    fun k => hχs.fderiv_apply ℝ _
  have hcχ2 : Continuous (fun p : ℝ × EucConfig d N => χ p.2) := hcχ.comp continuous_snd
  have hbc' : Continuous (fun p : ℝ × EucConfig d N => b p.1 p.2) := hP.bc
  have hwc' : Continuous (fun p : ℝ × EucConfig d N => w p.1 p.2) := hwc
  -- the source is jointly continuous
  have hSc : Continuous (fun p : ℝ × EucConfig d N => sb1S θ b w Wψ p.1 p.2) := by
    unfold sb1S
    refine ((hdwc.neg.sub (((p4m_continuous_innerL.comp hwc').clm_apply hbc').div_const θ)).add
      ((p4m_continuous_q.comp hwc').div_const θ)).add (hWc.div_const θ)
  -- the integrand of the time derivative
  have hg : Continuous (fun p : ℝ × EucConfig d N =>
      χ p.2 * (p4m_a v θ (μ p.1) (b p.1) p.2 * p4m_Lam v θ (μ p.1) (fun y => H y + Ψ p.1 y) p.2 +
        p4Mol v (μ p.1) p.2 * Wψ p.1 p.2 / θ)) :=
    hcχ2.mul ((hca.mul hcΛ).add ((hcu.mul hWc).div_const θ))
  have hgz : ∀ s x, χ x = 0 → χ x * (p4m_a v θ (μ s) (b s) x *
      p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x + p4Mol v (μ s) x * Wψ s x / θ) = 0 :=
    fun s x hx => by simp [hx]
  have hPhic : Continuous (fun p : ℝ × EucConfig d N =>
      p4m_Phi v θ μ (fun s y => H y + Ψ s y) p.1 p.2) := by
    unfold p4m_Phi
    refine (hcu.mul (hcu.log fun p => (hP.pos_u hv p.1 p.2).ne')).add ?_
    exact (hcu.mul ((hP.Vc.comp (Continuous.prodMk continuous_fst continuous_snd)).add hΨc)).div_const θ
  -- pointwise fundamental theorem of calculus
  have hftc : ∀ x, p4m_Phi v θ μ (fun s y => H y + Ψ s y) t x - p4m_Phi v θ μ (fun s y => H y + Ψ s y) 0 x =
      ∫ s in Set.Icc (0 : ℝ) t, (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x +
        p4Mol v (μ s) x * Wψ s x / θ) := by
    intro x
    have hPc : Continuous (fun s => p4m_Phi v θ μ (fun s y => H y + Ψ s y) s x) :=
      hPhic.comp (Continuous.prodMk continuous_id continuous_const)
    have hfc : Continuous (fun s => p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x +
        p4Mol v (μ s) x * Wψ s x / θ) :=
      ((hca.mul hcΛ).add ((hcu.mul hWc).div_const θ)).comp
        (Continuous.prodMk continuous_id (continuous_const (y := x)))
    have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht0 hPc.continuousOn
      (f' := fun s => p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x +
        p4Mol v (μ s) x * Wψ s x / θ)
      (fun s hs => (sb1_hasDerivAt_Phi hP hv hWd x ⟨hs.1, lt_of_lt_of_le hs.2 ht.2⟩).hasDerivWithinAt)
      (hfc.intervalIntegrable 0 t)
    rw [intervalIntegral.integral_of_le ht0, ← integral_Icc_eq_integral_Ioc] at this
    exact this.symm
  have hΦi : ∀ s, Integrable (fun x => χ x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) s x) := fun s =>
    p4m_int_of_supp (hcχ.mul (hPhic.comp (Continuous.prodMk continuous_const continuous_id)))
      hχs fun x hx => by simp [hx]
  have hF : (∫ x, χ x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) t x) -
      (∫ x, χ x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) 0 x) =
      ∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ x * (p4m_a v θ (μ s) (b s) x *
        p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x + p4Mol v (μ s) x * Wψ s x / θ) := by
    rw [← integral_sub (hΦi t) (hΦi 0)]
    have e : ∀ x, χ x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) t x -
        χ x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) 0 x =
        ∫ s in Set.Icc (0 : ℝ) t, χ x * (p4m_a v θ (μ s) (b s) x *
          p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x + p4Mol v (μ s) x * Wψ s x / θ) := by
      intro x
      rw [integral_const_mul, ← hftc x]
      ring
    simp_rw [e]
    exact (p4m_swap_time (f := fun s x => χ x * (p4m_a v θ (μ s) (b s) x *
      p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x + p4Mol v (μ s) x * Wψ s x / θ)) hg hχs hgz t).symm
  -- continuity in time of the parametric integrals
  have hcg := p4m_cont_param_cs (f := fun s x => χ x * (p4m_a v θ (μ s) (b s) x *
    p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x + p4Mol v (μ s) x * Wψ s x / θ)) hg hχs hgz
  have hT1c : Continuous (fun p : ℝ × EucConfig d N => χ p.2 * (p4Mol v (μ p.1) p.2 * sb1S θ b w Wψ p.1 p.2)) :=
    hcχ2.mul (hcu.mul hSc)
  have hcT1 := p4m_cont_param_cs (f := fun s x => χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) hT1c hχs
    (fun s x hx => by simp [hx])
  have hT2c : ∀ k : Fin N × Fin d, Continuous (fun p : ℝ × EucConfig d N =>
      p4Mol v (μ p.1) p.2 * (w p.1 p.2 k.1 k.2 * fderiv ℝ χ p.2 (configBasis d N k))) := fun k =>
    hcu.mul (((p4m_continuous_coord k).comp hwc').mul ((hdχ k).comp continuous_snd))
  have hcT2 := fun k : Fin N × Fin d => p4m_cont_param_cs (f := fun s x => p4Mol v (μ s) x *
    (w s x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))) (hT2c k) (hdχs k) (fun s x hx => by simp [hx])
  have hEc : ∀ k : Fin N × Fin d, Continuous (fun p : ℝ × EucConfig d N =>
      p4m_Lam v θ (μ p.1) (fun y => H y + Ψ p.1 y) p.2 * fderiv ℝ χ p.2 (configBasis d N k) *
        (θ * p4m_gu v (μ p.1) k p.2 - p4m_B v (μ p.1) (b p.1) k p.2)) := fun k =>
    (hcΛ.mul ((hdχ k).comp continuous_snd)).mul (hP.cont_J hv k)
  have hcE := fun k : Fin N × Fin d => p4m_cont_param_cs (f := fun s x =>
    p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x * fderiv ℝ χ x (configBasis d N k) *
      (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) (hEc k) (hdχs k) (fun s x hx => by simp [hx])
  -- the fixed-time inequality at every time
  have hfix : ∀ s, ∫ x, χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x +
        p4Mol v (μ s) x * Wψ s x / θ) ≤
      (∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) + N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ) -
      (∑ k : Fin N × Fin d, ∫ x, p4Mol v (μ s) x * (w s x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))) -
      ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) := by
    intro s
    haveI := hP.prob s
    have hfx := sb1_fixed_time hv (hP.hm s) hθ (hP.bl s) hP.hB hP.hK (hP.bg s) (H := H) (Ψ := Ψ s) (w := w s)
      (fun x => hP.grad s x) (hΨg s) (hw1 s) hχ hχs hχ0 hχ1
    have hcs : ∀ g : EucConfig d N → ℝ, Continuous g → Integrable (fun x => χ x * g x) := fun g hgc =>
      p4m_int_of_supp (hcχ.mul hgc) hχs fun x hx => by simp [hx]
    have hAi : Integrable (fun x => χ x * (p4m_a v θ (μ s) (b s) x *
        p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x)) :=
      hcs _ ((hca.comp (Continuous.prodMk continuous_const continuous_id)).mul
        (hcΛ.comp (Continuous.prodMk continuous_const continuous_id)))
    have hWi : Integrable (fun x => χ x * (p4Mol v (μ s) x * Wψ s x / θ)) :=
      hcs _ (((hcu.comp (Continuous.prodMk continuous_const continuous_id)).mul
        (hWc.comp (Continuous.prodMk continuous_const continuous_id))).div_const θ)
    have e : ∫ x, χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x +
        p4Mol v (μ s) x * Wψ s x / θ) =
        (∫ x, χ x * (p4m_a v θ (μ s) (b s) x * p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x)) +
          ∫ x, χ x * (p4Mol v (μ s) x * Wψ s x / θ) := by
      rw [← integral_add hAi hWi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    have hP1 : Continuous (fun x => sb1div (w s) x) := hdwc.comp (Continuous.prodMk continuous_const continuous_id)
    have hP2 : Continuous (fun x => p4InnerL (w s x) (b s x)) :=
      ((p4m_continuous_innerL.comp (hwc.comp (Continuous.prodMk continuous_const continuous_id))).clm_apply
        (hbc'.comp (Continuous.prodMk continuous_const continuous_id)))
    have hP3 : Continuous (fun x => p4m_q (w s x)) :=
      p4m_continuous_q.comp (hwc.comp (Continuous.prodMk continuous_const continuous_id))
    have hu_s : Continuous (p4Mol v (μ s)) := hcu.comp (Continuous.prodMk continuous_const continuous_id)
    have hAi2 : Integrable (fun x => χ x * (p4Mol v (μ s) x *
        (-(sb1div (w s) x) - p4InnerL (w s x) (b s x) / θ + p4m_q (w s x) / θ))) :=
      hcs _ (hu_s.mul ((hP1.neg.sub (hP2.div_const θ)).add (hP3.div_const θ)))
    have e2 : ∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x) =
        (∫ x, χ x * (p4Mol v (μ s) x *
          (-(sb1div (w s) x) - p4InnerL (w s x) (b s x) / θ + p4m_q (w s x) / θ))) +
          ∫ x, χ x * (p4Mol v (μ s) x * Wψ s x / θ) := by
      rw [← integral_add hAi2 hWi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [sb1S]; ring
    rw [e, e2]
    linarith
  have hRc : Continuous (fun s : ℝ => (∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) +
      N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ) -
      (∑ k : Fin N × Fin d, ∫ x, p4Mol v (μ s) x * (w s x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))) -
      ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) :=
    ((hcT1.add continuous_const).sub (continuous_finset_sum _ fun k _ => hcT2 k)).sub
      (continuous_finset_sum _ fun k _ => hcE k)
  have hmono := setIntegral_mono_on (hcg.integrableOn_Icc (μ := volume) (a := 0) (b := t))
    (hRc.integrableOn_Icc (μ := volume) (a := 0) (b := t)) measurableSet_Icc
    (fun s _ => hfix s)
  have hRint : ∫ s in Set.Icc (0 : ℝ) t, ((∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) +
      N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ) -
      (∑ k : Fin N × Fin d, ∫ x, p4Mol v (μ s) x * (w s x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))) -
      ∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) =
      (∫ s in Set.Icc (0 : ℝ) t, ∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) +
      t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ)) -
      (∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x *
        (w s x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))) -
      ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x *
        fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) := by
    have i1 : IntegrableOn (fun s : ℝ => ∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x))
        (Set.Icc (0 : ℝ) t) := hcT1.integrableOn_Icc (μ := volume)
    have i2 : IntegrableOn (fun s : ℝ => N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ))
        (Set.Icc (0 : ℝ) t) := continuous_const.integrableOn_Icc (μ := volume)
    have i3 : ∀ k : Fin N × Fin d, IntegrableOn (fun s : ℝ => ∫ x, p4Mol v (μ s) x *
        (w s x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))) (Set.Icc (0 : ℝ) t) :=
      fun k => (hcT2 k).integrableOn_Icc (μ := volume)
    have i4 : ∀ k : Fin N × Fin d, IntegrableOn (fun s : ℝ => ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x *
        fderiv ℝ χ x (configBasis d N k) * (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x))
        (Set.Icc (0 : ℝ) t) := fun k => (hcE k).integrableOn_Icc (μ := volume)
    have i12 : IntegrableOn (fun s : ℝ => (∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) +
        N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ)) (Set.Icc (0 : ℝ) t) := i1.add i2
    have i123 : IntegrableOn (fun s : ℝ => (∫ x, χ x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) +
        N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ) -
        (∑ k : Fin N × Fin d, ∫ x, p4Mol v (μ s) x * (w s x k.1 k.2 * fderiv ℝ χ x (configBasis d N k))))
        (Set.Icc (0 : ℝ) t) := i12.sub (integrable_finset_sum _ fun k _ => i3 k)
    rw [integral_sub i123 (integrable_finset_sum _ fun k _ => i4 k), integral_sub i12
      (integrable_finset_sum _ fun k _ => i3 k), integral_add i1 i2, integral_finset_sum _ fun k _ => i3 k,
      integral_finset_sum _ fun k _ => i4 k, setIntegral_const]
    simp [Measure.real, Real.volume_Icc, ht0]
  have h1 := hF.trans_le hmono
  rw [hRint] at h1
  linarith

end

end HRS.MS.MfeConf
