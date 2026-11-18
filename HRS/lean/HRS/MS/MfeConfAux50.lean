import HRS.MS.MfeConfAux49

/-!
# S.B.1, packet F6 (part 12): the mollified entropy inequality along the tilted reference

`sb1_mol_ineq`: for the mollified flow `u_s = G_v * μ_s`, with `Φ_s = u log u + u (H + Ψ_s)/θ`,
`∫ Φ_t ≤ ∫ Φ_0 + ∫_0^t ∫ u_s S_s ds + t N Kl² (N d v)/(4θ)`,
`S = -div w - ⟨w,b⟩/θ + |w|²/θ + ∂_sΨ/θ` (`b` the drift, `∇H = -b`, `∇Ψ_s = w_s`, the cut-off removed).
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {θ T : ℝ} {b w : ℝ → EucConfig d N → EucConfig d N} {H : EucConfig d N → ℝ}
  {Ψ Wψ : ℝ → EucConfig d N → ℝ} {CΨ Bw Kw CS : ℝ → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem sb1_V_bound (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (s : ℝ) (x : EucConfig d N) :
    |H x + Ψ s x| ≤ (CV + CΨ s) * (1 + p4m_q x) := by
  have h1 := hP.Vg s x
  have h2 := hΨ.Ψg s x
  calc |H x + Ψ s x| ≤ |H x| + |Ψ s x| := abs_add_le _ _
    _ ≤ CV * (1 + p4m_q x) + CΨ s * (1 + p4m_q x) := add_le_add h1 h2
    _ = _ := by ring

theorem sb1_CV_nonneg (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV) : 0 ≤ CV := by
  have := hP.Vg 0 0
  have h0 : p4m_q (0 : EucConfig d N) = 0 := by simp [p4m_q]
  simp only [h0] at this
  nlinarith [abs_nonneg (H 0)]

theorem sb1_tendsto_free_t (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hv : 0 < v) (hθ : 0 < θ) (s : ℝ) :
    Tendsto (fun n : ℕ => ∫ x, p4m_chi ((n : ℝ) + 1) x *
        p4m_Phi v θ μ (fun s y => H y + Ψ s y) s x) atTop
      (𝓝 (∫ x, p4m_Phi v θ μ (fun s y => H y + Ψ s y) s x)) := by
  haveI := hP.prob s
  have hM0 := sb1_M_nonneg hP
  have hCV := sb1_CV_nonneg hP
  have hΨs := (hΨ.nn s).1
  have hVc : Continuous (fun y => H y + Ψ s y) :=
    (hP.Vc.comp (Continuous.prodMk (continuous_const (y := s)) continuous_id)).add
      (hΨ.Ψc.comp (Continuous.prodMk (continuous_const (y := s)) continuous_id))
  exact sb1_tendsto_free hv hθ (hP.hm s) (hP.hM s) hM0 (by linarith : 0 ≤ CV + CΨ s) hVc
    (fun x => sb1_V_bound hP hΨ s x)

theorem sb1_mol_ineq (hP : P4MolData θ T b (fun _ => H) (fun _ _ => 0) μ Kl B K M CV)
    (hΨ : Sb1Tilt θ T b w Ψ Wψ CΨ Bw Kw CS) (hv : 0 < v) (hθ : 0 < θ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ x, p4m_Phi v θ μ (fun s y => H y + Ψ s y) t x ≤
      (∫ x, p4m_Phi v θ μ (fun s y => H y + Ψ s y) 0 x) +
      (∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x * sb1S θ b w Wψ s x) +
      t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ)) := by
  have hle : ∀ n : ℕ, ∫ x, p4m_chi ((n : ℝ) + 1) x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) t x ≤
      (∫ x, p4m_chi ((n : ℝ) + 1) x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) 0 x) +
      (∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_chi ((n : ℝ) + 1) x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) +
      t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ)) -
      (∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x *
        (w s x k.1 k.2 * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k))) -
      ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x *
        fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
          (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x) := fun n =>
    sb1_time_ineq hP hv hθ hΨ.Ψc hΨ.Ψgrad hΨ.wc hΨ.w1 hΨ.dwc hΨ.Wc hΨ.Wd
      (p4m_contDiff_chi (R := (n : ℝ) + 1)) (p4m_hasCompactSupport_chi (R := (n : ℝ) + 1) (by positivity))
      (p4m_chi_nonneg _) (p4m_chi_le_one _) ht
  have h2 : Tendsto (fun n : ℕ => ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x *
      (w s x k.1 k.2 * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k))) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin N × Fin d))
      (fun k _ => sb1_tendsto_wcut hP hΨ hv ht k)
    simpa using this
  have hR : Tendsto (fun n : ℕ =>
      (∫ x, p4m_chi ((n : ℝ) + 1) x * p4m_Phi v θ μ (fun s y => H y + Ψ s y) 0 x) +
      (∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_chi ((n : ℝ) + 1) x * (p4Mol v (μ s) x * sb1S θ b w Wψ s x)) +
      t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ)) -
      (∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x *
        (w s x k.1 k.2 * fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k))) -
      ∑ k : Fin N × Fin d, ∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4m_Lam v θ (μ s) (fun y => H y + Ψ s y) x *
        fderiv ℝ (p4m_chi ((n : ℝ) + 1)) x (configBasis d N k) *
          (θ * p4m_gu v (μ s) k x - p4m_B v (μ s) (b s) k x)) atTop
      (𝓝 ((∫ x, p4m_Phi v θ μ (fun s y => H y + Ψ s y) 0 x) +
        (∫ s in Set.Icc (0 : ℝ) t, ∫ x, p4Mol v (μ s) x * sb1S θ b w Wψ s x) +
        t * (N * (Kl : ℝ) ^ 2 * (((N * d : ℕ) : ℝ) * v) / (4 * θ)) - 0 - 0)) :=
    ((((sb1_tendsto_free_t hP hΨ hv hθ 0).add (sb1_tendsto_src hP hΨ hv ht)).add tendsto_const_nhds).sub
      h2).sub (sb1_tendsto_flux hP hΨ hv hθ ht)
  have := le_of_tendsto_of_tendsto' (sb1_tendsto_free_t hP hΨ hv hθ t) hR hle
  linarith

end

end HRS.MS.MfeConf
