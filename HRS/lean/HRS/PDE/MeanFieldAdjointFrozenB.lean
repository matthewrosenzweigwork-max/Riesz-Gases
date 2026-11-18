import HRS.PDE.MeanFieldAdjointFrozen

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFAdjoint

variable {d : ℕ}

section Bform

/-- The Dirichlet form `B_ρ(u,v) = ∫ ρ ∇u·∇v`. -/
def Bform (ρ u v : Torus d → ℝ) : ℝ := ∫ x, ρ x * inner ℝ (Torus.grad u x) (Torus.grad v x)

theorem Bform_eq (ρ u v : Torus d → ℝ) :
    Bform ρ u v = ∫ x, ρ x * ∑ j, Torus.partialDeriv j u x * Torus.partialDeriv j v x := by
  unfold Bform
  simp_rw [MFApriori.inner_grad_grad]

theorem Bform_comm (ρ u v : Torus d → ℝ) : Bform ρ u v = Bform ρ v u := by
  rw [Bform_eq, Bform_eq]
  simp_rw [mul_comm (Torus.partialDeriv _ u _)]

theorem partialDeriv_sub' (j : Fin d) {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.partialDeriv j (fun y => f y - g y) x =
      Torus.partialDeriv j f x - Torus.partialDeriv j g x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => f y - g y) = fun y => Torus.lift f y - Torus.lift g y := rfl
  rw [e, fderiv_fun_sub ((hf.differentiable one_ne_zero) _) ((hg.differentiable one_ne_zero) _)]
  rfl

variable {ρ : Torus d → ℝ}

theorem Bform_sub_left (hρ : Continuous ρ) {u u' v : Torus d → ℝ} (hu : Torus.IsCk 1 u)
    (hu' : Torus.IsCk 1 u') (hv : Torus.IsCk 1 v) :
    Bform ρ (fun x => u x - u' x) v = Bform ρ u v - Bform ρ u' v := by
  rw [Bform_eq, Bform_eq, Bform_eq, ← integral_sub]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [partialDeriv_sub' _ hu hu']
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · exact integrable_of_cont (hρ.mul (continuous_finsetSum _ fun j _ =>
      (continuous_partialDeriv j _ hu).mul (continuous_partialDeriv j _ hv)))
  · exact integrable_of_cont (hρ.mul (continuous_finsetSum _ fun j _ =>
      (continuous_partialDeriv j _ hu').mul (continuous_partialDeriv j _ hv)))

theorem Bform_smul_left (r : ℝ) {u v : Torus d → ℝ} (hu : Torus.IsCk 1 u) :
    Bform ρ (fun x => r * u x) v = r * Bform ρ u v := by
  rw [Bform_eq, Bform_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [MFApriori.partialDeriv_const_mul_of_isCk1 _ hu]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Bform_add_left (hρ : Continuous ρ) {u u' v : Torus d → ℝ} (hu : Torus.IsCk 1 u)
    (hu' : Torus.IsCk 1 u') (hv : Torus.IsCk 1 v) :
    Bform ρ (fun x => u x + u' x) v = Bform ρ u v + Bform ρ u' v := by
  have : (fun x => u x + u' x) = fun x => u x - (-1 : ℝ) * u' x := by funext x; ring
  rw [this, Bform_sub_left hρ hu (by exact (contDiff_const.mul hu')) hv,
    Bform_smul_left _ hu']
  ring

/-- `|B(u,v)| ≤ ‖u‖_{C¹}‖v‖_{C¹}`. -/
theorem abs_Bform_le (hρ : IsProbDensity ρ) (hρc : Continuous ρ) {u v : Torus d → ℝ}
    (hu : Torus.IsCk 1 u) (hv : Torus.IsCk 1 v) :
    |Bform ρ u v| ≤ Torus.cbNorm 1 u * Torus.cbNorm 1 v := by
  unfold Bform
  have hg : Integrable (fun x => ρ x * (Torus.cbNorm 1 u * Torus.cbNorm 1 v)) :=
    integrable_of_cont (hρc.mul continuous_const)
  have := norm_integral_le_of_norm_le hg (f := fun x => ρ x * inner ℝ (Torus.grad u x) (Torus.grad v x))
    (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg x)]
      refine mul_le_mul_of_nonneg_left ?_ (hρ.nonneg x)
      refine (norm_inner_le_norm _ _).trans ?_
      exact mul_le_mul (MFApriori.norm_grad_le_cbNorm hu x) (MFApriori.norm_grad_le_cbNorm hv x)
        (norm_nonneg _) (by
          refine le_trans (norm_nonneg _) (MFApriori.norm_grad_le_cbNorm hu x)))
  rw [integral_mul_const, hρ.integral_one, one_mul] at this
  simpa [Real.norm_eq_abs] using this

end Bform

section EnergyDeriv

theorem toFun_real_smul (r : ℝ) (a : Coeff d) (x : Torus d) :
    toFun (fun k => ((r : ℝ) : ℂ) * a k) x = r * toFun a x := by
  unfold toFun series
  have : (∑' k, (((r : ℝ) : ℂ) * a k) * Torus.mode k x) =
      ((r : ℝ) : ℂ) * ∑' k, a k * Torus.mode k x := by
    rw [← tsum_mul_left]
    congr 1
    funext k
    ring
  rw [this, Complex.re_ofReal_mul]

theorem isRealCoeff_quot {a b e : Coeff d} (ha : IsRealCoeff a) (hb : IsRealCoeff b)
    (he : IsRealCoeff e) (h : ℝ) :
    IsRealCoeff (fun k => (a k - b k) / ((h : ℝ) : ℂ) - e k) := by
  intro k
  simp only [ha k, hb k, he k, map_sub, map_div₀, Complex.conj_ofReal]

/-- Differentiability of the Dirichlet energy along an `H^{m''}`-differentiable path. -/
theorem hasDerivWithinAt_energy {ρ : Torus d → ℝ} (hprob : IsProbDensity ρ) (hρc : Continuous ρ)
    {m'' : ℝ} (hm'' : (d : ℝ) / 2 + 1 < m'') {T : ℝ}
    (c e : ℝ → Coeff d)
    (hreal : ∀ σ ∈ Set.Icc 0 T, IsRealCoeff (c σ)) (hmem : ∀ σ ∈ Set.Icc 0 T, MemHs m'' (c σ))
    (hereal : ∀ σ ∈ Set.Icc 0 T, IsRealCoeff (e σ)) (hemem : ∀ σ ∈ Set.Icc 0 T, MemHs m'' (e σ))
    (hder : ∀ σ ∈ Set.Icc 0 T, Tendsto (fun σ' => hsNorm m'' (fun k =>
        (c σ' k - c σ k) / ((σ' - σ : ℝ) : ℂ) - e σ k)) (𝓝[Set.Icc 0 T \ {σ}] σ) (𝓝 0)) :
    ∀ σ ∈ Set.Icc 0 T, HasDerivWithinAt (fun σ => Bform ρ (toFun (c σ)) (toFun (c σ)))
      (2 * Bform ρ (toFun (c σ)) (toFun (e σ))) (Set.Icc 0 T) σ := by
  intro σ hσ
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) 1 m'' (by exact_mod_cast hm'')
  have hd2 : (d : ℝ) / 2 < m'' := by linarith
  have hWS : ∀ a : Coeff d, MemHs m'' a → ClassicalPart.WS 0 a := fun a ha =>
    ClassicalPart.ws0_of_memHs hd2 ha
  have hB : ∀ a b : Coeff d, IsRealCoeff a → MemHs m'' a → IsRealCoeff b → MemHs m'' b →
      |Bform ρ (toFun a) (toFun b)| ≤ C ^ 2 * (hsNorm m'' a * hsNorm m'' b) := by
    intro a b ha1 ha2 hb1 hb2
    obtain ⟨hA1, hA2⟩ := hC a ha2 ha1
    obtain ⟨hB1, hB2⟩ := hC b hb2 hb1
    refine (abs_Bform_le hprob hρc hA1 hB1).trans ?_
    have n1 : 0 ≤ Torus.cbNorm 1 (toFun a) := ClassicalPart.cbNorm_nonneg'' 1 _
    have n2 : 0 ≤ Torus.cbNorm 1 (toFun b) := ClassicalPart.cbNorm_nonneg'' 1 _
    calc Torus.cbNorm 1 (toFun a) * Torus.cbNorm 1 (toFun b)
        ≤ (C * hsNorm m'' a) * (C * hsNorm m'' b) := mul_le_mul hA2 hB2 n2 (n1.trans hA2)
      _ = C ^ 2 * (hsNorm m'' a * hsNorm m'' b) := by ring
  have hCk : ∀ a : Coeff d, IsRealCoeff a → MemHs m'' a → Torus.IsCk 1 (toFun a) :=
    fun a ha hm => (hC a hm ha).1
  have hcσ := hreal σ hσ
  have hmσ := hmem σ hσ
  have heσ := hereal σ hσ
  have hemσ := hemem σ hσ
  set Hc := hsNorm m'' (c σ) with hHc
  set He := hsNorm m'' (e σ) with hHe
  rw [hasDerivWithinAt_iff_tendsto_slope]
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  have hN := hder σ hσ
  have hh : Tendsto (fun σ' : ℝ => |σ' - σ|) (𝓝[Set.Icc 0 T \ {σ}] σ) (𝓝 0) := by
    have : Tendsto (fun σ' : ℝ => |σ' - σ|) (𝓝 σ) (𝓝 |σ - σ|) :=
      ((continuous_id.sub continuous_const).abs.tendsto σ)
    simpa using this.mono_left nhdsWithin_le_nhds
  set N : ℝ → ℝ := fun σ' => hsNorm m'' (fun k => (c σ' k - c σ k) / ((σ' - σ : ℝ) : ℂ) - e σ k)
    with hNdef
  have hbound : Tendsto (fun σ' : ℝ => C ^ 2 * (N σ' * (Hc + |σ' - σ| * (N σ' + He)) + N σ' * Hc +
      He * (|σ' - σ| * (N σ' + He)))) (𝓝[Set.Icc 0 T \ {σ}] σ) (𝓝 0) := by
    have hA : Tendsto (fun σ' : ℝ => N σ' + He) (𝓝[Set.Icc 0 T \ {σ}] σ) (𝓝 (0 + He)) :=
      hN.add (tendsto_const_nhds (x := He))
    have hAA : Tendsto (fun σ' : ℝ => |σ' - σ| * (N σ' + He)) (𝓝[Set.Icc 0 T \ {σ}] σ)
        (𝓝 (0 * (0 + He))) := hh.mul hA
    have h1 : Tendsto (fun σ' : ℝ => N σ' * (Hc + |σ' - σ| * (N σ' + He)))
        (𝓝[Set.Icc 0 T \ {σ}] σ) (𝓝 (0 * (Hc + 0 * (0 + He)))) :=
      hN.mul ((tendsto_const_nhds (x := Hc)).add hAA)
    have h2 : Tendsto (fun σ' : ℝ => N σ' * Hc) (𝓝[Set.Icc 0 T \ {σ}] σ) (𝓝 (0 * Hc)) :=
      hN.mul (tendsto_const_nhds (x := Hc))
    have h3 : Tendsto (fun σ' : ℝ => He * (|σ' - σ| * (N σ' + He))) (𝓝[Set.Icc 0 T \ {σ}] σ)
        (𝓝 (He * (0 * (0 + He)))) := (tendsto_const_nhds (x := He)).mul hAA
    have := ((h1.add h2).add h3).const_mul (C ^ 2)
    simpa using this
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
  filter_upwards [self_mem_nhdsWithin] with σ' hσ'
  obtain ⟨hσ'I, hσ'ne⟩ := hσ'
  have hne : σ' - σ ≠ 0 := sub_ne_zero.2 hσ'ne
  have hcσ' := hreal σ' hσ'I
  have hmσ' := hmem σ' hσ'I
  set h : ℝ := σ' - σ with hhdef
  -- the coefficients
  set Dc : Coeff d := fun k => c σ' k - c σ k with hDc
  set Qc : Coeff d := fun k => (c σ' k - c σ k) / ((h : ℝ) : ℂ) - e σ k with hQc
  have hDreal : IsRealCoeff Dc := ClassicalPart.isRealCoeff_sub hcσ' hcσ
  have hDmem : MemHs m'' Dc := memHs_sub hmσ' hmσ
  have hQreal : IsRealCoeff Qc := isRealCoeff_quot hcσ' hcσ heσ h
  have hhC : ((h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hne
  have hQeq : Qc = (fun k => (((1 / h : ℝ)) : ℂ) * Dc k) - e σ := by
    funext k
    simp only [hQc, hDc, Pi.sub_apply]
    push_cast
    field_simp
  have hAmem : MemHs m'' (fun k => (((1 / h : ℝ)) : ℂ) * Dc k) := MFThermalReg.memHs_smul hDmem _
  have hQmem : MemHs m'' Qc := by rw [hQeq]; exact memHs_sub hAmem hemσ
  have hAWS := hWS _ hAmem
  have hDWS := hWS _ hDmem
  have hEWS := hWS _ hemσ
  have hcWS' := hWS _ hmσ'
  have hcWS := hWS _ hmσ
  -- function-level identities
  have hDfun : toFun Dc = fun x => toFun (c σ') x - toFun (c σ) x := by
    funext x
    exact ClassicalPart.toFun_sub hcWS' hcWS x
  have hqfun : toFun Qc = fun x => (1 / h) * (toFun (c σ') x - toFun (c σ) x) - toFun (e σ) x := by
    funext x
    rw [hQeq, ClassicalPart.toFun_sub hAWS hEWS, toFun_real_smul, ← congrFun hDfun x]
  set u' := toFun (c σ') with hu'
  set u := toFun (c σ) with hu
  set w := toFun (e σ) with hw
  set q := toFun Qc with hq
  have hu'C : Torus.IsCk 1 u' := hCk _ hcσ' hmσ'
  have huC : Torus.IsCk 1 u := hCk _ hcσ hmσ
  have hwC : Torus.IsCk 1 w := hCk _ heσ hemσ
  have hqC : Torus.IsCk 1 q := hCk _ hQreal hQmem
  have hΔC : Torus.IsCk 1 (fun x => u' x - u x) := hu'C.sub huC
  -- bilinear identities
  have e1 := Bform_sub_left hρc hu'C huC hu'C
  have e2 := Bform_sub_left hρc hu'C huC huC
  have c1 := Bform_comm ρ u u'
  have c2 := Bform_comm ρ u w
  have e3 : ∀ z : Torus d → ℝ, Torus.IsCk 1 z →
      Bform ρ q z + Bform ρ w z = (1 / h) * Bform ρ (fun x => u' x - u x) z := by
    intro z hz
    rw [← Bform_add_left hρc hqC hwC hz, ← Bform_smul_left (1 / h) hΔC]
    congr 1
    funext x
    rw [hqfun]
    simp only
    ring
  have e4 := Bform_sub_left hρc hu'C huC hwC
  have c3 := Bform_comm ρ (fun x => u' x - u x) w
  have e5 := e3 u' hu'C
  have e6 := e3 u huC
  have key : (σ' - σ)⁻¹ * (Bform ρ u' u' - Bform ρ u u) - 2 * Bform ρ u w =
      Bform ρ q u' + Bform ρ q u + Bform ρ w (fun x => u' x - u x) := by
    have k1 : (σ' - σ)⁻¹ * (Bform ρ u' u' - Bform ρ u u) =
        (1 / h) * Bform ρ (fun x => u' x - u x) u' + (1 / h) * Bform ρ (fun x => u' x - u x) u := by
      rw [← mul_add, one_div]
      congr 1
      have := Bform_comm ρ u' u
      linarith
    have c4 := Bform_comm ρ w u'
    have c5 := Bform_comm ρ w u
    have c6 := Bform_comm ρ w (fun x => u' x - u x)
    rw [k1]
    linarith
  -- norms
  have hNn : 0 ≤ N σ' := Real.sqrt_nonneg _
  have hHe0 : 0 ≤ He := Real.sqrt_nonneg _
  have hDn : hsNorm m'' Dc ≤ |h| * (N σ' + He) := by
    have hDeq : Dc = fun k => ((h : ℝ) : ℂ) * (Qc k + e σ k) := by
      funext k
      simp only [hQc, hDc]
      field_simp
      ring
    rw [hDeq, MFLocal.hsNorm_smul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact MFThermalReg.hsNorm_add_le m'' hQmem hemσ
  have hcn : hsNorm m'' (c σ') ≤ Hc + hsNorm m'' Dc := by
    have : c σ' = fun k => c σ k + Dc k := by funext k; simp [hDc]
    rw [this]
    exact MFThermalReg.hsNorm_add_le m'' hmσ hDmem
  have hb1 := hB Qc (c σ') hQreal hQmem hcσ' hmσ'
  have hb2 := hB Qc (c σ) hQreal hQmem hcσ hmσ
  have hb3 := hB (e σ) Dc heσ hemσ hDreal hDmem
  have hΔeq : (fun x => u' x - u x) = toFun Dc := hDfun.symm
  have hC0 : 0 ≤ C ^ 2 := sq_nonneg C
  have hDnn : 0 ≤ hsNorm m'' Dc := Real.sqrt_nonneg _
  have hcnn : 0 ≤ hsNorm m'' (c σ') := Real.sqrt_nonneg _
  have hHc0 : 0 ≤ Hc := Real.sqrt_nonneg _
  have hslope : slope (fun σ => Bform ρ (toFun (c σ)) (toFun (c σ))) σ σ' =
      (σ' - σ)⁻¹ * (Bform ρ u' u' - Bform ρ u u) := by
    rw [slope_def_field, div_eq_inv_mul]
  rw [hslope, key, Real.norm_eq_abs]
  rw [hΔeq] at *
  calc |Bform ρ q u' + Bform ρ q u + Bform ρ w (toFun Dc)|
      ≤ |Bform ρ q u'| + |Bform ρ q u| + |Bform ρ w (toFun Dc)| := by
        refine (abs_add_le _ _).trans ?_
        exact add_le_add (abs_add_le _ _) le_rfl
    _ ≤ C ^ 2 * (N σ' * hsNorm m'' (c σ')) + C ^ 2 * (N σ' * Hc) + C ^ 2 * (He * hsNorm m'' Dc) :=
        add_le_add (add_le_add hb1 hb2) hb3
    _ ≤ C ^ 2 * (N σ' * (Hc + |h| * (N σ' + He)) + N σ' * Hc + He * (|h| * (N σ' + He))) := by
        have i1 : N σ' * hsNorm m'' (c σ') ≤ N σ' * (Hc + |h| * (N σ' + He)) :=
          mul_le_mul_of_nonneg_left (hcn.trans (by linarith)) hNn
        have i2 : He * hsNorm m'' Dc ≤ He * (|h| * (N σ' + He)) :=
          mul_le_mul_of_nonneg_left hDn hHe0
        nlinarith [mul_le_mul_of_nonneg_left i1 hC0, mul_le_mul_of_nonneg_left i2 hC0]

end EnergyDeriv

section Dissipation

variable {ρ : Torus d → ℝ}

theorem continuous_lop (hρ : IsProbDensity ρ) (hρ1 : Torus.IsCk 1 ρ) (hpos : ∀ x, 0 < ρ x)
    {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) : Continuous (Lop ρ f) := by
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  have : Lop ρ f = fun x => -(ρ x)⁻¹ *
      ∑ j, Torus.partialDeriv j (fun y => ρ y * Torus.partialDeriv j f y) x := by
    funext x
    unfold Lop
    rw [MFAux.div_smul_grad ρ f hρ1 hf x]
  rw [this]
  exact ((hρc.inv₀ fun x => (hpos x).ne').neg).mul (continuous_finsetSum _ fun j _ =>
    continuous_partialDeriv j _ (MFAux.isCk_mul_partialDeriv ρ f hρ1 hf j))

theorem l2Inner_projMean_right (hρ : IsProbDensity ρ) (hρc : Continuous ρ) {v w : Torus d → ℝ}
    (hv : Continuous v) (hw : Continuous w) (hv0 : pair (withDensityReal ρ) v = 0) :
    l2Inner (withDensityReal ρ) v (projMean (withDensityReal ρ) w) =
      l2Inner (withDensityReal ρ) v w := by
  rw [l2Inner_mu hρ, l2Inner_mu hρ]
  rw [pair_mu hρ] at hv0
  have e : ∀ x, ρ x * (v x * projMean (withDensityReal ρ) w x) =
      ρ x * (v x * w x) - pair (withDensityReal ρ) w * (ρ x * v x) := fun x => by
    unfold projMean; ring
  simp_rw [e]
  have i1 : Integrable (fun x => ρ x * (v x * w x)) := integrable_of_cont (hρc.mul (hv.mul hw))
  have i2 : Integrable (fun x => pair (withDensityReal ρ) w * (ρ x * v x)) :=
    (integrable_of_cont (hρc.mul hv)).const_mul _
  rw [integral_sub i1 i2, integral_const_mul, hv0, mul_zero, sub_zero]

theorem pair_lop (hρ : IsProbDensity ρ) (hρ1 : Torus.IsCk 1 ρ) {f : Torus d → ℝ}
    (hf : Torus.IsCk 2 f) : pair (withDensityReal ρ) (Lop ρ f) = 0 := by
  have h := l2Inner_lop_eq ρ hρ hρ1 f (fun _ => 1) hf contDiff_const
  unfold pair
  have h1 : ∫ x, Lop ρ f x ∂(withDensityReal ρ) = l2Inner (withDensityReal ρ) (Lop ρ f) (fun _ => 1) := by
    unfold l2Inner; simp
  rw [h1, h]
  have : ∀ x, ρ x * inner ℝ (Torus.grad f x) (Torus.grad (fun _ : Torus d => (1 : ℝ)) x) = 0 := by
    intro x
    have : Torus.grad (fun _ : Torus d => (1 : ℝ)) x = 0 := by
      ext j
      rw [MFAux.grad_apply, MFAux.partialDeriv_const]
      rfl
    rw [this]; simp
  simp [this]

theorem l2Inner_young (hρ : IsProbDensity ρ) (hρc : Continuous ρ) {v f : Torus d → ℝ}
    (hv : Continuous v) (hf : Continuous f) (a : ℝ) :
    2 * a * l2Inner (withDensityReal ρ) v f ≤
      l2Inner (withDensityReal ρ) v v + a ^ 2 * l2Inner (withDensityReal ρ) f f := by
  rw [l2Inner_mu hρ, l2Inner_mu hρ, l2Inner_mu hρ]
  have i1 : Integrable (fun x => ρ x * (v x * v x)) := integrable_of_cont (hρc.mul (hv.mul hv))
  have i2 : Integrable (fun x => ρ x * (f x * f x)) := integrable_of_cont (hρc.mul (hf.mul hf))
  have i3 : Integrable (fun x => ρ x * (v x * f x)) := integrable_of_cont (hρc.mul (hv.mul hf))
  have lhs : 2 * a * ∫ x, ρ x * (v x * f x) = ∫ x, (2 * a) * (ρ x * (v x * f x)) :=
    (integral_const_mul _ _).symm
  have rhs : a ^ 2 * ∫ x, ρ x * (f x * f x) = ∫ x, a ^ 2 * (ρ x * (f x * f x)) :=
    (integral_const_mul _ _).symm
  rw [lhs, rhs, ← integral_add i1 (i2.const_mul _)]
  refine integral_mono (i3.const_mul _) (i1.add (i2.const_mul _)) fun x => ?_
  have h0 := hρ.nonneg x
  have := mul_nonneg h0 (sq_nonneg (v x - a * f x))
  nlinarith [this]

/-- The dissipation inequality `⟨∇g,∇w⟩_ρ ≤ -ν cP ⟨∇g,∇g⟩_ρ` when `Q w = -A L g`. -/
theorem energy_dissipation (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hρ : IsProbDensity ρ) (hρ1 : Torus.IsCk 1 ρ) {c₀ cP ν : ℝ} (hlow : ∀ x, c₀ ≤ ρ x)
    (hc₀ : 0 < c₀) (hcP : 0 < cP) (hν : 0 < ν)
    (hP : ∀ f : Torus d → ℝ, Torus.IsCk 1 f → pair (withDensityReal ρ) f = 0 →
      cP * l2Inner (withDensityReal ρ) f f ≤ ∫ x, ρ x * ‖Torus.grad f x‖ ^ 2)
    {g w : Torus d → ℝ} (hg : Torus.IsCk 2 g) (hw : Torus.IsCk 1 w)
    (hproj : projMean (withDensityReal ρ) w = equilibriumGen d s ρ ν g) :
    Bform ρ g w ≤ -(ν * cP) * Bform ρ g g := by
  have hρc : Continuous ρ := MFAux.continuous_of_isCk hρ1
  have hpos : ∀ x, 0 < ρ x := fun x => lt_of_lt_of_le hc₀ (hlow x)
  have := MFSemigroup.isProb_withDensityReal hρ
  set μ := withDensityReal ρ with hμ
  set v := Lop ρ g with hv
  have hvc : Continuous v := continuous_lop hρ hρ1 hpos hg
  have hv0 : pair μ v = 0 := pair_lop hρ hρ1 hg
  have hwc : Continuous w := MFAux.continuous_of_isCk hw
  have hg1 : Torus.IsCk 1 g := hg.of_le (by norm_num)
  have hgc : Continuous g := MFAux.continuous_of_isCk hg1
  have hKc : Continuous (Kop (periodicRiesz d s) μ v) := by
    rw [kop_eq s hρ v]
    exact (continuous_conv_kernel hd s hs0 hsd (hρc.mul hvc)).sub continuous_const
  have stepA : Bform ρ g w = l2Inner μ v w := (l2Inner_lop_eq ρ hρ hρ1 g w hg hw).symm
  have stepB : l2Inner μ v w = l2Inner μ v (projMean μ w) :=
    (l2Inner_projMean_right hρ hρc hvc hwc hv0).symm
  have stepC : projMean μ w = fun x => -(ν * v x + Kop (periodicRiesz d s) μ v x) := by
    rw [hproj]; rfl
  have stepD : l2Inner μ v (projMean μ w) =
      -(ν * l2Inner μ v v) - l2Inner μ v (Kop (periodicRiesz d s) μ v) := by
    rw [stepC, l2Inner_mu hρ, l2Inner_mu hρ, l2Inner_mu hρ]
    have e : ∀ x, ρ x * (v x * -(ν * v x + Kop (periodicRiesz d s) μ v x)) =
        -(ν * (ρ x * (v x * v x))) - ρ x * (v x * Kop (periodicRiesz d s) μ v x) := fun x => by ring
    simp_rw [e]
    rw [integral_sub, integral_neg, integral_const_mul]
    · exact (integrable_of_cont (hρc.mul (hvc.mul hvc))).const_mul ν |>.neg
    · exact integrable_of_cont (hρc.mul (hvc.mul hKc))
  have stepE : 0 ≤ l2Inner μ v (Kop (periodicRiesz d s) μ v) := by
    rw [l2Inner_comm']
    exact l2Inner_kop_nonneg' hd s hs0 hsd ρ hρ hρc v hvc hv0
  -- the Poincaré step
  set f := projMean μ g with hf
  have hf1 : Torus.IsCk 1 f := by
    have : Torus.IsCk 1 (fun x => g x - pair μ g) := hg1.sub contDiff_const
    exact this
  have hfc : Continuous f := MFAux.continuous_of_isCk hf1
  have hf0 : pair μ f = 0 := MFSemigroup.pair_projMean μ g
  have hgradf : Torus.grad f = Torus.grad g := MFSemigroup.grad_projMean μ g
  have hE : Bform ρ g g = ∫ x, ρ x * ‖Torus.grad f x‖ ^ 2 := by
    unfold Bform
    rw [hgradf]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [real_inner_self_eq_norm_sq]
  have hPf := hP f hf1 hf0
  rw [← hE] at hPf
  have hEv : Bform ρ g g = l2Inner μ v f := by
    have h1 : Bform ρ g g = l2Inner μ v g := (l2Inner_lop_eq ρ hρ hρ1 g g hg hg1).symm
    rw [h1]
    exact (l2Inner_projMean_right hρ hρc hvc hgc hv0).symm
  have hY := l2Inner_young hρ hρc hvc hfc cP
  have hkey : cP * Bform ρ g g ≤ l2Inner μ v v := by
    rw [hEv] at hPf ⊢
    nlinarith [hY, hPf, hcP]
  rw [stepA, stepB, stepD]
  nlinarith [stepE, hkey, hν]

end Dissipation

section Flow

/-- The frozen coefficient satisfies the hypotheses of Proposition 3.9 at level `mStar d + 2`,
with constants depending only on `Λ₀` (and the regime). -/
theorem adjointData_frozen_ck {s : ℝ} {νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (mStar d + 5) νm νp c₀ Λ₀ β V ρβ) :
    ∃ R : Regime, ∀ ν₀ T : ℝ, 0 < T →
      AdjointData s (mStar d + 2) R 1 Λ₀ Λ₀ (mfData d s H.hs0 H.hsd V β H.hβ) ν₀ T (fun _ => ρβ) := by
  have hM : MatBound 1 (-1 : Matrix (Fin d) (Fin d) ℝ) := by
    intro i j
    by_cases h : i = j <;> simp [h]
  have hsym : Torus.SymNonpos (-1 : Matrix (Fin d) (Fin d) ℝ) := by
    unfold Torus.SymNonpos Torus.symPart
    simp only [Matrix.transpose_neg, Matrix.transpose_one]
    have : (-((1 / 2 : ℝ) • ((-1 : Matrix (Fin d) (Fin d) ℝ) + -1))) = 1 := by
      rw [← two_smul ℝ (-1 : Matrix (Fin d) (Fin d) ℝ), smul_smul]
      norm_num
    rw [this]
    exact Matrix.PosSemidef.one
  have common : ∀ (R : Regime) (ν₀ T : ℝ), 0 < T →
      R.Holds d s (-1 : Matrix (Fin d) (Fin d) ℝ) β⁻¹ ν₀ T (fun _ => ρβ) →
      AdjointData s (mStar d + 2) R 1 Λ₀ Λ₀ (mfData d s H.hs0 H.hsd V β H.hβ) ν₀ T (fun _ => ρβ) :=
    fun R ν₀ T hT hR =>
    ⟨rfl, hM, ⟨H.hV, H.hVb⟩, ⟨fun r _ => H.thermal.1, fun r _ => H.hρC, fun r _ => H.hρb,
      fun ψ _ => continuousOn_const⟩, hT, hR⟩
  by_cases hs : s ≤ (d : ℝ) - 2
  · exact ⟨.R1, fun ν₀ T hT => common _ ν₀ T hT hs⟩
  · exact ⟨.R2b c₀, fun ν₀ T hT => common _ ν₀ T hT ⟨by linarith, hsym, H.hc₀,
      fun r _ x => H.hlow x⟩⟩

theorem mStar_gt (d : ℕ) : (d : ℝ) / 2 + 2 < (mStar d : ℝ) := by
  unfold mStar
  push_cast
  have := Nat.lt_floor_add_one ((d : ℝ) / 2)
  linarith

theorem isCk_two_of_memSobolev {ψ : Torus d → ℝ} (hψc : Continuous ψ)
    (hψ : MemSobolev ((mStar d : ℝ) + 2) ψ) : Torus.IsCk 2 ψ := by
  have hcm := (hsNormSq_coeffOf _ ψ hψ).1
  have hdm : (d : ℝ) / 2 < (mStar d : ℝ) + 2 := by linarith [mStar_gt d]
  have hs := summable_norm_of_memHs _ hdm _ hcm
  have hre : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf ψ (integrable_of_cont hψc)
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) 2 ((mStar d : ℝ) + 2) (by linarith [mStar_gt d])
  have := (hC _ hcm hre).1
  rwa [MFThermalReg.toFun_coeffOf hψc hs] at this

/-- The energy `∫ρβ|∇S(τ)ψ|²` of the frozen flow decays exponentially. -/
theorem frozen_energy_decay (hd : 1 ≤ d) {s νm νp c₀ Λ₀ β : ℝ} {V ρβ : Torus d → ℝ}
    (H : FrozenHyp d s (mStar d + 5) νm νp c₀ Λ₀ β V ρβ) {cP : ℝ} (hcP : 0 < cP)
    (hP : ∀ f : Torus d → ℝ, Torus.IsCk 1 f → pair (withDensityReal ρβ) f = 0 →
      cP * l2Inner (withDensityReal ρβ) f f ≤ ∫ x, ρβ x * ‖Torus.grad f x‖ ^ 2)
    {ψ : Torus d → ℝ} (hψc : Continuous ψ) (hψ : MemSobolev ((mStar d : ℝ) + 2) ψ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    Torus.IsCk 2 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ∧
    pair (withDensityReal ρβ) (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) = 0 ∧
    Bform ρβ (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ)
        (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
      Real.exp (-(2 * (β⁻¹ * cP)) * τ) * Bform ρβ ψ ψ := by
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρc : Continuous ρβ := MFAux.continuous_of_isCk (H.hρC.of_le (by exact_mod_cast (by omega : 1 ≤ mStar d + 5)))
  have hν : 0 < β⁻¹ := inv_pos.2 H.hβ
  have hpos : ∀ x, 0 < ρβ x := fun x => lt_of_lt_of_le H.hc₀ (H.hlow x)
  set m : ℕ := mStar d + 2 with hm
  have hmR : (m : ℝ) = (mStar d : ℝ) + 2 := by rw [hm]; push_cast; ring
  have hmst : mStar d ≤ m := by omega
  have hm1 : 1 ≤ m := by have := ClassicalPart.three_le_mStar d; omega
  have hmd : (d : ℝ) / 2 < m := by rw [hmR]; linarith [mStar_gt d]
  obtain ⟨R, hA⟩ := adjointData_frozen_ck H
  set T : ℝ := τ + 1 with hTdef
  have hT : 0 < T := by rw [hTdef]; linarith
  have hAT := hA 0 T hT
  have hψ' : MemSobolev (m : ℝ) ψ := by rw [hmR]; exact hψ
  have hψ2 : Torus.IsCk 2 ψ := isCk_two_of_memSobolev hψc hψ
  obtain ⟨C, Cs, hC, hCs, hmain⟩ := adjoint_torus_classical hd s H.hs0 H.hsd m hmst R 1 Λ₀ Λ₀
  obtain ⟨hcls, hpe, -, -⟩ := hmain D 0 T (fun _ => ρβ) hAT T ⟨hT, le_rfl⟩ ψ hψc hψ'
  set c : ℝ → Coeff d := propagatorCoeff D (fun _ => ρβ) m T (coeffOf ψ) with hcdef
  have hcm : MemHs (m : ℝ) (coeffOf ψ) := (hsNormSq_coeffOf _ ψ hψ').1
  have hre : IsRealCoeff (coeffOf ψ) := isRealCoeff_coeffOf ψ (integrable_of_cont hψc)
  obtain ⟨C0, hC0, hspec⟩ := propagatorCoeff_spec hd s H.hs0 H.hsd m hm1 R 1 Λ₀ Λ₀
  obtain ⟨hsol, hw, -⟩ := hspec D 0 T (fun _ => ρβ) hAT T ⟨hT, le_rfl⟩ (coeffOf ψ) hcm
  have hreal := ClassicalPart.propagatorCoeff_real hd s H.hs0 H.hsd m hm1 R 1 Λ₀ Λ₀ D 0 T
    (fun _ => ρβ) hAT T ⟨hT, le_rfl⟩ (coeffOf ψ) hcm hre
  have hmemc : ∀ σ ∈ Set.Icc (0 : ℝ) T, MemHs (m : ℝ) (c σ) := hw.1
  -- time regularity
  obtain ⟨-, hdt⟩ := adjoint_torus_time_regularity hd s H.hs0 H.hsd m hm1 R 1 Λ₀ Λ₀ D 0 T
    (fun _ => ρβ) hAT T ⟨hT, le_rfl⟩ (coeffOf ψ) hcm
  have hm2 : (m : ℝ) - 2 = (mStar d : ℝ) := by rw [hmR]; ring
  rw [hm2] at hdt
  obtain ⟨m'', hm''1, hm''2⟩ := ClassicalPart.exists_mid (d := d) hmst
  have hcont : ContinuousInHs m'' c T := forward_strong_continuity (m : ℝ) T c hw m'' hm''2
  obtain ⟨hgws, -, -, -⟩ := ClassicalPart.gen_path_facts hAT hmd ⟨hT, le_rfl⟩ hsol hreal hm''1 hcont
  -- generator coefficients
  set e : ℝ → Coeff d := fun σ => forwardGen D ρβ (c σ) with hedef
  have hereal : ∀ σ ∈ Set.Icc (0 : ℝ) T, IsRealCoeff (e σ) := fun σ hσ => (hgws σ hσ).2
  have hewsz : ∀ σ ∈ Set.Icc (0 : ℝ) T, ClassicalPart.WS 0 (e σ) := fun σ hσ => (hgws σ hσ).1
  obtain ⟨K, hK0, hK⟩ := ET.forwardGen_hs_bound hd s H.hs0 H.hsd (mStar d) 1 Λ₀ Λ₀
  have hVH : VHyp (mStar d) Λ₀ D.V :=
    ⟨ET.isCk_mono' (a := mStar d + 3) (b := mStar d + 5) (by omega) H.hV,
      (ET.cbNorm_mono' (a := mStar d + 3) (b := mStar d + 5) (by omega) V).trans H.hVb⟩
  have hemem : ∀ σ ∈ Set.Icc (0 : ℝ) T, MemHs (mStar d : ℝ) (e σ) := by
    intro σ hσ
    have hu : MemHs (((mStar d : ℕ) : ℝ) + 2) (c σ) := by rw [← hmR]; exact hmemc σ hσ
    exact (hK D hAT.hs hAT.hM hVH ρβ hprob
      (ET.isCk_mono' (a := mStar d + 3) (b := mStar d + 5) (by omega) H.hρC)
      ((ET.cbNorm_mono' (a := mStar d + 3) (b := mStar d + 5) (by omega) ρβ).trans H.hρb)
      (c σ) hu).1
  have hmemc' : ∀ σ ∈ Set.Icc (0 : ℝ) T, MemHs (mStar d : ℝ) (c σ) := fun σ hσ =>
    (hmemc σ hσ).mono (by rw [← hm2]; linarith)
  have hEder := hasDerivWithinAt_energy hprob hρc (m'' := (mStar d : ℝ))
    (by linarith [mStar_gt d]) c e hreal hmemc' hereal hemem hdt
  -- regularity of the profile
  have hdm : (d : ℝ) / 2 < (m : ℝ) := hmd
  obtain ⟨C2, hC2⟩ := toFun_isCk_le (d := d) 2 (m : ℝ) (by rw [hmR]; linarith [mStar_gt d])
  obtain ⟨C1, hC1⟩ := toFun_isCk_le (d := d) 1 (mStar d : ℝ) (by linarith [mStar_gt d])
  have hKf := ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 D.V :=
    ET.isCk_mono' (a := 1) (b := mStar d + 5) (by omega) H.hV
  have hV2 : Torus.IsCk 2 D.V :=
    ET.isCk_mono' (a := 2) (b := mStar d + 5) (by omega) H.hV
  have hρ1 : Torus.IsCk 1 ρβ := ET.isCk_mono' (a := 1) (b := mStar d + 5) (by omega) H.hρC
  have hρ2 : Torus.IsCk 2 ρβ := ET.isCk_mono' (a := 2) (b := mStar d + 5) (by omega) H.hρC
  set a : ℝ := 2 * (β⁻¹ * cP) with hadef
  have ha0 : 0 ≤ a := by positivity
  have hdiss : ∀ σ ∈ Set.Icc (0 : ℝ) T,
      2 * Bform ρβ (toFun (c σ)) (toFun (e σ)) ≤ -a * Bform ρβ (toFun (c σ)) (toFun (c σ)) := by
    intro σ hσ
    have hg2 : Torus.IsCk 2 (toFun (c σ)) := (hC2 _ (hmemc σ hσ) (hreal σ hσ)).1
    have hw1 : Torus.IsCk 1 (toFun (e σ)) := (hC1 _ (hemem σ hσ) (hereal σ hσ)).1
    have hWSc : ClassicalPart.WS 0 (c σ) := ClassicalPart.ws0_of_memHs hmd (hmemc σ hσ)
    have hbg : backwardGenerator D ρβ (toFun (c σ)) = toFun (e σ) :=
      ClassicalPart.backwardGenerator_eq_toFun D hKf hV1 hρ1 (hreal σ hσ) hWSc hg2
        (hereal σ hσ) (hewsz σ hσ)
    have hproj : projMean (withDensityReal ρβ) (toFun (e σ)) =
        equilibriumGen d s ρβ β⁻¹ (toFun (c σ)) := by
      rw [← hbg]
      exact MFOneLe.operator_order_core_of_one_le hd D rfl β H.hβ rfl hV2 ρβ H.thermal hρ2 hpos _ hg2
    have := energy_dissipation hd s H.hs0 H.hsd hprob hρ1 H.hlow H.hc₀ hcP hν hP hg2 hw1 hproj
    rw [hadef]
    linarith
  -- the Lyapunov argument
  set E : ℝ → ℝ := fun σ => Bform ρβ (toFun (c σ)) (toFun (c σ)) with hEdef
  set G : ℝ → ℝ := fun σ => Real.exp (a * σ) * E σ with hGdef
  have hGder : ∀ σ ∈ Set.Icc (0 : ℝ) T, HasDerivWithinAt G
      (Real.exp (a * σ) * (a * E σ + 2 * Bform ρβ (toFun (c σ)) (toFun (e σ)))) (Set.Icc 0 T) σ := by
    intro σ hσ
    have h1 : HasDerivWithinAt (fun σ => Real.exp (a * σ)) (Real.exp (a * σ) * a) (Set.Icc 0 T) σ :=
      by simpa using (((hasDerivAt_id σ).const_mul a).exp).hasDerivWithinAt (s := Set.Icc 0 T)
    have h2 := h1.mul (hEder σ hσ)
    refine h2.congr_deriv ?_
    ring
  have hGnp : ∀ σ ∈ Set.Icc (0 : ℝ) T,
      Real.exp (a * σ) * (a * E σ + 2 * Bform ρβ (toFun (c σ)) (toFun (e σ))) ≤ 0 := by
    intro σ hσ
    have := hdiss σ hσ
    have h3 : a * E σ + 2 * Bform ρβ (toFun (c σ)) (toFun (e σ)) ≤ 0 := by
      simp only [hEdef]; linarith
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le h3
  have hanti : AntitoneOn G (Set.Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ?_ ?_ ?_
    · intro σ hσ; exact (hGder σ hσ).continuousWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      exact ((hGder σ (Set.Ioo_subset_Icc_self hσ)).hasDerivAt
        (Icc_mem_nhds hσ.1 hσ.2)).differentiableAt.differentiableWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      rw [((hGder σ (Set.Ioo_subset_Icc_self hσ)).hasDerivAt (Icc_mem_nhds hσ.1 hσ.2)).deriv]
      exact hGnp σ (Set.Ioo_subset_Icc_self hσ)
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ, by rw [hTdef]; linarith⟩
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hGτ : G τ ≤ G 0 := hanti h0T hτT hτ
  have hEτ : E τ ≤ Real.exp (-a * τ) * E 0 := by
    have : Real.exp (a * τ) * E τ ≤ Real.exp (a * 0) * E 0 := hGτ
    rw [mul_zero, Real.exp_zero, one_mul] at this
    have h5 : E τ = Real.exp (-a * τ) * (Real.exp (a * τ) * E τ) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [h5]
    exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le
  -- identification of the flow
  have hc0 : c 0 = coeffOf ψ := by
    funext k
    have := hsol.eq k 0 ⟨le_rfl, hT.le⟩
    simpa using this
  have hdmψ : (d : ℝ) / 2 < (m : ℝ) := hmd
  have hsumψ := summable_norm_of_memHs (m : ℝ) hdmψ _ hcm
  have htoψ : toFun (c 0) = ψ := by
    rw [hc0]; exact MFThermalReg.toFun_coeffOf hψc hsumψ
  have hμ1 : Torus.IsCk 1 ((fun _ : ℝ => ρβ) 0) := hρ1
  have hprop : propagator D (fun _ => ρβ) 0 τ ψ = toFun (c τ) := by
    rcases hτ.eq_or_lt with h0 | hpos'
    · subst h0
      rw [MFSemigroup.propagator_zero D hKf hV1 _ hμ1 hψ2, ← htoψ]
    · have := MFOneLe.propagator_frozen_eq_of_one_le hd s H.hs0 H.hsd m hm1 R 1 Λ₀ Λ₀ D 0 T ρβ hAT
        ⟨hT, le_rfl⟩ hcls ⟨hpos', by rw [hTdef]; linarith⟩
      rw [this]
      funext x
      simp only [sub_sub_cancel]
  have hS : equilibriumSemigroup D ρβ τ ψ = projMean (withDensityReal ρβ) (toFun (c τ)) := by
    unfold equilibriumSemigroup
    rw [hprop]
  have hgτ : Torus.IsCk 2 (toFun (c τ)) := (hC2 _ (hmemc τ hτT) (hreal τ hτT)).1
  have hgrad : Torus.grad (projMean (withDensityReal ρβ) (toFun (c τ))) = Torus.grad (toFun (c τ)) :=
    MFSemigroup.grad_projMean _ _
  have := MFSemigroup.isProb_withDensityReal hprob
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]
    have : Torus.IsCk 2 (fun x => toFun (c τ) x - pair (withDensityReal ρβ) (toFun (c τ))) :=
      hgτ.sub contDiff_const
    exact this
  · rw [hS]; exact MFSemigroup.pair_projMean _ _
  · rw [hS]
    have e1 : Bform ρβ (projMean (withDensityReal ρβ) (toFun (c τ)))
        (projMean (withDensityReal ρβ) (toFun (c τ))) = E τ := by
      simp only [hEdef, Bform, hgrad]
    have e0 : E 0 = Bform ρβ ψ ψ := by simp only [hEdef, htoψ]
    rw [e1, ← e0]
    have : -(2 * (β⁻¹ * cP)) * τ = -a * τ := by rw [hadef]
    rw [this]
    exact hEτ

theorem sobolevNorm_zero_eq {f : Torus d → ℝ} (hf : Continuous f) :
    sobolevNorm 0 f = Real.sqrt (∫ x, f x ^ 2) := by
  have hL2 : MemLp f 2 volume := hf.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hms : MemSobolev 0 f := memSobolev_of_memHs 0 f hL2 (MFApriori.memHs_zero_coeffOf_continuous hf)
  rw [ClassicalPart.sobolevNorm_eq_hsNorm hms]
  unfold hsNorm
  rw [MFApriori.parseval_real hf]

/-- `∫|∇u|² ≤ ‖u‖²_{H²}`. -/
theorem integral_norm_grad_sq_le {u : Torus d → ℝ} (hu : Torus.IsCk 2 u) :
    ∫ x, ‖Torus.grad u x‖ ^ 2 ≤ sobolevNorm 2 u ^ 2 := by
  have hu1 : Torus.IsCk 1 u := hu.of_le (by norm_num)
  have huc : Continuous u := MFAux.continuous_of_isCk hu1
  have hL2 : MemLp u 2 volume := huc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm2 : MemHs ((2 : ℕ) : ℝ) (coeffOf u) := MFSemigroup.memHs_nat_of_isCk 2 u hu
  have hm2' : MemHs 2 (coeffOf u) := by simpa using hm2
  have hS : MemSobolev 2 u := memSobolev_of_memHs 2 u hL2 hm2'
  rw [← (hsNormSq_coeffOf 2 u hS).2, ← MFApriori.grad_parseval hu1]
  have hterm : ∀ k : Lattice d, sobWeight 0 k *
      ‖((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * coeffOf u k‖ ^ 2 ≤ sobWeight 2 k * ‖coeffOf u k‖ ^ 2 := by
    intro k
    rw [sobWeight_zero, one_mul, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    unfold sobWeight
    have : ((1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ (2 : ℝ)) =
        (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [this]
    nlinarith [sq_nonneg (Real.pi * Lattice.enorm k), sq_nonneg (2 * Real.pi * Lattice.enorm k),
      sq_nonneg (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2)]
  unfold hsNormSq
  refine Summable.tsum_le_tsum hterm ?_ hm2'
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (by rw [sobWeight_zero]; norm_num) (sq_nonneg _))
    hterm hm2'

end Flow

/-- The frozen semigroup decays in `L²` with an `H²` loss on the datum
(Lyapunov functional: the weighted Dirichlet energy `E = ⟨L_β f, f⟩_{L²(μβ)} = ∫ρβ|∇f|²`,
`E' = 2⟨L_β f, -A_β L_β f⟩ ≤ -2 ν cP E`; this is simpler than the plan's `Φ = ⟨A L f, L f⟩`). -/
theorem exists_frozen_l2_decay (hd : 1 ≤ d) (s : ℝ) (νm νp c₀ Λ₀ : ℝ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (β : ℝ) (V ρβ : Torus d → ℝ)
      (H : FrozenHyp d s (mStar d + 5) νm νp c₀ Λ₀ β V ρβ),
      ∀ ψ : Torus d → ℝ, Continuous ψ → MemSobolev (mStar d + 2) ψ → ∀ τ, 0 ≤ τ →
        sobolevNorm 0 (equilibriumSemigroup (mfData d s H.hs0 H.hsd V β H.hβ) ρβ τ ψ) ≤
          C * Real.exp (-c * τ) * sobolevNorm 2 (projMean (withDensityReal ρβ) ψ) := by
  have hup : ∀ {β : ℝ} {V ρβ : Torus d → ℝ} (H : FrozenHyp d s (mStar d + 5) νm νp c₀ Λ₀ β V ρβ)
      (x : Torus d), ρβ x ≤ Λ₀ := by
    intro β V ρβ H x
    exact (le_abs_self _).trans ((abs_le_cbNorm (mStar d + 5) ρβ H.hρC x).trans H.hρb)
  by_cases hpos : 0 < c₀ ∧ 0 < νm ∧ 0 < Λ₀
  swap
  · refine ⟨1, 1, one_pos, one_pos, fun β V ρβ H => ?_⟩
    exfalso
    exact hpos ⟨H.hc₀, H.hνm, lt_of_lt_of_le H.hc₀ ((H.hlow 0).trans (hup H 0))⟩
  obtain ⟨hc₀, hνm, hΛ⟩ := hpos
  obtain ⟨cP, hcP, hPoin⟩ := exists_weighted_poincare (d := d) c₀ Λ₀ hc₀
  refine ⟨Real.sqrt (Λ₀ / (c₀ * cP)), νm * cP, Real.sqrt_pos.2 (by positivity), by positivity, ?_⟩
  intro β V ρβ H ψ hψc hψ τ hτ
  set D := mfData d s H.hs0 H.hsd V β H.hβ with hD
  have hprob : IsProbDensity ρβ := H.thermal.1
  have hρ1 : Torus.IsCk 1 ρβ := ET.isCk_mono' (a := 1) (b := mStar d + 5) (by omega) H.hρC
  have hρc : Continuous ρβ := MFAux.continuous_of_isCk hρ1
  have hP := hPoin ρβ hprob hρc H.hlow (hup H)
  have := MFSemigroup.isProb_withDensityReal hprob
  obtain ⟨hf2, hf0, hdec⟩ := frozen_energy_decay hd H hcP hP hψc hψ hτ
  set f := equilibriumSemigroup D ρβ τ ψ with hf
  have hf1 : Torus.IsCk 1 f := hf2.of_le (by norm_num)
  have hfc : Continuous f := MFAux.continuous_of_isCk hf1
  have hψ2 : Torus.IsCk 2 ψ := isCk_two_of_memSobolev hψc hψ
  -- (3) Poincaré for f
  have hPf := hP f hf1 hf0
  have hBff : Bform ρβ f f = ∫ x, ρβ x * ‖Torus.grad f x‖ ^ 2 := by
    unfold Bform
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [real_inner_self_eq_norm_sq]
  -- (2) L² vs weighted L²
  have hL : c₀ * ∫ x, f x ^ 2 ≤ l2Inner (withDensityReal ρβ) f f := by
    rw [l2Inner_mu hprob, ← integral_const_mul]
    exact integral_mono ((integrable_of_cont (hfc.pow 2)).const_mul c₀)
      (integrable_of_cont (hρc.mul (hfc.mul hfc))) fun x => by
        have := H.hlow x
        nlinarith [sq_nonneg (f x)]
  -- (4) the initial energy
  set u := projMean (withDensityReal ρβ) ψ with hu
  have hu2 : Torus.IsCk 2 u := by
    have : Torus.IsCk 2 (fun x => ψ x - pair (withDensityReal ρβ) ψ) := hψ2.sub contDiff_const
    exact this
  have hgradu : Torus.grad u = Torus.grad ψ := MFSemigroup.grad_projMean _ _
  have hB0 : Bform ρβ ψ ψ ≤ Λ₀ * sobolevNorm 2 u ^ 2 := by
    have h1 := integral_norm_grad_sq_le hu2
    rw [hgradu] at h1
    have : Bform ρβ ψ ψ ≤ Λ₀ * ∫ x, ‖Torus.grad ψ x‖ ^ 2 := by
      unfold Bform
      rw [← integral_const_mul]
      refine integral_mono (integrable_of_cont (hρc.mul (MFApriori.continuous_inner_grad (hψ2.of_le (by norm_num)) (hψ2.of_le (by norm_num)))))
        ?_ fun x => ?_
      · exact (integrable_of_cont (MFApriori.continuous_norm_grad_sq (hψ2.of_le (by norm_num)))).const_mul _
      · rw [real_inner_self_eq_norm_sq]
        exact mul_le_mul_of_nonneg_right (hup H x) (sq_nonneg _)
    exact this.trans (mul_le_mul_of_nonneg_left h1 hΛ.le)
  -- assemble
  have hN : 0 ≤ sobolevNorm 2 u := by unfold sobolevNorm; exact Real.sqrt_nonneg _
  have hcc : 0 < c₀ * cP := by positivity
  have hI : ∫ x, f x ^ 2 ≤ Λ₀ / (c₀ * cP) * (Real.exp (-(β⁻¹ * cP) * τ) * sobolevNorm 2 u) ^ 2 := by
    have h1 : c₀ * cP * ∫ x, f x ^ 2 ≤ Bform ρβ f f := by
      have := mul_le_mul_of_nonneg_left hL hcP.le
      rw [hBff]
      nlinarith [this, hPf]
    have h2 : Bform ρβ f f ≤ Real.exp (-(2 * (β⁻¹ * cP)) * τ) * (Λ₀ * sobolevNorm 2 u ^ 2) :=
      hdec.trans (mul_le_mul_of_nonneg_left hB0 (Real.exp_pos _).le)
    have h3 : Real.exp (-(2 * (β⁻¹ * cP)) * τ) = Real.exp (-(β⁻¹ * cP) * τ) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h3] at h2
    rw [div_mul_eq_mul_div, le_div_iff₀ hcc]
    nlinarith [h1, h2]
  have hK : Real.sqrt (Λ₀ / (c₀ * cP)) ^ 2 = Λ₀ / (c₀ * cP) :=
    Real.sq_sqrt (by positivity)
  have hexp : Real.exp (-(β⁻¹ * cP) * τ) ≤ Real.exp (-(νm * cP) * τ) := by
    apply Real.exp_le_exp.2
    have : νm ≤ β⁻¹ := H.hν.1
    nlinarith [mul_nonneg hcP.le hτ]
  rw [sobolevNorm_zero_eq hfc]
  calc Real.sqrt (∫ x, f x ^ 2)
      ≤ Real.sqrt ((Real.sqrt (Λ₀ / (c₀ * cP)) * (Real.exp (-(β⁻¹ * cP) * τ) * sobolevNorm 2 u)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [mul_pow, hK]; exact hI
    _ = Real.sqrt (Λ₀ / (c₀ * cP)) * (Real.exp (-(β⁻¹ * cP) * τ) * sobolevNorm 2 u) :=
        Real.sqrt_sq (by positivity)
    _ ≤ Real.sqrt (Λ₀ / (c₀ * cP)) * (Real.exp (-(νm * cP) * τ) * sobolevNorm 2 u) := by
        gcongr
    _ = _ := by ring


end HRS.PDE.MFAdjoint
