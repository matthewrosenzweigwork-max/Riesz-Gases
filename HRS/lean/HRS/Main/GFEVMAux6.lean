import HRS.Main.GFEVMAux5

/-!
# Packet GFEVM, part 6: the backward generator on `C² ∩ H^{a+2}`: membership in `H^a`, linearity, constants, increments in `ρ`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.GF

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

theorem gfm_isCk_const (c : ℝ) : Torus.IsCk 2 (fun _ : Torus d => c) := by
  unfold Torus.IsCk
  exact contDiff_const

theorem gfm_isCk_lin {u v : Torus d → ℝ} (hu : Torus.IsCk 2 u) (hv : Torus.IsCk 2 v) (α β : ℝ) :
    Torus.IsCk 2 (fun x => α * u x + β * v x) := by
  unfold Torus.IsCk at *
  show ContDiff ℝ 2 (fun y => α * Torus.lift u y + β * Torus.lift v y)
  exact (contDiff_const.mul hu).add (contDiff_const.mul hv)

theorem gfm_cont_of_isCk2 {u : Torus d → ℝ} (hu : Torus.IsCk 2 u) : Continuous u :=
  ClassicalAux.continuous_of_isCk (ClassicalAux.isCk_of_le (by norm_num) hu)

theorem gfm_memSobolev_lin {m : ℝ} {u v : Torus d → ℝ} (hu : Continuous u) (hv : Continuous v)
    (hu' : MemSobolev m u) (hv' : MemSobolev m v) (α β : ℝ) :
    MemSobolev m (fun x => α * u x + β * v x) := by
  have hc : Continuous (fun x => α * u x + β * v x) :=
    (continuous_const.mul hu).add (continuous_const.mul hv)
  refine memSobolev_of_memHs _ _ (ClassicalAux.memLp_two_of_continuous hc) ?_
  rw [Q54.coeffOf_lin hu hv α β]
  have h1 := (hsNormSq_coeffOf m u hu').1
  have h2 := (hsNormSq_coeffOf m v hv').1
  exact MFThermalReg.memHs_add (MFThermalReg.memHs_smul h1 (α : ℂ)) (MFThermalReg.memHs_smul h2 (β : ℂ))

theorem gfmCls_lin {m : ℝ} {u v : Torus d → ℝ} (hu : gfmCls m u) (hv : gfmCls m v) (α β : ℝ) :
    gfmCls m (fun x => α * u x + β * v x) :=
  ⟨gfm_isCk_lin hu.1 hv.1 α β,
    gfm_memSobolev_lin (gfm_cont_of_isCk2 hu.1) (gfm_cont_of_isCk2 hv.1) hu.2 hv.2 α β⟩

theorem gfmCls_smooth (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : gfmCls m φ :=
  ⟨(show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ).of_le
      (by first | exact WithTop.coe_le_coe.2 le_top | (norm_cast; exact le_top) | simp), MFSemigroup.memSobolev_of_isSmooth hφ m⟩

theorem gfmCls_mono {m m' : ℝ} {φ : Torus d → ℝ} (hφ : gfmCls m φ) (h : m' ≤ m) : gfmCls m' φ :=
  ⟨hφ.1, gfm_memSobolev_mono hφ.2 h⟩

section Gen

variable {s K MB Bμ BV : ℝ} {ρ' : Torus d → ℝ}

theorem gfm_bg_facts (D : DynData d) (hd : 1 ≤ d) (hsd : s < d) (a : ℝ) (ha : 1 ≤ a + 2)
    (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV) (hK : (d : ℝ) + |a| + 4 ≤ K)
    (hρ1 : Torus.IsCk 1 ρ') (hV1 : Torus.IsCk 1 D.V) (hG : GenHyp d s K MB Bμ BV D ρ')
    {φ : Torus d → ℝ} (hφ : gfmCls (a + 2) φ) :
    coeffOf (backwardGenerator D ρ' φ) = forwardGen D ρ' (coeffOf φ) ∧
      Continuous (backwardGenerator D ρ' φ) ∧ MemSobolev a (backwardGenerator D ρ' φ) := by
  have hK' : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd D
  have hc : coeffOf (backwardGenerator D ρ' φ) = forwardGen D ρ' (coeffOf φ) :=
    ClassicalAux.coeffOf_backwardGenerator D hK' hV1 hρ1 hφ.1
  have hcont : Continuous (backwardGenerator D ρ' φ) :=
    MFSemigroup.continuous_backwardGenerator D hK' hV1 hρ1 hφ.1
  obtain ⟨C, hC, hgen⟩ := gen_hs_bound s hsd K MB Bμ BV hMB hBμ hBV a hK
  have hc2 : MemHs (a + 2) (coeffOf φ) := (hsNormSq_coeffOf (a + 2) φ hφ.2).1
  have hm := (hgen D ρ' hG (coeffOf φ) hc2 (hc2.mono ha)).1
  exact ⟨hc, hcont, memSobolev_of_memHs a _ (ClassicalAux.memLp_two_of_continuous hcont)
    (by rw [hc]; exact hm)⟩

theorem gfm_bg_lin (D : DynData d) (hd : 1 ≤ d) (hsd : s < d) (hMB : 0 ≤ MB) (hBμ : 0 ≤ Bμ) (hBV : 0 ≤ BV)
    (hK1 : (d : ℝ) / 2 + 1 < K) (hρ1 : Torus.IsCk 1 ρ') (hV1 : Torus.IsCk 1 D.V)
    (hG : GenHyp d s K MB Bμ BV D ρ') {u v : Torus d → ℝ} (hu : Torus.IsCk 2 u) (hv : Torus.IsCk 2 v)
    (hu1 : MemSobolev 1 u) (hv1 : MemSobolev 1 v) (α β : ℝ) :
    backwardGenerator D ρ' (fun x => α * u x + β * v x) =
      fun x => α * backwardGenerator D ρ' u x + β * backwardGenerator D ρ' v x := by
  have hK' : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd D
  have cu := gfm_cont_of_isCk2 hu
  have cv := gfm_cont_of_isCk2 hv
  have hcl := gfm_isCk_lin hu hv α β
  have hbu := MFSemigroup.continuous_backwardGenerator D hK' hV1 hρ1 hu
  have hbv := MFSemigroup.continuous_backwardGenerator D hK' hV1 hρ1 hv
  have hbc := MFSemigroup.continuous_backwardGenerator D hK' hV1 hρ1 hcl
  obtain ⟨h0, hdr⟩ := genHyp_memHs0 hsd hG hK1 hMB hBμ hBV
  have hu1' : MemHs 1 (coeffOf u) := (hsNormSq_coeffOf 1 u hu1).1
  have hv1' : MemHs 1 (coeffOf v) := (hsNormSq_coeffOf 1 v hv1).1
  refine ClassicalAux.eq_of_coeffOf_eq hbc ((continuous_const.mul hbu).add (continuous_const.mul hbv)) ?_
  rw [ClassicalAux.coeffOf_backwardGenerator D hK' hV1 hρ1 hcl, Q54.coeffOf_lin cu cv α β,
    Q54.coeffOf_lin hbu hbv α β, ClassicalAux.coeffOf_backwardGenerator D hK' hV1 hρ1 hu,
    ClassicalAux.coeffOf_backwardGenerator D hK' hV1 hρ1 hv]
  exact gfev_forwardGen_lin D ρ' h0 hdr hu1' hv1' (α : ℂ) (β : ℂ)

theorem gfm_bg_const (D : DynData d) (hd : 1 ≤ d) (hρ1 : Torus.IsCk 1 ρ') (hV1 : Torus.IsCk 1 D.V) (c : ℝ) :
    backwardGenerator D ρ' (fun _ => c) = fun _ => 0 := by
  have hK' : ClassicalAux.ConvKernelFacts d D.s := ClassicalAux.convKernelFacts hd D
  refine ClassicalAux.eq_of_coeffOf_eq
    (MFSemigroup.continuous_backwardGenerator D hK' hV1 hρ1 (gfm_isCk_const c)) continuous_const ?_
  rw [ClassicalAux.coeffOf_backwardGenerator D hK' hV1 hρ1 (gfm_isCk_const c), gfev_forwardGen_delta]
  funext k
  rw [ClassicalAux.coeffOf_apply]
  simp

end Gen

end HRS.GF
