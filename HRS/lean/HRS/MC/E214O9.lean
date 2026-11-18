import HRS.MC.E214O8
import HRS.MC.E214L4

/-!
# Packet E214O, part 9: `Kwin_relax_cond_proof`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214O

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

theorem o_exp_mono {C c c' a : ℝ} (hC : 0 ≤ C) (hc : c' ≤ c) (ha : 0 ≤ a) :
    C * Real.exp (-c * a) ≤ C * Real.exp (-c' * a) :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hC

section KwinRelax

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} {sd : StatDatum S β₀ m hE}

set_option maxHeartbeats 4000000 in
theorem Kwin_relax_cond_proof (pg : PairGD sd) (T : ℝ) (hT : 0 < T) (hJ : WinJCompare sd T hT) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a : ℝ, 0 ≤ a →
      ‖pg.gd.Kproj T a - pg.gds.Kproj T a‖ ≤ C * Real.exp (-c * a) := by
  obtain ⟨Cd, cd, hCd, hcd, hD⟩ := Dwin_relax_proof pg T hT 3 (by norm_num)
  obtain ⟨Cz3, cz3, hCz3, hcz3, hZ3⟩ := HRS.MC.E214L.Zwin_relax_proof pg T hT 3 (by norm_num)
  obtain ⟨CJ, cJ, hCJ, hcJ, hJr⟩ := Jwin_relax_cond_proof pg T hT hJ 2 (by norm_num)
  obtain ⟨Cz2, cz2, hCz2, hcz2, hZ2⟩ := HRS.MC.E214L.Zwin_relax_proof pg T hT 2 (by norm_num)
  obtain ⟨C1, c1, hC1, hc1, hI1⟩ := o_init_decay S β₀ hE T
  obtain ⟨C2, c2, hC2, hc2, hI2⟩ := o_init_decay sd.Ss S.β sd.hEs T
  obtain ⟨MZ, hMZ0, hMZ⟩ := o_mom_Z3 pg.gd T hT
  obtain ⟨MZ', hMZ'0, hMZ'⟩ := o_mom_Z3 pg.gds T hT
  obtain ⟨MD, hMD0, hMD⟩ := o_mom_D3 pg.gd T hT
  obtain ⟨MD', hMD'0, hMD'⟩ := o_mom_D3 pg.gds T hT
  obtain ⟨MZ2, hMZ20, hMZ2⟩ := o_mom_Z2 pg.gd T hT
  obtain ⟨MJ', hMJ'0, hMJ'⟩ := o_mom_J2 pg.gds T hT
  obtain ⟨MJ, hMJ0, hMJ⟩ := o_mom_J2 pg.gd T hT
  have e3 : ENNReal.ofReal 3 = (3 : ℝ≥0∞) := by norm_num
  have e2 : ENNReal.ofReal 2 = (2 : ℝ≥0∞) := by norm_num
  set c := min (min (min cd cz3) (min cJ cz2)) (min c1 c2) with hc
  have hcpos : 0 < c := lt_min (lt_min (lt_min hcd hcz3) (lt_min hcJ hcz2)) (lt_min hc1 hc2)
  have hc_cd : c ≤ cd := (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hc_cz3 : c ≤ cz3 := (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hc_cJ : c ≤ cJ := (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hc_cz2 : c ≤ cz2 := (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hc_c1 : c ≤ c1 := (min_le_right _ _).trans (min_le_left _ _)
  have hc_c2 : c ≤ c2 := (min_le_right _ _).trans (min_le_right _ _)
  set K3 := Cd * MZ * MZ + MD' * Cz3 * MZ + MD' * MZ' * Cz3 with hK3
  set K21 := CJ * MZ2 + MJ' * Cz2 with hK21
  refine ⟨(C1 + C2) + 3 * K3 + 3 * K21 + 1, c, by positivity, hcpos, fun a ha => ?_⟩
  have hK := o_Kproj_sub_le pg.gd pg.gds T hT a ha
  -- the cubic term
  have hDm : AEStronglyMeasurable (pg.gd.Dwin T a) pg.P := (hMD a ha).1
  have hDm' : AEStronglyMeasurable (pg.gds.Dwin T a) pg.P := (hMD' a ha).1
  have hZm : AEStronglyMeasurable (pg.gd.Zwin T a) pg.P := (hMZ a ha).1
  have hZm' : AEStronglyMeasurable (pg.gds.Zwin T a) pg.P := (hMZ' a ha).1
  have hdx : eLpNorm (fun ω => pg.gd.Dwin T a ω - pg.gds.Dwin T a ω) 3 pg.P ≤
      ENNReal.ofReal (Cd * Real.exp (-cd * a)) := by
    have := hD a ha; rwa [e3] at this
  have hdy : eLpNorm (fun ω => pg.gd.Zwin T a ω - pg.gds.Zwin T a ω) 3 pg.P ≤
      ENNReal.ofReal (Cz3 * Real.exp (-cz3 * a)) := by
    have := hZ3 a ha; rwa [e3] at this
  have hb3 := HRS.MC.E214M.norm_bochTensor3_sub_le_holder pg.P
    (x := pg.gd.Dwin T a) (y := pg.gd.Zwin T a) (z := pg.gd.Zwin T a)
    (x' := pg.gds.Dwin T a) (y' := pg.gds.Zwin T a) (z' := pg.gds.Zwin T a)
    hDm hZm hZm hDm' hZm' hZm'
    (δx := Cd * Real.exp (-cd * a)) (δy := Cz3 * Real.exp (-cz3 * a)) (δz := Cz3 * Real.exp (-cz3 * a))
    (My := MZ) (Mz := MZ) (Mx' := MD') (My' := MZ')
    (by positivity) (by positivity) (by positivity) hMZ0 hMZ0 hMD'0 hMZ'0 hdx hdy hdy
    (hMZ a ha).2 (hMZ a ha).2 (hMD' a ha).2 (hMZ' a ha).2
  -- the covariance term
  have hJm : AEStronglyMeasurable (pg.gd.Jwin T a) pg.P := (hMJ a ha).1
  have hJm' : AEStronglyMeasurable (pg.gds.Jwin T a) pg.P := (hMJ' a ha).1
  have hZ2m : AEStronglyMeasurable (pg.gd.Zwin T a) pg.P := (hMZ2 a ha).1
  have hZ2m' : AEStronglyMeasurable (pg.gds.Zwin T a) pg.P := hZm'
  have hdJ : eLpNorm (fun ω => pg.gd.Jwin T a ω - pg.gds.Jwin T a ω) 2 pg.P ≤
      ENNReal.ofReal (CJ * Real.exp (-cJ * a)) := by
    have := hJr a ha; rwa [e2] at this
  have hdg : eLpNorm (fun ω => pg.gd.Zwin T a ω - pg.gds.Zwin T a ω) 2 pg.P ≤
      ENNReal.ofReal (Cz2 * Real.exp (-cz2 * a)) := by
    have := hZ2 a ha; rwa [e2] at this
  have hb21 := HRS.MC.E214M.norm_bochTensor21_sub_le_holder pg.P
    (J := pg.gd.Jwin T a) (J' := pg.gds.Jwin T a) (g := pg.gd.Zwin T a) (g' := pg.gds.Zwin T a)
    hJm hJm' hZ2m hZ2m'
    (δJ := CJ * Real.exp (-cJ * a)) (δg := Cz2 * Real.exp (-cz2 * a)) (Mg := MZ2) (MJ' := MJ')
    (by positivity) (by positivity) hMZ20 hMJ'0 hdJ hdg (hMZ2 a ha).2 (hMJ' a ha).2
  -- assemble
  have i1 := (hI1 a ha).trans (o_exp_mono hC1.le hc_c1 ha)
  have i2 := (hI2 a ha).trans (o_exp_mono hC2.le hc_c2 ha)
  have ex1 : Real.exp (-cd * a) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by nlinarith)
  have ex2 : Real.exp (-cz3 * a) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by nlinarith)
  have ex3 : Real.exp (-cJ * a) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by nlinarith)
  have ex4 : Real.exp (-cz2 * a) ≤ Real.exp (-c * a) := Real.exp_le_exp.2 (by nlinarith)
  have hE0 : 0 < Real.exp (-c * a) := Real.exp_pos _
  have b3 : Cd * Real.exp (-cd * a) * MZ * MZ + MD' * (Cz3 * Real.exp (-cz3 * a)) * MZ +
      MD' * MZ' * (Cz3 * Real.exp (-cz3 * a)) ≤ K3 * Real.exp (-c * a) := by
    rw [hK3]
    have t1 : Cd * Real.exp (-cd * a) * MZ * MZ ≤ Cd * Real.exp (-c * a) * MZ * MZ := by gcongr
    have t2 : MD' * (Cz3 * Real.exp (-cz3 * a)) * MZ ≤ MD' * (Cz3 * Real.exp (-c * a)) * MZ := by gcongr
    have t3 : MD' * MZ' * (Cz3 * Real.exp (-cz3 * a)) ≤ MD' * MZ' * (Cz3 * Real.exp (-c * a)) := by gcongr
    nlinarith
  have b21 : CJ * Real.exp (-cJ * a) * MZ2 + MJ' * (Cz2 * Real.exp (-cz2 * a)) ≤ K21 * Real.exp (-c * a) := by
    rw [hK21]
    have t1 : CJ * Real.exp (-cJ * a) * MZ2 ≤ CJ * Real.exp (-c * a) * MZ2 := by gcongr
    have t2 : MJ' * (Cz2 * Real.exp (-cz2 * a)) ≤ MJ' * (Cz2 * Real.exp (-c * a)) := by gcongr
    nlinarith
  have hK' : ‖pg.gd.Kproj T a - pg.gds.Kproj T a‖ ≤
      (‖pushforward3 (Iwin S β₀ hE T a) (Kinit0 S β₀)‖ +
        ‖pushforward3 (Iwin sd.Ss S.β sd.hEs T a) (Kinit0 sd.Ss S.β)‖) +
      3 * ‖bochTensor3 pg.P (pg.gd.Dwin T a) (pg.gd.Zwin T a) (pg.gd.Zwin T a) -
        bochTensor3 pg.P (pg.gds.Dwin T a) (pg.gds.Zwin T a) (pg.gds.Zwin T a)‖ +
      3 * ‖bochTensor21 pg.P (pg.gd.Jwin T a) (pg.gd.Zwin T a) -
        bochTensor21 pg.P (pg.gds.Jwin T a) (pg.gds.Zwin T a)‖ := hK
  have hfin : (C1 * Real.exp (-c * a) + C2 * Real.exp (-c * a)) + 3 * (K3 * Real.exp (-c * a)) +
      3 * (K21 * Real.exp (-c * a)) ≤ ((C1 + C2) + 3 * K3 + 3 * K21 + 1) * Real.exp (-c * a) := by
    nlinarith
  refine hK'.trans ?_
  refine le_trans ?_ hfin
  have := add_le_add (add_le_add (add_le_add i1 i2) (mul_le_mul_of_nonneg_left (hb3.trans b3) (by norm_num : (0:ℝ) ≤ 3)))
    (mul_le_mul_of_nonneg_left (hb21.trans b21) (by norm_num : (0:ℝ) ≤ 3))
  exact this

end KwinRelax

end HRS.MC.E214O

end
