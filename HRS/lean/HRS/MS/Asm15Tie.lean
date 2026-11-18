import HRS.MS.CzHlsTie
import HRS.MS.CzPvAsmAux2
import HRS.MS.CzElemAux4
import HRS.MS.Asm15Aux2

/-!
# ASM-15 ties (S.A.15): `lp_Lambda_commutator_low`, `lp_screened_negative_order`, `lp_positive_order_product`

* `lp_Lambda_commutator_low_proof` (`cbNorm 2`): `HRS.CZ.ElemA.lp_Lambda_commutator_low_cb2`, whose only hypothesis at
  `θ = 1` (`ElemTruncBound`) is discharged by `HRS.CZ.PvAsm.elemTruncBound_lin`.
* `lp_screened_negative_order_proof`: conjunct 1 from `HRS.CZ.Hls.lp_screened_negative_order_first_conjunct` at `Ω = u_i`
  (`asm15_isOddSmooth_coord`), conjunct 2 is `HRS.CZ.PvAsm.lp_screened_negative_order_theta_one_coord`.
* `lp_positive_order_product_proof`: `HRS.CZ.Asm15.asm15_lp_positive_order_product` (`Asm15Aux2.lean`): clause 1 from
  (ii-a) `elema_positive_order_bound`, clause 2 (ii-b) by the Mikhlin bounds for `ξ_i|ξ|^{θ-2}(1+4π²|ξ|²)^{-(θ-1)/2}`
  and the plain Bessel symbol.
-/

open MeasureTheory
open HRS.Whole.AppendixA

namespace HRS.CZ.Asm15

theorem lp_Lambda_commutator_low_proof {d : ℕ} (hd : 1 ≤ d) (θ p : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hp : 2 ≤ p) :
    ∃ C : ℝ, ∀ μ : Euc d → ℝ, HRS.MemCb 2 μ → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (lamComm d θ μ W) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * HRS.cbNorm 2 μ) * eLpNorm W (ENNReal.ofReal p) volume :=
  HRS.CZ.ElemA.lp_Lambda_commutator_low_cb2 hd θ p hθ0 hθ1 hp fun _ => by
    obtain ⟨CR, -, h⟩ := HRS.CZ.PvAsm.elemTruncBound_lin hd (show 1 < p by linarith)
    exact ⟨CR, h⟩

theorem asm15_isOddSmooth_coord {d : ℕ} (i : Fin d) : IsOddSmooth (fun u : Euc d => u i) :=
  ⟨(EuclideanSpace.proj (𝕜 := ℝ) i).contDiff, fun u _ => by simp⟩

theorem lp_screened_negative_order_proof {d : ℕ} (hd : 1 ≤ d) (θ p : ℝ) (hp : 2 ≤ p) (i : Fin d) :
    (0 < θ → θ < 1 → 1 / p + (1 - θ) / d < 1 →
      ∃ C : ℝ, ∀ a W : Euc d → ℝ, MemLp a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume →
        MemLp W (ENNReal.ofReal p) volume →
        eLpNorm (pvOdd d θ (fun u : Euc d => u i) fun x => a x * W x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal C * eLpNorm a (ENNReal.ofReal ((d : ℝ) / (1 - θ))) volume *
            eLpNorm W (ENNReal.ofReal p) volume) ∧
    (∃ C : ℝ, ∀ a W : Euc d → ℝ, MemLp a ⊤ volume → MemLp W (ENNReal.ofReal p) volume →
      eLpNorm (pvOdd d 1 (fun u : Euc d => u i) fun x => a x * W x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm a ⊤ volume * eLpNorm W (ENNReal.ofReal p) volume) :=
  ⟨fun h0 h1 hq => HRS.CZ.Hls.lp_screened_negative_order_first_conjunct hd θ p hp (fun u => u i)
      (asm15_isOddSmooth_coord i) h0 h1 hq,
    HRS.CZ.PvAsm.lp_screened_negative_order_theta_one_coord hd hp i⟩

theorem lp_positive_order_product_proof {d : ℕ} (hd : 1 ≤ d) (θ p : ℝ) (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hp : 2 ≤ p) (i : Fin d) :
    ∃ C : ℝ, ∀ a : Euc d → ℝ, HRS.MemCb 1 a →
      (∀ W : SchwartzMap (Euc d) ℝ,
        eLpNorm (fun x => pvOdd d θ (fun u : Euc d => u i) (fun y => a y * W y) x -
            a x * pvOdd d θ (fun u : Euc d => u i) W x)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * HRS.cbNorm 1 a) * eLpNorm W (ENNReal.ofReal p) volume) ∧
      ∀ Z : SchwartzMap (Euc d) ℝ,
        eLpNorm (pvOdd d θ (fun u : Euc d => u i) fun y => a y * Z y) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * HRS.cbNorm 1 a) * besselNormE d (θ - 1) p Z :=
  asm15_lp_positive_order_product hd θ p hθ1 hθ2 hp i

end HRS.CZ.Asm15

example : type_of% @HRS.Whole.AppendixA.lp_Lambda_commutator_low :=
  @HRS.CZ.Asm15.lp_Lambda_commutator_low_proof

example : type_of% @HRS.Whole.AppendixA.lp_screened_negative_order :=
  @HRS.CZ.Asm15.lp_screened_negative_order_proof

example : type_of% @HRS.Whole.AppendixA.lp_positive_order_product :=
  @HRS.CZ.Asm15.lp_positive_order_product_proof
