import HRS.MC.WinJP12
import HRS.MC.E214Final

/-! Tie of `WinJ.p_assembly` to the frozen `WinJCompare` (this file does not import the sorried `E214Plan`). -/

noncomputable section

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan HRS.MC.Sec7.PID HRS.MC.E213U3

example {d : ℕ} {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE) (T : ℝ)
    (hT : 0 < T) : HRS.MC.E214O.WinJCompare sd T hT := HRS.MC.WinJ.p_assembly sd T hT

end
