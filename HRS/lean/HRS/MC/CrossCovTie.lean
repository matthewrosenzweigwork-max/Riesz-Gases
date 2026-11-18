import HRS.MC.CrossCovP6
import HRS.Main.HeadlineEdgeworth

/-!
# Packet CC6 tie: `p_assembly` has the type of the frozen row `HRS.Main.cross_cov_densities_exist`
(`HRS/Main/HeadlineEdgeworth.lean`).  The check only elaborates; it adds no proof.
-/

namespace HRS.MC.CrossCov

example := (@HRS.MC.CrossCov.p_assembly : type_of% @HRS.Main.cross_cov_densities_exist)

end HRS.MC.CrossCov
