import Erdos883AdaptiveCertificate40310Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq40310 : adaptiveRows40310 = adaptiveRowsThrough 40310 adaptiveRows199999 := by
  unfold adaptiveRows40310
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
