import Erdos883AdaptiveCertificate115021Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq115021 : adaptiveRows115021 = adaptiveRowsThrough 115021 adaptiveRows199999 := by
  unfold adaptiveRows115021
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
