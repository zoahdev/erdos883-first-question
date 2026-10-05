import Erdos883AdaptiveCertificate78559Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq78559 : adaptiveRows78559 = adaptiveRowsThrough 78559 adaptiveRows199999 := by
  unfold adaptiveRows78559
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
