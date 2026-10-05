import Erdos883AdaptiveCertificate95058Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq95058 : adaptiveRows95058 = adaptiveRowsThrough 95058 adaptiveRows199999 := by
  unfold adaptiveRows95058
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
