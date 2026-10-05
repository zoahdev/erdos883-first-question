import Erdos883AdaptiveCertificate18801Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq18801 : adaptiveRows18801 = adaptiveRowsThrough 18801 adaptiveRows199999 := by
  unfold adaptiveRows18801
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
