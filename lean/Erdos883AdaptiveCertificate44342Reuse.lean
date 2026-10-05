import Erdos883AdaptiveCertificate44342Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq44342 : adaptiveRows44342 = adaptiveRowsThrough 44342 adaptiveRows199999 := by
  unfold adaptiveRows44342
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
