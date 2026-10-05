import Erdos883AdaptiveCertificate20682Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq20682 : adaptiveRows20682 = adaptiveRowsThrough 20682 adaptiveRows199999 := by
  unfold adaptiveRows20682
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
