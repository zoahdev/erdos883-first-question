import Erdos883AdaptiveCertificate185246Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq185246 : adaptiveRows185246 = adaptiveRowsThrough 185246 adaptiveRows199999 := by
  unfold adaptiveRows185246
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
