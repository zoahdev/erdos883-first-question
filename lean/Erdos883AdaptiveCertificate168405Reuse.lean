import Erdos883AdaptiveCertificate168405Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq168405 : adaptiveRows168405 = adaptiveRowsThrough 168405 adaptiveRows199999 := by
  unfold adaptiveRows168405
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
