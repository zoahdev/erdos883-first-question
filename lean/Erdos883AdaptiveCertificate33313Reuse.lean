import Erdos883AdaptiveCertificate33313Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq33313 : adaptiveRows33313 = adaptiveRowsThrough 33313 adaptiveRows199999 := by
  unfold adaptiveRows33313
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
