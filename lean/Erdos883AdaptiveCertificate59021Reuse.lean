import Erdos883AdaptiveCertificate59021Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq59021 : adaptiveRows59021 = adaptiveRowsThrough 59021 adaptiveRows199999 := by
  unfold adaptiveRows59021
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
