import Erdos883AdaptiveCertificate71417Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq71417 : adaptiveRows71417 = adaptiveRowsThrough 71417 adaptiveRows199999 := by
  unfold adaptiveRows71417
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
