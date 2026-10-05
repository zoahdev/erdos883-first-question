import Erdos883AdaptiveCertificate12839Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq12839 : adaptiveRows12839 = adaptiveRowsThrough 12839 adaptiveRows199999 := by
  unfold adaptiveRows12839
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
