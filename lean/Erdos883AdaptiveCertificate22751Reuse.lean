import Erdos883AdaptiveCertificate22751Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq22751 : adaptiveRows22751 = adaptiveRowsThrough 22751 adaptiveRows199999 := by
  unfold adaptiveRows22751
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
