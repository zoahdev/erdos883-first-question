import Erdos883AdaptiveCertificate36645Data
import Erdos883AdaptiveCertificateReuse
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveRowsThroughEq36645 : adaptiveRows36645 = adaptiveRowsThrough 36645 adaptiveRows199999 := by
  unfold adaptiveRows36645
  rw [adaptiveRows199999, adaptiveRowsThrough_flatten]
  apply congrArg List.flatten
  simp only [List.map_cons, List.map_nil]
  rfl
end Erdos883Verified
