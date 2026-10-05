import Erdos883AdaptiveCertificate20682Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata20682 : coreProfileMetadataCheck adaptiveRows20682 = true := by
  rw [adaptiveRowsThroughEq20682]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 20682
theorem adaptiveOrder20682 : coreProfileOrderCheck adaptiveRows20682 = true := by
  rw [adaptiveRowsThroughEq20682]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 20682
end Erdos883Verified
