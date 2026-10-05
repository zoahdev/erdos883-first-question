import Erdos883AdaptiveCertificate14124Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata14124 : coreProfileMetadataCheck adaptiveRows14124 = true := by
  rw [adaptiveRowsThroughEq14124]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 14124
theorem adaptiveOrder14124 : coreProfileOrderCheck adaptiveRows14124 = true := by
  rw [adaptiveRowsThroughEq14124]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 14124
end Erdos883Verified
