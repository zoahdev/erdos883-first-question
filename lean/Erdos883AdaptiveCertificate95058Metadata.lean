import Erdos883AdaptiveCertificate95058Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata95058 : coreProfileMetadataCheck adaptiveRows95058 = true := by
  rw [adaptiveRowsThroughEq95058]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 95058
theorem adaptiveOrder95058 : coreProfileOrderCheck adaptiveRows95058 = true := by
  rw [adaptiveRowsThroughEq95058]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 95058
end Erdos883Verified
