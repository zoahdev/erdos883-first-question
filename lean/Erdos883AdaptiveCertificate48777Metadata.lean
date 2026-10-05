import Erdos883AdaptiveCertificate48777Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata48777 : coreProfileMetadataCheck adaptiveRows48777 = true := by
  rw [adaptiveRowsThroughEq48777]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 48777
theorem adaptiveOrder48777 : coreProfileOrderCheck adaptiveRows48777 = true := by
  rw [adaptiveRowsThroughEq48777]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 48777
end Erdos883Verified
