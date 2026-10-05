import Erdos883AdaptiveCertificate17091Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata17091 : coreProfileMetadataCheck adaptiveRows17091 = true := by
  rw [adaptiveRowsThroughEq17091]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 17091
theorem adaptiveOrder17091 : coreProfileOrderCheck adaptiveRows17091 = true := by
  rw [adaptiveRowsThroughEq17091]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 17091
end Erdos883Verified
