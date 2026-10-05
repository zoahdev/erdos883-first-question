import Erdos883AdaptiveCertificate33313Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata33313 : coreProfileMetadataCheck adaptiveRows33313 = true := by
  rw [adaptiveRowsThroughEq33313]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 33313
theorem adaptiveOrder33313 : coreProfileOrderCheck adaptiveRows33313 = true := by
  rw [adaptiveRowsThroughEq33313]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 33313
end Erdos883Verified
