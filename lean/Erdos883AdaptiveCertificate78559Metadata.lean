import Erdos883AdaptiveCertificate78559Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata78559 : coreProfileMetadataCheck adaptiveRows78559 = true := by
  rw [adaptiveRowsThroughEq78559]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 78559
theorem adaptiveOrder78559 : coreProfileOrderCheck adaptiveRows78559 = true := by
  rw [adaptiveRowsThroughEq78559]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 78559
end Erdos883Verified
