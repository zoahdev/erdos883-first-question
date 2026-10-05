import Erdos883AdaptiveCertificate53655Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata53655 : coreProfileMetadataCheck adaptiveRows53655 = true := by
  rw [adaptiveRowsThroughEq53655]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 53655
theorem adaptiveOrder53655 : coreProfileOrderCheck adaptiveRows53655 = true := by
  rw [adaptiveRowsThroughEq53655]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 53655
end Erdos883Verified
