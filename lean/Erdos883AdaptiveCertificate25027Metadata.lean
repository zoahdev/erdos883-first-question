import Erdos883AdaptiveCertificate25027Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata25027 : coreProfileMetadataCheck adaptiveRows25027 = true := by
  rw [adaptiveRowsThroughEq25027]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 25027
theorem adaptiveOrder25027 : coreProfileOrderCheck adaptiveRows25027 = true := by
  rw [adaptiveRowsThroughEq25027]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 25027
end Erdos883Verified
