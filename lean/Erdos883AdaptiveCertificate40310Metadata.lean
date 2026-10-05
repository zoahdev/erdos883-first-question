import Erdos883AdaptiveCertificate40310Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata40310 : coreProfileMetadataCheck adaptiveRows40310 = true := by
  rw [adaptiveRowsThroughEq40310]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 40310
theorem adaptiveOrder40310 : coreProfileOrderCheck adaptiveRows40310 = true := by
  rw [adaptiveRowsThroughEq40310]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 40310
end Erdos883Verified
