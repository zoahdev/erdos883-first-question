import Erdos883AdaptiveCertificate18801Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata18801 : coreProfileMetadataCheck adaptiveRows18801 = true := by
  rw [adaptiveRowsThroughEq18801]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 18801
theorem adaptiveOrder18801 : coreProfileOrderCheck adaptiveRows18801 = true := by
  rw [adaptiveRowsThroughEq18801]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 18801
end Erdos883Verified
