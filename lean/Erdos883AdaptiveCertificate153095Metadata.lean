import Erdos883AdaptiveCertificate153095Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata153095 : coreProfileMetadataCheck adaptiveRows153095 = true := by
  rw [adaptiveRowsThroughEq153095]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 153095
theorem adaptiveOrder153095 : coreProfileOrderCheck adaptiveRows153095 = true := by
  rw [adaptiveRowsThroughEq153095]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 153095
end Erdos883Verified
