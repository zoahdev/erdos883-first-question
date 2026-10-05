import Erdos883AdaptiveCertificate11671Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata11671 : coreProfileMetadataCheck adaptiveRows11671 = true := by
  rw [adaptiveRowsThroughEq11671]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 11671
theorem adaptiveOrder11671 : coreProfileOrderCheck adaptiveRows11671 = true := by
  rw [adaptiveRowsThroughEq11671]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 11671
end Erdos883Verified
