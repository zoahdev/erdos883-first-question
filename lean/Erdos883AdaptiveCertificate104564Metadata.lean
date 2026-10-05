import Erdos883AdaptiveCertificate104564Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata104564 : coreProfileMetadataCheck adaptiveRows104564 = true := by
  rw [adaptiveRowsThroughEq104564]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 104564
theorem adaptiveOrder104564 : coreProfileOrderCheck adaptiveRows104564 = true := by
  rw [adaptiveRowsThroughEq104564]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 104564
end Erdos883Verified
