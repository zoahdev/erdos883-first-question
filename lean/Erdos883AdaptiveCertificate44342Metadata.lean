import Erdos883AdaptiveCertificate44342Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata44342 : coreProfileMetadataCheck adaptiveRows44342 = true := by
  rw [adaptiveRowsThroughEq44342]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 44342
theorem adaptiveOrder44342 : coreProfileOrderCheck adaptiveRows44342 = true := by
  rw [adaptiveRowsThroughEq44342]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 44342
end Erdos883Verified
