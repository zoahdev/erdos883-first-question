import Erdos883AdaptiveCertificate64924Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata64924 : coreProfileMetadataCheck adaptiveRows64924 = true := by
  rw [adaptiveRowsThroughEq64924]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 64924
theorem adaptiveOrder64924 : coreProfileOrderCheck adaptiveRows64924 = true := by
  rw [adaptiveRowsThroughEq64924]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 64924
end Erdos883Verified
