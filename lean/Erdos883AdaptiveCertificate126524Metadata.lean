import Erdos883AdaptiveCertificate126524Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata126524 : coreProfileMetadataCheck adaptiveRows126524 = true := by
  rw [adaptiveRowsThroughEq126524]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 126524
theorem adaptiveOrder126524 : coreProfileOrderCheck adaptiveRows126524 = true := by
  rw [adaptiveRowsThroughEq126524]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 126524
end Erdos883Verified
