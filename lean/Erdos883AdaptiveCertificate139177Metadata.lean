import Erdos883AdaptiveCertificate139177Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata139177 : coreProfileMetadataCheck adaptiveRows139177 = true := by
  rw [adaptiveRowsThroughEq139177]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 139177
theorem adaptiveOrder139177 : coreProfileOrderCheck adaptiveRows139177 = true := by
  rw [adaptiveRowsThroughEq139177]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 139177
end Erdos883Verified
