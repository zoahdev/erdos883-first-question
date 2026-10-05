import Erdos883AdaptiveCertificate22751Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata22751 : coreProfileMetadataCheck adaptiveRows22751 = true := by
  rw [adaptiveRowsThroughEq22751]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 22751
theorem adaptiveOrder22751 : coreProfileOrderCheck adaptiveRows22751 = true := by
  rw [adaptiveRowsThroughEq22751]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 22751
end Erdos883Verified
