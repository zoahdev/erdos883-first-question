import Erdos883AdaptiveCertificate168405Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata168405 : coreProfileMetadataCheck adaptiveRows168405 = true := by
  rw [adaptiveRowsThroughEq168405]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 168405
theorem adaptiveOrder168405 : coreProfileOrderCheck adaptiveRows168405 = true := by
  rw [adaptiveRowsThroughEq168405]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 168405
end Erdos883Verified
