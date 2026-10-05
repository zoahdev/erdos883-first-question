import Erdos883AdaptiveCertificate185246Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata185246 : coreProfileMetadataCheck adaptiveRows185246 = true := by
  rw [adaptiveRowsThroughEq185246]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 185246
theorem adaptiveOrder185246 : coreProfileOrderCheck adaptiveRows185246 = true := by
  rw [adaptiveRowsThroughEq185246]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 185246
end Erdos883Verified
