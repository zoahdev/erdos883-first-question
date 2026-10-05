import Erdos883AdaptiveCertificate115021Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata115021 : coreProfileMetadataCheck adaptiveRows115021 = true := by
  rw [adaptiveRowsThroughEq115021]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 115021
theorem adaptiveOrder115021 : coreProfileOrderCheck adaptiveRows115021 = true := by
  rw [adaptiveRowsThroughEq115021]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 115021
end Erdos883Verified
