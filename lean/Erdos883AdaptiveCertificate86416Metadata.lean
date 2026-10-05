import Erdos883AdaptiveCertificate86416Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata86416 : coreProfileMetadataCheck adaptiveRows86416 = true := by
  rw [adaptiveRowsThroughEq86416]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 86416
theorem adaptiveOrder86416 : coreProfileOrderCheck adaptiveRows86416 = true := by
  rw [adaptiveRowsThroughEq86416]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 86416
end Erdos883Verified
