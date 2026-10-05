import Erdos883AdaptiveCertificate15537Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata15537 : coreProfileMetadataCheck adaptiveRows15537 = true := by
  rw [adaptiveRowsThroughEq15537]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 15537
theorem adaptiveOrder15537 : coreProfileOrderCheck adaptiveRows15537 = true := by
  rw [adaptiveRowsThroughEq15537]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 15537
end Erdos883Verified
