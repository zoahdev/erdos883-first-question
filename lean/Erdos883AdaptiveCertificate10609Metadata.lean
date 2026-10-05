import Erdos883AdaptiveCertificate10609Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata10609 : coreProfileMetadataCheck adaptiveRows10609 = true := by
  rw [adaptiveRowsThroughEq10609]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 10609
theorem adaptiveOrder10609 : coreProfileOrderCheck adaptiveRows10609 = true := by
  rw [adaptiveRowsThroughEq10609]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 10609
end Erdos883Verified
