import Erdos883AdaptiveCertificate71417Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata71417 : coreProfileMetadataCheck adaptiveRows71417 = true := by
  rw [adaptiveRowsThroughEq71417]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 71417
theorem adaptiveOrder71417 : coreProfileOrderCheck adaptiveRows71417 = true := by
  rw [adaptiveRowsThroughEq71417]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 71417
end Erdos883Verified
