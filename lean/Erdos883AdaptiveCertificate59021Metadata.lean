import Erdos883AdaptiveCertificate59021Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata59021 : coreProfileMetadataCheck adaptiveRows59021 = true := by
  rw [adaptiveRowsThroughEq59021]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 59021
theorem adaptiveOrder59021 : coreProfileOrderCheck adaptiveRows59021 = true := by
  rw [adaptiveRowsThroughEq59021]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 59021
end Erdos883Verified
