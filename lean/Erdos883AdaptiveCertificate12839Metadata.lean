import Erdos883AdaptiveCertificate12839Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata12839 : coreProfileMetadataCheck adaptiveRows12839 = true := by
  rw [adaptiveRowsThroughEq12839]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 12839
theorem adaptiveOrder12839 : coreProfileOrderCheck adaptiveRows12839 = true := by
  rw [adaptiveRowsThroughEq12839]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 12839
end Erdos883Verified
