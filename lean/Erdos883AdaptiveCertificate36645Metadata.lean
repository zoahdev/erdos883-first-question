import Erdos883AdaptiveCertificate36645Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata36645 : coreProfileMetadataCheck adaptiveRows36645 = true := by
  rw [adaptiveRowsThroughEq36645]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 36645
theorem adaptiveOrder36645 : coreProfileOrderCheck adaptiveRows36645 = true := by
  rw [adaptiveRowsThroughEq36645]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 36645
end Erdos883Verified
