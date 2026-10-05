import Erdos883AdaptiveCertificate27530Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata27530 : coreProfileMetadataCheck adaptiveRows27530 = true := by
  rw [adaptiveRowsThroughEq27530]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 27530
theorem adaptiveOrder27530 : coreProfileOrderCheck adaptiveRows27530 = true := by
  rw [adaptiveRowsThroughEq27530]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 27530
end Erdos883Verified
