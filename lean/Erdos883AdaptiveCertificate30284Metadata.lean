import Erdos883AdaptiveCertificate30284Reuse
import Erdos883AdaptiveCertificate199999Metadata
namespace Erdos883Verified
theorem adaptiveMetadata30284 : coreProfileMetadataCheck adaptiveRows30284 = true := by
  rw [adaptiveRowsThroughEq30284]
  exact coreProfileMetadataCheck_rowsThrough adaptiveMetadata199999 30284
theorem adaptiveOrder30284 : coreProfileOrderCheck adaptiveRows30284 = true := by
  rw [adaptiveRowsThroughEq30284]
  exact adaptiveRowsThrough_order (coreProfileMetadataCheck_sound adaptiveMetadata199999) adaptiveOrder199999 30284
end Erdos883Verified
