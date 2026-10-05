import Erdos883SmallCertificate509Data
import Erdos883SmallCertificateCoreBridge
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem dataValidChunk509_0 :
    OddCertificateDataValid [3, 5, 7, 11] ((coreMetadataChunks509 0).map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValidChunk509_0
end Erdos883Verified
