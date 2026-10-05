import Erdos883SmallCertificate561Data
import Erdos883SmallCertificateCoreBridge
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem dataValidChunk561_4 :
    OddCertificateDataValid [3, 5, 7, 11] ((coreMetadataChunks561 4).map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValidChunk561_4
end Erdos883Verified
