import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck103_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks103 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck103_0
end Erdos883Verified
