import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck158_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks158 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck158_0
end Erdos883Verified
