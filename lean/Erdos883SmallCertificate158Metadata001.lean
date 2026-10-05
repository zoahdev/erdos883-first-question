import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck158_1 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks158 1) = true := by
  decide +kernel
#print axioms coreMetadataCheck158_1
end Erdos883Verified
