import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck192_1 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks192 1) = true := by
  decide +kernel
#print axioms coreMetadataCheck192_1
end Erdos883Verified
