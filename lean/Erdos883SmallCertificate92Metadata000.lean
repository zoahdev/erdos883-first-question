import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck92_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks92 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck92_0
end Erdos883Verified
