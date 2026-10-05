import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck1100_7 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks1100 7) = true := by
  decide +kernel
#print axioms coreMetadataCheck1100_7
end Erdos883Verified
