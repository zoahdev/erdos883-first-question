import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck618_2 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks618 2) = true := by
  decide +kernel
#print axioms coreMetadataCheck618_2
end Erdos883Verified
