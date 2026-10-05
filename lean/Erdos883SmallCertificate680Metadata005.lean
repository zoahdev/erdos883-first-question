import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck680_5 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks680 5) = true := by
  decide +kernel
#print axioms coreMetadataCheck680_5
end Erdos883Verified
