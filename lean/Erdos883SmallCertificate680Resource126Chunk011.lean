import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk680_126_11 :
    (coreChunks680_126 11).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 126)) = true := by
  decide +kernel
#print axioms coreCheckChunk680_126_11
end Erdos883Verified
