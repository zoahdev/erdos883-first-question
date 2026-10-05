import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk680_124_1 :
    (coreChunks680_124 1).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 124)) = true := by
  decide +kernel
#print axioms coreCheckChunk680_124_1
end Erdos883Verified
