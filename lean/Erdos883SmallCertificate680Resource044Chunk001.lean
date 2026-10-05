import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk680_44_1 :
    (coreChunks680_44 1).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 44)) = true := by
  decide +kernel
#print axioms coreCheckChunk680_44_1
end Erdos883Verified
