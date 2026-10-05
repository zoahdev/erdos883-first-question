import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk680_44_5 :
    (coreChunks680_44 5).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 44)) = true := by
  decide +kernel
#print axioms coreCheckChunk680_44_5
end Erdos883Verified
