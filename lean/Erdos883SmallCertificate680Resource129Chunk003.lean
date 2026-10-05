import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk680_129_3 :
    (coreChunks680_129 3).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 129)) = true := by
  decide +kernel
#print axioms coreCheckChunk680_129_3
end Erdos883Verified
