import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk561_36_3 :
    (coreChunks561_36 3).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 36)) = true := by
  decide +kernel
#print axioms coreCheckChunk561_36_3
end Erdos883Verified
