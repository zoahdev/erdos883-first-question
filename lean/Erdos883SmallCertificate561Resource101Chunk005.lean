import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk561_101_5 :
    (coreChunks561_101 5).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 101)) = true := by
  decide +kernel
#print axioms coreCheckChunk561_101_5
end Erdos883Verified
