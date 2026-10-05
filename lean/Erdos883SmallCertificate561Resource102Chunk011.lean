import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk561_102_11 :
    (coreChunks561_102 11).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 102)) = true := by
  decide +kernel
#print axioms coreCheckChunk561_102_11
end Erdos883Verified
