import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk561_106_7 :
    (coreChunks561_106 7).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 106)) = true := by
  decide +kernel
#print axioms coreCheckChunk561_106_7
end Erdos883Verified
