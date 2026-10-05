import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk174_32_1 :
    (coreChunks174_32 1).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 32)) = true := by
  decide +kernel
#print axioms coreCheckChunk174_32_1
end Erdos883Verified
