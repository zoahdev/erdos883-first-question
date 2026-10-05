import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk174_31_0 :
    (coreChunks174_31 0).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 31)) = true := by
  decide +kernel
#print axioms coreCheckChunk174_31_0
end Erdos883Verified
