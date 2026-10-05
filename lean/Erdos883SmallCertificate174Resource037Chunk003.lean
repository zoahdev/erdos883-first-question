import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk174_37_3 :
    (coreChunks174_37 3).all
      (coreResourceRowCheck 159 coreData174 (coreResources174 37)) = true := by
  decide +kernel
#print axioms coreCheckChunk174_37_3
end Erdos883Verified
