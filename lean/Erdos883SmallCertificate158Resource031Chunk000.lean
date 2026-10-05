import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk158_31_0 :
    (coreChunks158_31 0).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 31)) = true := by
  decide +kernel
#print axioms coreCheckChunk158_31_0
end Erdos883Verified
