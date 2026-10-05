import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk158_34_1 :
    (coreChunks158_34 1).all
      (coreResourceRowCheck 144 coreData158 (coreResources158 34)) = true := by
  decide +kernel
#print axioms coreCheckChunk158_34_1
end Erdos883Verified
