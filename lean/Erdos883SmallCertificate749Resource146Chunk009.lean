import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk749_146_9 :
    (coreChunks749_146 9).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 146)) = true := by
  decide +kernel
#print axioms coreCheckChunk749_146_9
end Erdos883Verified
