import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk749_146_13 :
    (coreChunks749_146 13).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 146)) = true := by
  decide +kernel
#print axioms coreCheckChunk749_146_13
end Erdos883Verified
