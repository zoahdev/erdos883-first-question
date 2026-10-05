import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk749_0_3 :
    (coreChunks749_0 3).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 0)) = true := by
  decide +kernel
#print axioms coreCheckChunk749_0_3
end Erdos883Verified
