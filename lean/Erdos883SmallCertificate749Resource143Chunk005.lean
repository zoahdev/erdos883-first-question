import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk749_143_5 :
    (coreChunks749_143 5).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 143)) = true := by
  decide +kernel
#print axioms coreCheckChunk749_143_5
end Erdos883Verified
