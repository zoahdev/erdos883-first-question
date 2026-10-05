import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk749_143_14 :
    (coreChunks749_143 14).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 143)) = true := by
  decide +kernel
#print axioms coreCheckChunk749_143_14
end Erdos883Verified
