import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk749_142_14 :
    (coreChunks749_142 14).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 142)) = true := by
  decide +kernel
#print axioms coreCheckChunk749_142_14
end Erdos883Verified
