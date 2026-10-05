import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk749_145_11 :
    (coreChunks749_145 11).all
      (coreResourceRowCheck 681 coreData749 (coreResources749 145)) = true := by
  decide +kernel
#print axioms coreCheckChunk749_145_11
end Erdos883Verified
