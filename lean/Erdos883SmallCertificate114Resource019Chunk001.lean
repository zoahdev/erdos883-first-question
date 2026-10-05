import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk114_19_1 :
    (coreChunks114_19 1).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 19)) = true := by
  decide +kernel
#print axioms coreCheckChunk114_19_1
end Erdos883Verified
