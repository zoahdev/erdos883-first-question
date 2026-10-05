import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk114_20_0 :
    (coreChunks114_20 0).all
      (coreResourceRowCheck 104 coreData114 (coreResources114 20)) = true := by
  decide +kernel
#print axioms coreCheckChunk114_20_0
end Erdos883Verified
