import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk999_0_5 :
    (coreChunks999_0 5).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 0)) = true := by
  decide +kernel
#print axioms coreCheckChunk999_0_5
end Erdos883Verified
