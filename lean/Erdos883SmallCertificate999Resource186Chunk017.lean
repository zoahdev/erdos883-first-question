import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk999_186_17 :
    (coreChunks999_186 17).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 186)) = true := by
  decide +kernel
#print axioms coreCheckChunk999_186_17
end Erdos883Verified
