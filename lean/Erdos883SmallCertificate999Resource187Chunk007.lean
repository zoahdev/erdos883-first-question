import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk999_187_7 :
    (coreChunks999_187 7).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 187)) = true := by
  decide +kernel
#print axioms coreCheckChunk999_187_7
end Erdos883Verified
