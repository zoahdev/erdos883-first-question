import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk999_192_7 :
    (coreChunks999_192 7).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 192)) = true := by
  decide +kernel
#print axioms coreCheckChunk999_192_7
end Erdos883Verified
