import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk999_192_6 :
    (coreChunks999_192 6).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 192)) = true := by
  decide +kernel
#print axioms coreCheckChunk999_192_6
end Erdos883Verified
