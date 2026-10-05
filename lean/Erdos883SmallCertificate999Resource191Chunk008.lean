import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk999_191_8 :
    (coreChunks999_191 8).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 191)) = true := by
  decide +kernel
#print axioms coreCheckChunk999_191_8
end Erdos883Verified
