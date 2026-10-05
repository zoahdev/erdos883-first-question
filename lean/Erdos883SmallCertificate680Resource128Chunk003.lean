import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk680_128_3 :
    (coreChunks680_128 3).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 128)) = true := by
  decide +kernel
#print axioms coreCheckChunk680_128_3
end Erdos883Verified
