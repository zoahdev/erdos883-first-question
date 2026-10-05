import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk680_125_6 :
    (coreChunks680_125 6).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 125)) = true := by
  decide +kernel
#print axioms coreCheckChunk680_125_6
end Erdos883Verified
