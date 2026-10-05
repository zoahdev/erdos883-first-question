import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk1211_225_6 :
    (coreChunks1211_225 6).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 225)) = true := by
  decide +kernel
#print axioms coreCheckChunk1211_225_6
end Erdos883Verified
