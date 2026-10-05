import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk1211_215_28 :
    (coreChunks1211_215 28).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 215)) = true := by
  decide +kernel
#print axioms coreCheckChunk1211_215_28
end Erdos883Verified
