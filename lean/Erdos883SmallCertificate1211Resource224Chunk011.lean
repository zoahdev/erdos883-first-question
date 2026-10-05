import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk1211_224_11 :
    (coreChunks1211_224 11).all
      (coreResourceRowCheck 1101 coreData1211 (coreResources1211 224)) = true := by
  decide +kernel
#print axioms coreCheckChunk1211_224_11
end Erdos883Verified
