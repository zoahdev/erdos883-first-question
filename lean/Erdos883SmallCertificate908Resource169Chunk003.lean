import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk908_169_3 :
    (coreChunks908_169 3).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 169)) = true := by
  decide +kernel
#print axioms coreCheckChunk908_169_3
end Erdos883Verified
