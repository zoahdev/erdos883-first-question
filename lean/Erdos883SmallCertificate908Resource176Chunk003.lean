import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk908_176_3 :
    (coreChunks908_176 3).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 176)) = true := by
  decide +kernel
#print axioms coreCheckChunk908_176_3
end Erdos883Verified
