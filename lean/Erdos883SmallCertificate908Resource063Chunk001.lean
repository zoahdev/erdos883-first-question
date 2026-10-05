import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk908_63_1 :
    (coreChunks908_63 1).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 63)) = true := by
  decide +kernel
#print axioms coreCheckChunk908_63_1
end Erdos883Verified
