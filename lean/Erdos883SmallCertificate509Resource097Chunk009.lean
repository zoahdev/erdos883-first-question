import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk509_97_9 :
    (coreChunks509_97 9).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 97)) = true := by
  decide +kernel
#print axioms coreCheckChunk509_97_9
end Erdos883Verified
