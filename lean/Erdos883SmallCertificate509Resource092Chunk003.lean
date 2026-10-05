import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk509_92_3 :
    (coreChunks509_92 3).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 92)) = true := by
  decide +kernel
#print axioms coreCheckChunk509_92_3
end Erdos883Verified
