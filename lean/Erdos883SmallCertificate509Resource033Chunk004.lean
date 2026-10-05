import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk509_33_4 :
    (coreChunks509_33 4).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 33)) = true := by
  decide +kernel
#print axioms coreCheckChunk509_33_4
end Erdos883Verified
