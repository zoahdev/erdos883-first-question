import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_10 :
    (List.ofFn coreChunks103_10).flatten =
      (coreData103.take (coreResources103 10).q).drop 24 := by
  decide +kernel

theorem coreCheck103_10 :
    ∀ c : Fin 1, (coreChunks103_10 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 10)) = true := by
  decide +kernel
#print axioms coreFlatten103_10
#print axioms coreCheck103_10
end Erdos883Verified
