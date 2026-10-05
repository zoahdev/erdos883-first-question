import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_17 :
    (List.ofFn coreChunks103_17).flatten =
      (coreData103.take (coreResources103 17).q).drop 39 := by
  decide +kernel

theorem coreCheck103_17 :
    ∀ c : Fin 1, (coreChunks103_17 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 17)) = true := by
  decide +kernel
#print axioms coreFlatten103_17
#print axioms coreCheck103_17
end Erdos883Verified
