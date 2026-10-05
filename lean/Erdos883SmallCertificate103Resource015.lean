import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_15 :
    (List.ofFn coreChunks103_15).flatten =
      (coreData103.take (coreResources103 15).q).drop 32 := by
  decide +kernel

theorem coreCheck103_15 :
    ∀ c : Fin 1, (coreChunks103_15 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 15)) = true := by
  decide +kernel
#print axioms coreFlatten103_15
#print axioms coreCheck103_15
end Erdos883Verified
