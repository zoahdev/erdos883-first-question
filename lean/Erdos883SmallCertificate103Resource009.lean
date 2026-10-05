import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_9 :
    (List.ofFn coreChunks103_9).flatten =
      (coreData103.take (coreResources103 9).q).drop 23 := by
  decide +kernel

theorem coreCheck103_9 :
    ∀ c : Fin 1, (coreChunks103_9 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 9)) = true := by
  decide +kernel
#print axioms coreFlatten103_9
#print axioms coreCheck103_9
end Erdos883Verified
