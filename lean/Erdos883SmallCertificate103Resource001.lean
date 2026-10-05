import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_1 :
    (List.ofFn coreChunks103_1).flatten =
      (coreData103.take (coreResources103 1).q).drop 13 := by
  decide +kernel

theorem coreCheck103_1 :
    ∀ c : Fin 1, (coreChunks103_1 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 1)) = true := by
  decide +kernel
#print axioms coreFlatten103_1
#print axioms coreCheck103_1
end Erdos883Verified
