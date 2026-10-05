import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_3 :
    (List.ofFn coreChunks103_3).flatten =
      (coreData103.take (coreResources103 3).q).drop 0 := by
  decide +kernel

theorem coreCheck103_3 :
    ∀ c : Fin 1, (coreChunks103_3 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 3)) = true := by
  decide +kernel
#print axioms coreFlatten103_3
#print axioms coreCheck103_3
end Erdos883Verified
