import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_23 :
    (List.ofFn coreChunks103_23).flatten =
      (coreData103.take (coreResources103 23).q).drop 33 := by
  decide +kernel

theorem coreCheck103_23 :
    ∀ c : Fin 1, (coreChunks103_23 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 23)) = true := by
  decide +kernel
#print axioms coreFlatten103_23
#print axioms coreCheck103_23
end Erdos883Verified
