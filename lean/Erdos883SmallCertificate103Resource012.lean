import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_12 :
    (List.ofFn coreChunks103_12).flatten =
      (coreData103.take (coreResources103 12).q).drop 28 := by
  decide +kernel

theorem coreCheck103_12 :
    ∀ c : Fin 1, (coreChunks103_12 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 12)) = true := by
  decide +kernel
#print axioms coreFlatten103_12
#print axioms coreCheck103_12
end Erdos883Verified
