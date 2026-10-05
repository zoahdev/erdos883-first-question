import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_22 :
    (List.ofFn coreChunks103_22).flatten =
      (coreData103.take (coreResources103 22).q).drop 32 := by
  decide +kernel

theorem coreCheck103_22 :
    ∀ c : Fin 1, (coreChunks103_22 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 22)) = true := by
  decide +kernel
#print axioms coreFlatten103_22
#print axioms coreCheck103_22
end Erdos883Verified
