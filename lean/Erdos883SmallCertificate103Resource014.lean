import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_14 :
    (List.ofFn coreChunks103_14).flatten =
      (coreData103.take (coreResources103 14).q).drop 30 := by
  decide +kernel

theorem coreCheck103_14 :
    ∀ c : Fin 1, (coreChunks103_14 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 14)) = true := by
  decide +kernel
#print axioms coreFlatten103_14
#print axioms coreCheck103_14
end Erdos883Verified
