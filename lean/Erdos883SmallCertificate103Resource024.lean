import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_24 :
    (List.ofFn coreChunks103_24).flatten =
      (coreData103.take (coreResources103 24).q).drop 34 := by
  decide +kernel

theorem coreCheck103_24 :
    ∀ c : Fin 1, (coreChunks103_24 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 24)) = true := by
  decide +kernel
#print axioms coreFlatten103_24
#print axioms coreCheck103_24
end Erdos883Verified
