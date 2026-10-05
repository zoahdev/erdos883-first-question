import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_18 :
    (List.ofFn coreChunks103_18).flatten =
      (coreData103.take (coreResources103 18).q).drop 41 := by
  decide +kernel

theorem coreCheck103_18 :
    ∀ c : Fin 1, (coreChunks103_18 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 18)) = true := by
  decide +kernel
#print axioms coreFlatten103_18
#print axioms coreCheck103_18
end Erdos883Verified
