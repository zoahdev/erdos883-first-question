import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_0 :
    (List.ofFn coreChunks103_0).flatten =
      (coreData103.take (coreResources103 0).q).drop 0 := by
  decide +kernel

theorem coreCheck103_0 :
    ∀ c : Fin 1, (coreChunks103_0 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 0)) = true := by
  decide +kernel
#print axioms coreFlatten103_0
#print axioms coreCheck103_0
end Erdos883Verified
