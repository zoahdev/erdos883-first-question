import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_19 :
    (List.ofFn coreChunks103_19).flatten =
      (coreData103.take (coreResources103 19).q).drop 45 := by
  decide +kernel

theorem coreCheck103_19 :
    ∀ c : Fin 1, (coreChunks103_19 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 19)) = true := by
  decide +kernel
#print axioms coreFlatten103_19
#print axioms coreCheck103_19
end Erdos883Verified
