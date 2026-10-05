import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_21 :
    (List.ofFn coreChunks103_21).flatten =
      (coreData103.take (coreResources103 21).q).drop 0 := by
  decide +kernel

theorem coreCheck103_21 :
    ∀ c : Fin 2, (coreChunks103_21 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 21)) = true := by
  decide +kernel
#print axioms coreFlatten103_21
#print axioms coreCheck103_21
end Erdos883Verified
