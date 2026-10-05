import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_13 :
    (List.ofFn coreChunks103_13).flatten =
      (coreData103.take (coreResources103 13).q).drop 29 := by
  decide +kernel

theorem coreCheck103_13 :
    ∀ c : Fin 1, (coreChunks103_13 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 13)) = true := by
  decide +kernel
#print axioms coreFlatten103_13
#print axioms coreCheck103_13
end Erdos883Verified
