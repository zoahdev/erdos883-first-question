import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_8 :
    (List.ofFn coreChunks103_8).flatten =
      (coreData103.take (coreResources103 8).q).drop 22 := by
  decide +kernel

theorem coreCheck103_8 :
    ∀ c : Fin 1, (coreChunks103_8 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 8)) = true := by
  decide +kernel
#print axioms coreFlatten103_8
#print axioms coreCheck103_8
end Erdos883Verified
