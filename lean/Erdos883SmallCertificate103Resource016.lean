import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_16 :
    (List.ofFn coreChunks103_16).flatten =
      (coreData103.take (coreResources103 16).q).drop 35 := by
  decide +kernel

theorem coreCheck103_16 :
    ∀ c : Fin 1, (coreChunks103_16 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 16)) = true := by
  decide +kernel
#print axioms coreFlatten103_16
#print axioms coreCheck103_16
end Erdos883Verified
