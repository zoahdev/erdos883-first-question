import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_7 :
    (List.ofFn coreChunks103_7).flatten =
      (coreData103.take (coreResources103 7).q).drop 20 := by
  decide +kernel

theorem coreCheck103_7 :
    ∀ c : Fin 1, (coreChunks103_7 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 7)) = true := by
  decide +kernel
#print axioms coreFlatten103_7
#print axioms coreCheck103_7
end Erdos883Verified
