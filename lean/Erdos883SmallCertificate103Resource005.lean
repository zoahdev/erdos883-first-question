import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_5 :
    (List.ofFn coreChunks103_5).flatten =
      (coreData103.take (coreResources103 5).q).drop 14 := by
  decide +kernel

theorem coreCheck103_5 :
    ∀ c : Fin 1, (coreChunks103_5 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 5)) = true := by
  decide +kernel
#print axioms coreFlatten103_5
#print axioms coreCheck103_5
end Erdos883Verified
