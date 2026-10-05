import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_4 :
    (List.ofFn coreChunks103_4).flatten =
      (coreData103.take (coreResources103 4).q).drop 13 := by
  decide +kernel

theorem coreCheck103_4 :
    ∀ c : Fin 1, (coreChunks103_4 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 4)) = true := by
  decide +kernel
#print axioms coreFlatten103_4
#print axioms coreCheck103_4
end Erdos883Verified
