import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_6 :
    (List.ofFn coreChunks103_6).flatten =
      (coreData103.take (coreResources103 6).q).drop 19 := by
  decide +kernel

theorem coreCheck103_6 :
    ∀ c : Fin 1, (coreChunks103_6 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 6)) = true := by
  decide +kernel
#print axioms coreFlatten103_6
#print axioms coreCheck103_6
end Erdos883Verified
