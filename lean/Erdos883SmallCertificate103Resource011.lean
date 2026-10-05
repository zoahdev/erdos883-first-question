import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten103_11 :
    (List.ofFn coreChunks103_11).flatten =
      (coreData103.take (coreResources103 11).q).drop 26 := by
  decide +kernel

theorem coreCheck103_11 :
    ∀ c : Fin 1, (coreChunks103_11 c).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 11)) = true := by
  decide +kernel
#print axioms coreFlatten103_11
#print axioms coreCheck103_11
end Erdos883Verified
