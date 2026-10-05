import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_28 :
    (List.ofFn coreChunks129_28).flatten =
      (coreData129.take (coreResources129 28).q).drop 35 := by
  decide +kernel

theorem coreCheck129_28 :
    ∀ c : Fin 1, (coreChunks129_28 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 28)) = true := by
  decide +kernel
#print axioms coreFlatten129_28
#print axioms coreCheck129_28
end Erdos883Verified
