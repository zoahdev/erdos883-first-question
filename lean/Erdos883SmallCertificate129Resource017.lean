import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_17 :
    (List.ofFn coreChunks129_17).flatten =
      (coreData129.take (coreResources129 17).q).drop 35 := by
  decide +kernel

theorem coreCheck129_17 :
    ∀ c : Fin 1, (coreChunks129_17 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 17)) = true := by
  decide +kernel
#print axioms coreFlatten129_17
#print axioms coreCheck129_17
end Erdos883Verified
