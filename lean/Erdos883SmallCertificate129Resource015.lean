import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_15 :
    (List.ofFn coreChunks129_15).flatten =
      (coreData129.take (coreResources129 15).q).drop 31 := by
  decide +kernel

theorem coreCheck129_15 :
    ∀ c : Fin 1, (coreChunks129_15 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 15)) = true := by
  decide +kernel
#print axioms coreFlatten129_15
#print axioms coreCheck129_15
end Erdos883Verified
