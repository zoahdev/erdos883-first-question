import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_14 :
    (List.ofFn coreChunks129_14).flatten =
      (coreData129.take (coreResources129 14).q).drop 29 := by
  decide +kernel

theorem coreCheck129_14 :
    ∀ c : Fin 1, (coreChunks129_14 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 14)) = true := by
  decide +kernel
#print axioms coreFlatten129_14
#print axioms coreCheck129_14
end Erdos883Verified
