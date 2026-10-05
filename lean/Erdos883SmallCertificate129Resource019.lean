import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_19 :
    (List.ofFn coreChunks129_19).flatten =
      (coreData129.take (coreResources129 19).q).drop 38 := by
  decide +kernel

theorem coreCheck129_19 :
    ∀ c : Fin 1, (coreChunks129_19 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 19)) = true := by
  decide +kernel
#print axioms coreFlatten129_19
#print axioms coreCheck129_19
end Erdos883Verified
