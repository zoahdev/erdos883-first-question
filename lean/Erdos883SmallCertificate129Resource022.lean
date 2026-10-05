import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_22 :
    (List.ofFn coreChunks129_22).flatten =
      (coreData129.take (coreResources129 22).q).drop 47 := by
  decide +kernel

theorem coreCheck129_22 :
    ∀ c : Fin 1, (coreChunks129_22 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 22)) = true := by
  decide +kernel
#print axioms coreFlatten129_22
#print axioms coreCheck129_22
end Erdos883Verified
