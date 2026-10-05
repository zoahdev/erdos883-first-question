import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_3 :
    (List.ofFn coreChunks129_3).flatten =
      (coreData129.take (coreResources129 3).q).drop 18 := by
  decide +kernel

theorem coreCheck129_3 :
    ∀ c : Fin 1, (coreChunks129_3 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 3)) = true := by
  decide +kernel
#print axioms coreFlatten129_3
#print axioms coreCheck129_3
end Erdos883Verified
