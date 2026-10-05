import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_1 :
    (List.ofFn coreChunks129_1).flatten =
      (coreData129.take (coreResources129 1).q).drop 15 := by
  decide +kernel

theorem coreCheck129_1 :
    ∀ c : Fin 1, (coreChunks129_1 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 1)) = true := by
  decide +kernel
#print axioms coreFlatten129_1
#print axioms coreCheck129_1
end Erdos883Verified
