import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_0 :
    (List.ofFn coreChunks129_0).flatten =
      (coreData129.take (coreResources129 0).q).drop 0 := by
  decide +kernel

theorem coreCheck129_0 :
    ∀ c : Fin 1, (coreChunks129_0 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 0)) = true := by
  decide +kernel
#print axioms coreFlatten129_0
#print axioms coreCheck129_0
end Erdos883Verified
