import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_10 :
    (List.ofFn coreChunks129_10).flatten =
      (coreData129.take (coreResources129 10).q).drop 24 := by
  decide +kernel

theorem coreCheck129_10 :
    ∀ c : Fin 1, (coreChunks129_10 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 10)) = true := by
  decide +kernel
#print axioms coreFlatten129_10
#print axioms coreCheck129_10
end Erdos883Verified
