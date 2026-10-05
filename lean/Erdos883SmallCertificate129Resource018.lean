import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_18 :
    (List.ofFn coreChunks129_18).flatten =
      (coreData129.take (coreResources129 18).q).drop 37 := by
  decide +kernel

theorem coreCheck129_18 :
    ∀ c : Fin 1, (coreChunks129_18 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 18)) = true := by
  decide +kernel
#print axioms coreFlatten129_18
#print axioms coreCheck129_18
end Erdos883Verified
