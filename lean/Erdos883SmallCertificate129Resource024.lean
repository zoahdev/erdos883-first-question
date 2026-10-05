import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_24 :
    (List.ofFn coreChunks129_24).flatten =
      (coreData129.take (coreResources129 24).q).drop 55 := by
  decide +kernel

theorem coreCheck129_24 :
    ∀ c : Fin 1, (coreChunks129_24 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 24)) = true := by
  decide +kernel
#print axioms coreFlatten129_24
#print axioms coreCheck129_24
end Erdos883Verified
