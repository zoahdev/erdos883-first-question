import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_12 :
    (List.ofFn coreChunks129_12).flatten =
      (coreData129.take (coreResources129 12).q).drop 26 := by
  decide +kernel

theorem coreCheck129_12 :
    ∀ c : Fin 1, (coreChunks129_12 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 12)) = true := by
  decide +kernel
#print axioms coreFlatten129_12
#print axioms coreCheck129_12
end Erdos883Verified
