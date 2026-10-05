import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_21 :
    (List.ofFn coreChunks129_21).flatten =
      (coreData129.take (coreResources129 21).q).drop 43 := by
  decide +kernel

theorem coreCheck129_21 :
    ∀ c : Fin 1, (coreChunks129_21 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 21)) = true := by
  decide +kernel
#print axioms coreFlatten129_21
#print axioms coreCheck129_21
end Erdos883Verified
