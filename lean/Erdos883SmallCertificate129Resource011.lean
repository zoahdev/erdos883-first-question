import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_11 :
    (List.ofFn coreChunks129_11).flatten =
      (coreData129.take (coreResources129 11).q).drop 25 := by
  decide +kernel

theorem coreCheck129_11 :
    ∀ c : Fin 1, (coreChunks129_11 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 11)) = true := by
  decide +kernel
#print axioms coreFlatten129_11
#print axioms coreCheck129_11
end Erdos883Verified
