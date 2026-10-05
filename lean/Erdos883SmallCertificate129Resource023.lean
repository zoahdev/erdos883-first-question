import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_23 :
    (List.ofFn coreChunks129_23).flatten =
      (coreData129.take (coreResources129 23).q).drop 51 := by
  decide +kernel

theorem coreCheck129_23 :
    ∀ c : Fin 1, (coreChunks129_23 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 23)) = true := by
  decide +kernel
#print axioms coreFlatten129_23
#print axioms coreCheck129_23
end Erdos883Verified
