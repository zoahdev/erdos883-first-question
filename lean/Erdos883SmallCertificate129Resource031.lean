import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_31 :
    (List.ofFn coreChunks129_31).flatten =
      (coreData129.take (coreResources129 31).q).drop 42 := by
  decide +kernel

theorem coreCheck129_31 :
    ∀ c : Fin 1, (coreChunks129_31 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 31)) = true := by
  decide +kernel
#print axioms coreFlatten129_31
#print axioms coreCheck129_31
end Erdos883Verified
