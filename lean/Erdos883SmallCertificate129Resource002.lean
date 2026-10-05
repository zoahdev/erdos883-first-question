import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_2 :
    (List.ofFn coreChunks129_2).flatten =
      (coreData129.take (coreResources129 2).q).drop 16 := by
  decide +kernel

theorem coreCheck129_2 :
    ∀ c : Fin 1, (coreChunks129_2 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 2)) = true := by
  decide +kernel
#print axioms coreFlatten129_2
#print axioms coreCheck129_2
end Erdos883Verified
