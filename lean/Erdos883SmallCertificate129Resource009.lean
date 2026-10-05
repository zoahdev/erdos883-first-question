import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_9 :
    (List.ofFn coreChunks129_9).flatten =
      (coreData129.take (coreResources129 9).q).drop 23 := by
  decide +kernel

theorem coreCheck129_9 :
    ∀ c : Fin 1, (coreChunks129_9 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 9)) = true := by
  decide +kernel
#print axioms coreFlatten129_9
#print axioms coreCheck129_9
end Erdos883Verified
