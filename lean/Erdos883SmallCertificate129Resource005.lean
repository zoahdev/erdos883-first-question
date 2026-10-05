import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_5 :
    (List.ofFn coreChunks129_5).flatten =
      (coreData129.take (coreResources129 5).q).drop 0 := by
  decide +kernel

theorem coreCheck129_5 :
    ∀ c : Fin 1, (coreChunks129_5 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 5)) = true := by
  decide +kernel
#print axioms coreFlatten129_5
#print axioms coreCheck129_5
end Erdos883Verified
