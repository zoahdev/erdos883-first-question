import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_7 :
    (List.ofFn coreChunks129_7).flatten =
      (coreData129.take (coreResources129 7).q).drop 16 := by
  decide +kernel

theorem coreCheck129_7 :
    ∀ c : Fin 1, (coreChunks129_7 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 7)) = true := by
  decide +kernel
#print axioms coreFlatten129_7
#print axioms coreCheck129_7
end Erdos883Verified
