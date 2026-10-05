import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_4 :
    (List.ofFn coreChunks129_4).flatten =
      (coreData129.take (coreResources129 4).q).drop 32 := by
  decide +kernel

theorem coreCheck129_4 :
    ∀ c : Fin 1, (coreChunks129_4 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 4)) = true := by
  decide +kernel
#print axioms coreFlatten129_4
#print axioms coreCheck129_4
end Erdos883Verified
