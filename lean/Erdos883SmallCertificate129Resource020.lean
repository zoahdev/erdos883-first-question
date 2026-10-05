import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_20 :
    (List.ofFn coreChunks129_20).flatten =
      (coreData129.take (coreResources129 20).q).drop 40 := by
  decide +kernel

theorem coreCheck129_20 :
    ∀ c : Fin 1, (coreChunks129_20 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 20)) = true := by
  decide +kernel
#print axioms coreFlatten129_20
#print axioms coreCheck129_20
end Erdos883Verified
