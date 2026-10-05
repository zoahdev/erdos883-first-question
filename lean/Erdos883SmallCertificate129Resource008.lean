import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_8 :
    (List.ofFn coreChunks129_8).flatten =
      (coreData129.take (coreResources129 8).q).drop 22 := by
  decide +kernel

theorem coreCheck129_8 :
    ∀ c : Fin 1, (coreChunks129_8 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 8)) = true := by
  decide +kernel
#print axioms coreFlatten129_8
#print axioms coreCheck129_8
end Erdos883Verified
