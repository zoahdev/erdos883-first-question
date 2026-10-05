import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_13 :
    (List.ofFn coreChunks129_13).flatten =
      (coreData129.take (coreResources129 13).q).drop 27 := by
  decide +kernel

theorem coreCheck129_13 :
    ∀ c : Fin 1, (coreChunks129_13 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 13)) = true := by
  decide +kernel
#print axioms coreFlatten129_13
#print axioms coreCheck129_13
end Erdos883Verified
