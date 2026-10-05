import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten129_29 :
    (List.ofFn coreChunks129_29).flatten =
      (coreData129.take (coreResources129 29).q).drop 40 := by
  decide +kernel

theorem coreCheck129_29 :
    ∀ c : Fin 1, (coreChunks129_29 c).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 29)) = true := by
  decide +kernel
#print axioms coreFlatten129_29
#print axioms coreCheck129_29
end Erdos883Verified
