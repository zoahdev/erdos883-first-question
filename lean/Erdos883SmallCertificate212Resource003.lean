import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_3 :
    (List.ofFn coreChunks212_3).flatten =
      (coreData212.take (coreResources212 3).q).drop 29 := by
  decide +kernel

theorem coreCheck212_3 :
    ∀ c : Fin 2, (coreChunks212_3 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 3)) = true := by
  decide +kernel
#print axioms coreFlatten212_3
#print axioms coreCheck212_3
end Erdos883Verified
