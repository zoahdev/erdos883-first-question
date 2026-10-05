import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_26 :
    (List.ofFn coreChunks212_26).flatten =
      (coreData212.take (coreResources212 26).q).drop 55 := by
  decide +kernel

theorem coreCheck212_26 :
    ∀ c : Fin 1, (coreChunks212_26 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 26)) = true := by
  decide +kernel
#print axioms coreFlatten212_26
#print axioms coreCheck212_26
end Erdos883Verified
