import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_42 :
    (List.ofFn coreChunks212_42).flatten =
      (coreData212.take (coreResources212 42).q).drop 69 := by
  decide +kernel

theorem coreCheck212_42 :
    ∀ c : Fin 1, (coreChunks212_42 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 42)) = true := by
  decide +kernel
#print axioms coreFlatten212_42
#print axioms coreCheck212_42
end Erdos883Verified
