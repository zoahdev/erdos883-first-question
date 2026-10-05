import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_17 :
    (List.ofFn coreChunks212_17).flatten =
      (coreData212.take (coreResources212 17).q).drop 41 := by
  decide +kernel

theorem coreCheck212_17 :
    ∀ c : Fin 1, (coreChunks212_17 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 17)) = true := by
  decide +kernel
#print axioms coreFlatten212_17
#print axioms coreCheck212_17
end Erdos883Verified
