import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_12 :
    (List.ofFn coreChunks212_12).flatten =
      (coreData212.take (coreResources212 12).q).drop 34 := by
  decide +kernel

theorem coreCheck212_12 :
    ∀ c : Fin 1, (coreChunks212_12 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 12)) = true := by
  decide +kernel
#print axioms coreFlatten212_12
#print axioms coreCheck212_12
end Erdos883Verified
