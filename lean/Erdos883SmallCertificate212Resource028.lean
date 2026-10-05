import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_28 :
    (List.ofFn coreChunks212_28).flatten =
      (coreData212.take (coreResources212 28).q).drop 59 := by
  decide +kernel

theorem coreCheck212_28 :
    ∀ c : Fin 1, (coreChunks212_28 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 28)) = true := by
  decide +kernel
#print axioms coreFlatten212_28
#print axioms coreCheck212_28
end Erdos883Verified
