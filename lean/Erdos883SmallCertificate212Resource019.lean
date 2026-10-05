import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_19 :
    (List.ofFn coreChunks212_19).flatten =
      (coreData212.take (coreResources212 19).q).drop 44 := by
  decide +kernel

theorem coreCheck212_19 :
    ∀ c : Fin 1, (coreChunks212_19 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 19)) = true := by
  decide +kernel
#print axioms coreFlatten212_19
#print axioms coreCheck212_19
end Erdos883Verified
