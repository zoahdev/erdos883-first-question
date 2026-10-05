import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_25 :
    (List.ofFn coreChunks212_25).flatten =
      (coreData212.take (coreResources212 25).q).drop 53 := by
  decide +kernel

theorem coreCheck212_25 :
    ∀ c : Fin 1, (coreChunks212_25 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 25)) = true := by
  decide +kernel
#print axioms coreFlatten212_25
#print axioms coreCheck212_25
end Erdos883Verified
