import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_18 :
    (List.ofFn coreChunks212_18).flatten =
      (coreData212.take (coreResources212 18).q).drop 42 := by
  decide +kernel

theorem coreCheck212_18 :
    ∀ c : Fin 1, (coreChunks212_18 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 18)) = true := by
  decide +kernel
#print axioms coreFlatten212_18
#print axioms coreCheck212_18
end Erdos883Verified
