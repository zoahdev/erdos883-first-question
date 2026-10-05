import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_15 :
    (List.ofFn coreChunks212_15).flatten =
      (coreData212.take (coreResources212 15).q).drop 39 := by
  decide +kernel

theorem coreCheck212_15 :
    ∀ c : Fin 1, (coreChunks212_15 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 15)) = true := by
  decide +kernel
#print axioms coreFlatten212_15
#print axioms coreCheck212_15
end Erdos883Verified
