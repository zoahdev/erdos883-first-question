import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_14 :
    (List.ofFn coreChunks212_14).flatten =
      (coreData212.take (coreResources212 14).q).drop 38 := by
  decide +kernel

theorem coreCheck212_14 :
    ∀ c : Fin 1, (coreChunks212_14 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 14)) = true := by
  decide +kernel
#print axioms coreFlatten212_14
#print axioms coreCheck212_14
end Erdos883Verified
