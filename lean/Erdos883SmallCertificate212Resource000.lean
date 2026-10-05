import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_0 :
    (List.ofFn coreChunks212_0).flatten =
      (coreData212.take (coreResources212 0).q).drop 0 := by
  decide +kernel

theorem coreCheck212_0 :
    ∀ c : Fin 2, (coreChunks212_0 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 0)) = true := by
  decide +kernel
#print axioms coreFlatten212_0
#print axioms coreCheck212_0
end Erdos883Verified
