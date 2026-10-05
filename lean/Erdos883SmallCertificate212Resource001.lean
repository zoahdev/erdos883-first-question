import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_1 :
    (List.ofFn coreChunks212_1).flatten =
      (coreData212.take (coreResources212 1).q).drop 24 := by
  decide +kernel

theorem coreCheck212_1 :
    ∀ c : Fin 1, (coreChunks212_1 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 1)) = true := by
  decide +kernel
#print axioms coreFlatten212_1
#print axioms coreCheck212_1
end Erdos883Verified
