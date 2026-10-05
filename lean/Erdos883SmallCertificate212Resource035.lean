import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_35 :
    (List.ofFn coreChunks212_35).flatten =
      (coreData212.take (coreResources212 35).q).drop 79 := by
  decide +kernel

theorem coreCheck212_35 :
    ∀ c : Fin 1, (coreChunks212_35 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 35)) = true := by
  decide +kernel
#print axioms coreFlatten212_35
#print axioms coreCheck212_35
end Erdos883Verified
