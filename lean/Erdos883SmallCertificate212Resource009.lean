import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_9 :
    (List.ofFn coreChunks212_9).flatten =
      (coreData212.take (coreResources212 9).q).drop 24 := by
  decide +kernel

theorem coreCheck212_9 :
    ∀ c : Fin 1, (coreChunks212_9 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 9)) = true := by
  decide +kernel
#print axioms coreFlatten212_9
#print axioms coreCheck212_9
end Erdos883Verified
