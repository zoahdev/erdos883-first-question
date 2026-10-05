import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_22 :
    (List.ofFn coreChunks212_22).flatten =
      (coreData212.take (coreResources212 22).q).drop 50 := by
  decide +kernel

theorem coreCheck212_22 :
    ∀ c : Fin 1, (coreChunks212_22 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 22)) = true := by
  decide +kernel
#print axioms coreFlatten212_22
#print axioms coreCheck212_22
end Erdos883Verified
