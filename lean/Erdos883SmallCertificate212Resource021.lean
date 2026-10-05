import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_21 :
    (List.ofFn coreChunks212_21).flatten =
      (coreData212.take (coreResources212 21).q).drop 47 := by
  decide +kernel

theorem coreCheck212_21 :
    ∀ c : Fin 1, (coreChunks212_21 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 21)) = true := by
  decide +kernel
#print axioms coreFlatten212_21
#print axioms coreCheck212_21
end Erdos883Verified
