import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_11 :
    (List.ofFn coreChunks212_11).flatten =
      (coreData212.take (coreResources212 11).q).drop 33 := by
  decide +kernel

theorem coreCheck212_11 :
    ∀ c : Fin 1, (coreChunks212_11 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 11)) = true := by
  decide +kernel
#print axioms coreFlatten212_11
#print axioms coreCheck212_11
end Erdos883Verified
