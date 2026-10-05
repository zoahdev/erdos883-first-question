import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_7 :
    (List.ofFn coreChunks212_7).flatten =
      (coreData212.take (coreResources212 7).q).drop 52 := by
  decide +kernel

theorem coreCheck212_7 :
    ∀ c : Fin 1, (coreChunks212_7 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 7)) = true := by
  decide +kernel
#print axioms coreFlatten212_7
#print axioms coreCheck212_7
end Erdos883Verified
