import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_24 :
    (List.ofFn coreChunks212_24).flatten =
      (coreData212.take (coreResources212 24).q).drop 52 := by
  decide +kernel

theorem coreCheck212_24 :
    ∀ c : Fin 1, (coreChunks212_24 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 24)) = true := by
  decide +kernel
#print axioms coreFlatten212_24
#print axioms coreCheck212_24
end Erdos883Verified
