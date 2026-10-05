import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_10 :
    (List.ofFn coreChunks212_10).flatten =
      (coreData212.take (coreResources212 10).q).drop 25 := by
  decide +kernel

theorem coreCheck212_10 :
    ∀ c : Fin 1, (coreChunks212_10 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 10)) = true := by
  decide +kernel
#print axioms coreFlatten212_10
#print axioms coreCheck212_10
end Erdos883Verified
