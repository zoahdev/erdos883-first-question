import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_5 :
    (List.ofFn coreChunks212_5).flatten =
      (coreData212.take (coreResources212 5).q).drop 50 := by
  decide +kernel

theorem coreCheck212_5 :
    ∀ c : Fin 1, (coreChunks212_5 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 5)) = true := by
  decide +kernel
#print axioms coreFlatten212_5
#print axioms coreCheck212_5
end Erdos883Verified
