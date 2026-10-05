import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_34 :
    (List.ofFn coreChunks212_34).flatten =
      (coreData212.take (coreResources212 34).q).drop 75 := by
  decide +kernel

theorem coreCheck212_34 :
    ∀ c : Fin 1, (coreChunks212_34 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 34)) = true := by
  decide +kernel
#print axioms coreFlatten212_34
#print axioms coreCheck212_34
end Erdos883Verified
