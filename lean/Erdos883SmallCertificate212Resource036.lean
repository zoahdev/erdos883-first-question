import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_36 :
    (List.ofFn coreChunks212_36).flatten =
      (coreData212.take (coreResources212 36).q).drop 85 := by
  decide +kernel

theorem coreCheck212_36 :
    ∀ c : Fin 1, (coreChunks212_36 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 36)) = true := by
  decide +kernel
#print axioms coreFlatten212_36
#print axioms coreCheck212_36
end Erdos883Verified
