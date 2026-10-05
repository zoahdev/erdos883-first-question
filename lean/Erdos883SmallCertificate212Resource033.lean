import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_33 :
    (List.ofFn coreChunks212_33).flatten =
      (coreData212.take (coreResources212 33).q).drop 71 := by
  decide +kernel

theorem coreCheck212_33 :
    ∀ c : Fin 1, (coreChunks212_33 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 33)) = true := by
  decide +kernel
#print axioms coreFlatten212_33
#print axioms coreCheck212_33
end Erdos883Verified
