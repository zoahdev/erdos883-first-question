import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_13 :
    (List.ofFn coreChunks212_13).flatten =
      (coreData212.take (coreResources212 13).q).drop 37 := by
  decide +kernel

theorem coreCheck212_13 :
    ∀ c : Fin 1, (coreChunks212_13 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 13)) = true := by
  decide +kernel
#print axioms coreFlatten212_13
#print axioms coreCheck212_13
end Erdos883Verified
