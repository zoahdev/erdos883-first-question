import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_23 :
    (List.ofFn coreChunks212_23).flatten =
      (coreData212.take (coreResources212 23).q).drop 51 := by
  decide +kernel

theorem coreCheck212_23 :
    ∀ c : Fin 1, (coreChunks212_23 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 23)) = true := by
  decide +kernel
#print axioms coreFlatten212_23
#print axioms coreCheck212_23
end Erdos883Verified
