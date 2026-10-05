import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_2 :
    (List.ofFn coreChunks212_2).flatten =
      (coreData212.take (coreResources212 2).q).drop 25 := by
  decide +kernel

theorem coreCheck212_2 :
    ∀ c : Fin 1, (coreChunks212_2 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 2)) = true := by
  decide +kernel
#print axioms coreFlatten212_2
#print axioms coreCheck212_2
end Erdos883Verified
