import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_4 :
    (List.ofFn coreChunks212_4).flatten =
      (coreData212.take (coreResources212 4).q).drop 47 := by
  decide +kernel

theorem coreCheck212_4 :
    ∀ c : Fin 1, (coreChunks212_4 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 4)) = true := by
  decide +kernel
#print axioms coreFlatten212_4
#print axioms coreCheck212_4
end Erdos883Verified
