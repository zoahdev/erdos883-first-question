import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_41 :
    (List.ofFn coreChunks212_41).flatten =
      (coreData212.take (coreResources212 41).q).drop 68 := by
  decide +kernel

theorem coreCheck212_41 :
    ∀ c : Fin 1, (coreChunks212_41 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 41)) = true := by
  decide +kernel
#print axioms coreFlatten212_41
#print axioms coreCheck212_41
end Erdos883Verified
