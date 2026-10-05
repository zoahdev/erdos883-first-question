import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_31 :
    (List.ofFn coreChunks212_31).flatten =
      (coreData212.take (coreResources212 31).q).drop 64 := by
  decide +kernel

theorem coreCheck212_31 :
    ∀ c : Fin 1, (coreChunks212_31 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 31)) = true := by
  decide +kernel
#print axioms coreFlatten212_31
#print axioms coreCheck212_31
end Erdos883Verified
