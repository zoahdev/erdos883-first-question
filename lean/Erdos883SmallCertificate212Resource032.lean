import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_32 :
    (List.ofFn coreChunks212_32).flatten =
      (coreData212.take (coreResources212 32).q).drop 67 := by
  decide +kernel

theorem coreCheck212_32 :
    ∀ c : Fin 1, (coreChunks212_32 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 32)) = true := by
  decide +kernel
#print axioms coreFlatten212_32
#print axioms coreCheck212_32
end Erdos883Verified
