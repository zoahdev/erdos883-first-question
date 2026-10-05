import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_44 :
    (List.ofFn coreChunks212_44).flatten =
      (coreData212.take (coreResources212 44).q).drop 58 := by
  decide +kernel

theorem coreCheck212_44 :
    ∀ c : Fin 1, (coreChunks212_44 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 44)) = true := by
  decide +kernel
#print axioms coreFlatten212_44
#print axioms coreCheck212_44
end Erdos883Verified
