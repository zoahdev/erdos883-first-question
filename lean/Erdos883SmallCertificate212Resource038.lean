import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_38 :
    (List.ofFn coreChunks212_38).flatten =
      (coreData212.take (coreResources212 38).q).drop 103 := by
  decide +kernel

theorem coreCheck212_38 :
    ∀ c : Fin 1, (coreChunks212_38 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 38)) = true := by
  decide +kernel
#print axioms coreFlatten212_38
#print axioms coreCheck212_38
end Erdos883Verified
