import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_30 :
    (List.ofFn coreChunks212_30).flatten =
      (coreData212.take (coreResources212 30).q).drop 62 := by
  decide +kernel

theorem coreCheck212_30 :
    ∀ c : Fin 1, (coreChunks212_30 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 30)) = true := by
  decide +kernel
#print axioms coreFlatten212_30
#print axioms coreCheck212_30
end Erdos883Verified
