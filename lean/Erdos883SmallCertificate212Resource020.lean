import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_20 :
    (List.ofFn coreChunks212_20).flatten =
      (coreData212.take (coreResources212 20).q).drop 46 := by
  decide +kernel

theorem coreCheck212_20 :
    ∀ c : Fin 1, (coreChunks212_20 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 20)) = true := by
  decide +kernel
#print axioms coreFlatten212_20
#print axioms coreCheck212_20
end Erdos883Verified
