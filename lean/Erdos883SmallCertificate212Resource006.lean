import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_6 :
    (List.ofFn coreChunks212_6).flatten =
      (coreData212.take (coreResources212 6).q).drop 51 := by
  decide +kernel

theorem coreCheck212_6 :
    ∀ c : Fin 1, (coreChunks212_6 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 6)) = true := by
  decide +kernel
#print axioms coreFlatten212_6
#print axioms coreCheck212_6
end Erdos883Verified
