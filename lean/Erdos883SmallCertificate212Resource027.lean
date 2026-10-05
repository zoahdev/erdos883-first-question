import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_27 :
    (List.ofFn coreChunks212_27).flatten =
      (coreData212.take (coreResources212 27).q).drop 58 := by
  decide +kernel

theorem coreCheck212_27 :
    ∀ c : Fin 1, (coreChunks212_27 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 27)) = true := by
  decide +kernel
#print axioms coreFlatten212_27
#print axioms coreCheck212_27
end Erdos883Verified
