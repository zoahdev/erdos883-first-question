import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_37 :
    (List.ofFn coreChunks212_37).flatten =
      (coreData212.take (coreResources212 37).q).drop 93 := by
  decide +kernel

theorem coreCheck212_37 :
    ∀ c : Fin 1, (coreChunks212_37 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 37)) = true := by
  decide +kernel
#print axioms coreFlatten212_37
#print axioms coreCheck212_37
end Erdos883Verified
