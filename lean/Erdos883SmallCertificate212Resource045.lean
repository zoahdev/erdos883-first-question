import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten212_45 :
    (List.ofFn coreChunks212_45).flatten =
      (coreData212.take (coreResources212 45).q).drop 60 := by
  decide +kernel

theorem coreCheck212_45 :
    ∀ c : Fin 1, (coreChunks212_45 c).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 45)) = true := by
  decide +kernel
#print axioms coreFlatten212_45
#print axioms coreCheck212_45
end Erdos883Verified
