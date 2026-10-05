import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_32 :
    (List.ofFn coreChunks345_32).flatten =
      (coreData345.take (coreResources345 32).q).drop 64 := by
  decide +kernel

theorem coreCheck345_32 :
    ∀ c : Fin 1, (coreChunks345_32 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 32)) = true := by
  decide +kernel
#print axioms coreFlatten345_32
#print axioms coreCheck345_32
end Erdos883Verified
