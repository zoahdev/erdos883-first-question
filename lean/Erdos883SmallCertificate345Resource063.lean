import Erdos883SmallCertificate345Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten345_63 :
    (List.ofFn coreChunks345_63).flatten =
      (coreData345.take (coreResources345 63).q).drop 150 := by
  decide +kernel

theorem coreCheck345_63 :
    ∀ c : Fin 1, (coreChunks345_63 c).all
      (coreResourceRowCheck 314 coreData345 (coreResources345 63)) = true := by
  decide +kernel
#print axioms coreFlatten345_63
#print axioms coreCheck345_63
end Erdos883Verified
