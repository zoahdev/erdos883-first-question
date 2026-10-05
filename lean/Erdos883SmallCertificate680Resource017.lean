import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_17 :
    (List.ofFn coreChunks680_17).flatten =
      (coreData680.take (coreResources680 17).q).drop 132 := by
  decide +kernel

theorem coreCheck680_17 :
    ∀ c : Fin 1, (coreChunks680_17 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 17)) = true := by
  decide +kernel
#print axioms coreFlatten680_17
#print axioms coreCheck680_17
end Erdos883Verified
