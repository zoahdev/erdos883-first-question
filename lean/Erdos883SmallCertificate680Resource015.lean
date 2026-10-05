import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_15 :
    (List.ofFn coreChunks680_15).flatten =
      (coreData680.take (coreResources680 15).q).drop 130 := by
  decide +kernel

theorem coreCheck680_15 :
    ∀ c : Fin 1, (coreChunks680_15 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 15)) = true := by
  decide +kernel
#print axioms coreFlatten680_15
#print axioms coreCheck680_15
end Erdos883Verified
