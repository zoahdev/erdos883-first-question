import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_120 :
    (List.ofFn coreChunks680_120).flatten =
      (coreData680.take (coreResources680 120).q).drop 285 := by
  decide +kernel

theorem coreCheck680_120 :
    ∀ c : Fin 1, (coreChunks680_120 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 120)) = true := by
  decide +kernel
#print axioms coreFlatten680_120
#print axioms coreCheck680_120
end Erdos883Verified
