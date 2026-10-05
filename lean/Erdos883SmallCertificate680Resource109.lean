import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_109 :
    (List.ofFn coreChunks680_109).flatten =
      (coreData680.take (coreResources680 109).q).drop 213 := by
  decide +kernel

theorem coreCheck680_109 :
    ∀ c : Fin 1, (coreChunks680_109 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 109)) = true := by
  decide +kernel
#print axioms coreFlatten680_109
#print axioms coreCheck680_109
end Erdos883Verified
