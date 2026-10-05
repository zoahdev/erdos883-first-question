import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_66 :
    (List.ofFn coreChunks680_66).flatten =
      (coreData680.take (coreResources680 66).q).drop 126 := by
  decide +kernel

theorem coreCheck680_66 :
    ∀ c : Fin 1, (coreChunks680_66 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 66)) = true := by
  decide +kernel
#print axioms coreFlatten680_66
#print axioms coreCheck680_66
end Erdos883Verified
