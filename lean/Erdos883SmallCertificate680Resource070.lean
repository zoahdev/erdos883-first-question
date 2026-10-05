import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_70 :
    (List.ofFn coreChunks680_70).flatten =
      (coreData680.take (coreResources680 70).q).drop 131 := by
  decide +kernel

theorem coreCheck680_70 :
    ∀ c : Fin 1, (coreChunks680_70 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 70)) = true := by
  decide +kernel
#print axioms coreFlatten680_70
#print axioms coreCheck680_70
end Erdos883Verified
