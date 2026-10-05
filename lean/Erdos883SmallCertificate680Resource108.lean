import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_108 :
    (List.ofFn coreChunks680_108).flatten =
      (coreData680.take (coreResources680 108).q).drop 211 := by
  decide +kernel

theorem coreCheck680_108 :
    ∀ c : Fin 1, (coreChunks680_108 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 108)) = true := by
  decide +kernel
#print axioms coreFlatten680_108
#print axioms coreCheck680_108
end Erdos883Verified
