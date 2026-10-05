import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_41 :
    (List.ofFn coreChunks680_41).flatten =
      (coreData680.take (coreResources680 41).q).drop 165 := by
  decide +kernel

theorem coreCheck680_41 :
    ∀ c : Fin 1, (coreChunks680_41 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 41)) = true := by
  decide +kernel
#print axioms coreFlatten680_41
#print axioms coreCheck680_41
end Erdos883Verified
