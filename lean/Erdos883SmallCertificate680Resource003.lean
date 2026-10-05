import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_3 :
    (List.ofFn coreChunks680_3).flatten =
      (coreData680.take (coreResources680 3).q).drop 78 := by
  decide +kernel

theorem coreCheck680_3 :
    ∀ c : Fin 1, (coreChunks680_3 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 3)) = true := by
  decide +kernel
#print axioms coreFlatten680_3
#print axioms coreCheck680_3
end Erdos883Verified
