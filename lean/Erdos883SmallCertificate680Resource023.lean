import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_23 :
    (List.ofFn coreChunks680_23).flatten =
      (coreData680.take (coreResources680 23).q).drop 139 := by
  decide +kernel

theorem coreCheck680_23 :
    ∀ c : Fin 1, (coreChunks680_23 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 23)) = true := by
  decide +kernel
#print axioms coreFlatten680_23
#print axioms coreCheck680_23
end Erdos883Verified
