import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_1 :
    (List.ofFn coreChunks680_1).flatten =
      (coreData680.take (coreResources680 1).q).drop 61 := by
  decide +kernel

theorem coreCheck680_1 :
    ∀ c : Fin 1, (coreChunks680_1 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 1)) = true := by
  decide +kernel
#print axioms coreFlatten680_1
#print axioms coreCheck680_1
end Erdos883Verified
