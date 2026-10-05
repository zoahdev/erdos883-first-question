import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_9 :
    (List.ofFn coreChunks680_9).flatten =
      (coreData680.take (coreResources680 9).q).drop 122 := by
  decide +kernel

theorem coreCheck680_9 :
    ∀ c : Fin 1, (coreChunks680_9 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 9)) = true := by
  decide +kernel
#print axioms coreFlatten680_9
#print axioms coreCheck680_9
end Erdos883Verified
