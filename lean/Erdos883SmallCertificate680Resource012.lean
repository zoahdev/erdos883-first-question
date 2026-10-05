import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_12 :
    (List.ofFn coreChunks680_12).flatten =
      (coreData680.take (coreResources680 12).q).drop 126 := by
  decide +kernel

theorem coreCheck680_12 :
    ∀ c : Fin 1, (coreChunks680_12 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 12)) = true := by
  decide +kernel
#print axioms coreFlatten680_12
#print axioms coreCheck680_12
end Erdos883Verified
