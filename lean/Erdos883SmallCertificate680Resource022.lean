import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_22 :
    (List.ofFn coreChunks680_22).flatten =
      (coreData680.take (coreResources680 22).q).drop 137 := by
  decide +kernel

theorem coreCheck680_22 :
    ∀ c : Fin 1, (coreChunks680_22 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 22)) = true := by
  decide +kernel
#print axioms coreFlatten680_22
#print axioms coreCheck680_22
end Erdos883Verified
