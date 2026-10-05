import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_102 :
    (List.ofFn coreChunks680_102).flatten =
      (coreData680.take (coreResources680 102).q).drop 195 := by
  decide +kernel

theorem coreCheck680_102 :
    ∀ c : Fin 1, (coreChunks680_102 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 102)) = true := by
  decide +kernel
#print axioms coreFlatten680_102
#print axioms coreCheck680_102
end Erdos883Verified
