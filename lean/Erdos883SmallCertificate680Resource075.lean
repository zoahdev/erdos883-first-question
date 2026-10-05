import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_75 :
    (List.ofFn coreChunks680_75).flatten =
      (coreData680.take (coreResources680 75).q).drop 141 := by
  decide +kernel

theorem coreCheck680_75 :
    ∀ c : Fin 1, (coreChunks680_75 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 75)) = true := by
  decide +kernel
#print axioms coreFlatten680_75
#print axioms coreCheck680_75
end Erdos883Verified
