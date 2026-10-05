import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_95 :
    (List.ofFn coreChunks680_95).flatten =
      (coreData680.take (coreResources680 95).q).drop 175 := by
  decide +kernel

theorem coreCheck680_95 :
    ∀ c : Fin 1, (coreChunks680_95 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 95)) = true := by
  decide +kernel
#print axioms coreFlatten680_95
#print axioms coreCheck680_95
end Erdos883Verified
