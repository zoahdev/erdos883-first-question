import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_35 :
    (List.ofFn coreChunks680_35).flatten =
      (coreData680.take (coreResources680 35).q).drop 153 := by
  decide +kernel

theorem coreCheck680_35 :
    ∀ c : Fin 1, (coreChunks680_35 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 35)) = true := by
  decide +kernel
#print axioms coreFlatten680_35
#print axioms coreCheck680_35
end Erdos883Verified
