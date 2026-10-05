import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_81 :
    (List.ofFn coreChunks680_81).flatten =
      (coreData680.take (coreResources680 81).q).drop 150 := by
  decide +kernel

theorem coreCheck680_81 :
    ∀ c : Fin 1, (coreChunks680_81 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 81)) = true := by
  decide +kernel
#print axioms coreFlatten680_81
#print axioms coreCheck680_81
end Erdos883Verified
