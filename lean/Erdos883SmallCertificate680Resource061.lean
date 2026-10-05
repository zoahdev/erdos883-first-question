import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_61 :
    (List.ofFn coreChunks680_61).flatten =
      (coreData680.take (coreResources680 61).q).drop 119 := by
  decide +kernel

theorem coreCheck680_61 :
    ∀ c : Fin 1, (coreChunks680_61 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 61)) = true := by
  decide +kernel
#print axioms coreFlatten680_61
#print axioms coreCheck680_61
end Erdos883Verified
