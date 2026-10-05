import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_51 :
    (List.ofFn coreChunks680_51).flatten =
      (coreData680.take (coreResources680 51).q).drop 106 := by
  decide +kernel

theorem coreCheck680_51 :
    ∀ c : Fin 1, (coreChunks680_51 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 51)) = true := by
  decide +kernel
#print axioms coreFlatten680_51
#print axioms coreCheck680_51
end Erdos883Verified
