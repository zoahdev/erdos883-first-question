import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_43 :
    (List.ofFn coreChunks680_43).flatten =
      (coreData680.take (coreResources680 43).q).drop 169 := by
  decide +kernel

theorem coreCheck680_43 :
    ∀ c : Fin 1, (coreChunks680_43 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 43)) = true := by
  decide +kernel
#print axioms coreFlatten680_43
#print axioms coreCheck680_43
end Erdos883Verified
