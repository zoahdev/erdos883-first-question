import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_59 :
    (List.ofFn coreChunks680_59).flatten =
      (coreData680.take (coreResources680 59).q).drop 115 := by
  decide +kernel

theorem coreCheck680_59 :
    ∀ c : Fin 1, (coreChunks680_59 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 59)) = true := by
  decide +kernel
#print axioms coreFlatten680_59
#print axioms coreCheck680_59
end Erdos883Verified
