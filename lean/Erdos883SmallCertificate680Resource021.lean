import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_21 :
    (List.ofFn coreChunks680_21).flatten =
      (coreData680.take (coreResources680 21).q).drop 136 := by
  decide +kernel

theorem coreCheck680_21 :
    ∀ c : Fin 1, (coreChunks680_21 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 21)) = true := by
  decide +kernel
#print axioms coreFlatten680_21
#print axioms coreCheck680_21
end Erdos883Verified
