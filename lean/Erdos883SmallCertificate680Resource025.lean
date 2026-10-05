import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_25 :
    (List.ofFn coreChunks680_25).flatten =
      (coreData680.take (coreResources680 25).q).drop 143 := by
  decide +kernel

theorem coreCheck680_25 :
    ∀ c : Fin 1, (coreChunks680_25 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 25)) = true := by
  decide +kernel
#print axioms coreFlatten680_25
#print axioms coreCheck680_25
end Erdos883Verified
