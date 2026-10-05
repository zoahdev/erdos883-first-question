import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_56 :
    (List.ofFn coreChunks680_56).flatten =
      (coreData680.take (coreResources680 56).q).drop 112 := by
  decide +kernel

theorem coreCheck680_56 :
    ∀ c : Fin 1, (coreChunks680_56 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 56)) = true := by
  decide +kernel
#print axioms coreFlatten680_56
#print axioms coreCheck680_56
end Erdos883Verified
