import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_10 :
    (List.ofFn coreChunks680_10).flatten =
      (coreData680.take (coreResources680 10).q).drop 124 := by
  decide +kernel

theorem coreCheck680_10 :
    ∀ c : Fin 1, (coreChunks680_10 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 10)) = true := by
  decide +kernel
#print axioms coreFlatten680_10
#print axioms coreCheck680_10
end Erdos883Verified
