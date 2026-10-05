import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_52 :
    (List.ofFn coreChunks680_52).flatten =
      (coreData680.take (coreResources680 52).q).drop 107 := by
  decide +kernel

theorem coreCheck680_52 :
    ∀ c : Fin 1, (coreChunks680_52 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 52)) = true := by
  decide +kernel
#print axioms coreFlatten680_52
#print axioms coreCheck680_52
end Erdos883Verified
