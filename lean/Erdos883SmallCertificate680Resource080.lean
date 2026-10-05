import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_80 :
    (List.ofFn coreChunks680_80).flatten =
      (coreData680.take (coreResources680 80).q).drop 149 := by
  decide +kernel

theorem coreCheck680_80 :
    ∀ c : Fin 1, (coreChunks680_80 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 80)) = true := by
  decide +kernel
#print axioms coreFlatten680_80
#print axioms coreCheck680_80
end Erdos883Verified
