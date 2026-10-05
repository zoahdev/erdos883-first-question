import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_116 :
    (List.ofFn coreChunks680_116).flatten =
      (coreData680.take (coreResources680 116).q).drop 274 := by
  decide +kernel

theorem coreCheck680_116 :
    ∀ c : Fin 1, (coreChunks680_116 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 116)) = true := by
  decide +kernel
#print axioms coreFlatten680_116
#print axioms coreCheck680_116
end Erdos883Verified
