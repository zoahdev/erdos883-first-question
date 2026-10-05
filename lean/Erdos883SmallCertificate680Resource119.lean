import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_119 :
    (List.ofFn coreChunks680_119).flatten =
      (coreData680.take (coreResources680 119).q).drop 284 := by
  decide +kernel

theorem coreCheck680_119 :
    ∀ c : Fin 1, (coreChunks680_119 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 119)) = true := by
  decide +kernel
#print axioms coreFlatten680_119
#print axioms coreCheck680_119
end Erdos883Verified
