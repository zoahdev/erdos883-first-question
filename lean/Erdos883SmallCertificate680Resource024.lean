import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_24 :
    (List.ofFn coreChunks680_24).flatten =
      (coreData680.take (coreResources680 24).q).drop 141 := by
  decide +kernel

theorem coreCheck680_24 :
    ∀ c : Fin 1, (coreChunks680_24 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 24)) = true := by
  decide +kernel
#print axioms coreFlatten680_24
#print axioms coreCheck680_24
end Erdos883Verified
