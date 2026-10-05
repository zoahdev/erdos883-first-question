import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_16 :
    (List.ofFn coreChunks680_16).flatten =
      (coreData680.take (coreResources680 16).q).drop 131 := by
  decide +kernel

theorem coreCheck680_16 :
    ∀ c : Fin 1, (coreChunks680_16 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 16)) = true := by
  decide +kernel
#print axioms coreFlatten680_16
#print axioms coreCheck680_16
end Erdos883Verified
