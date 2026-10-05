import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_48 :
    (List.ofFn coreChunks680_48).flatten =
      (coreData680.take (coreResources680 48).q).drop 98 := by
  decide +kernel

theorem coreCheck680_48 :
    ∀ c : Fin 1, (coreChunks680_48 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 48)) = true := by
  decide +kernel
#print axioms coreFlatten680_48
#print axioms coreCheck680_48
end Erdos883Verified
