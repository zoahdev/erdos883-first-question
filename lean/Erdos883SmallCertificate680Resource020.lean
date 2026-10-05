import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_20 :
    (List.ofFn coreChunks680_20).flatten =
      (coreData680.take (coreResources680 20).q).drop 135 := by
  decide +kernel

theorem coreCheck680_20 :
    ∀ c : Fin 1, (coreChunks680_20 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 20)) = true := by
  decide +kernel
#print axioms coreFlatten680_20
#print axioms coreCheck680_20
end Erdos883Verified
