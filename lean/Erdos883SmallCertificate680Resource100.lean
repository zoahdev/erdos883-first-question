import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_100 :
    (List.ofFn coreChunks680_100).flatten =
      (coreData680.take (coreResources680 100).q).drop 187 := by
  decide +kernel

theorem coreCheck680_100 :
    ∀ c : Fin 1, (coreChunks680_100 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 100)) = true := by
  decide +kernel
#print axioms coreFlatten680_100
#print axioms coreCheck680_100
end Erdos883Verified
