import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_4 :
    (List.ofFn coreChunks680_4).flatten =
      (coreData680.take (coreResources680 4).q).drop 79 := by
  decide +kernel

theorem coreCheck680_4 :
    ∀ c : Fin 1, (coreChunks680_4 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 4)) = true := by
  decide +kernel
#print axioms coreFlatten680_4
#print axioms coreCheck680_4
end Erdos883Verified
