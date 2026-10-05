import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_2 :
    (List.ofFn coreChunks680_2).flatten =
      (coreData680.take (coreResources680 2).q).drop 62 := by
  decide +kernel

theorem coreCheck680_2 :
    ∀ c : Fin 1, (coreChunks680_2 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 2)) = true := by
  decide +kernel
#print axioms coreFlatten680_2
#print axioms coreCheck680_2
end Erdos883Verified
