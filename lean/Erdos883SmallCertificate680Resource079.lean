import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_79 :
    (List.ofFn coreChunks680_79).flatten =
      (coreData680.take (coreResources680 79).q).drop 148 := by
  decide +kernel

theorem coreCheck680_79 :
    ∀ c : Fin 1, (coreChunks680_79 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 79)) = true := by
  decide +kernel
#print axioms coreFlatten680_79
#print axioms coreCheck680_79
end Erdos883Verified
