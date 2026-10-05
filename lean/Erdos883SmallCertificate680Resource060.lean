import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_60 :
    (List.ofFn coreChunks680_60).flatten =
      (coreData680.take (coreResources680 60).q).drop 117 := by
  decide +kernel

theorem coreCheck680_60 :
    ∀ c : Fin 1, (coreChunks680_60 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 60)) = true := by
  decide +kernel
#print axioms coreFlatten680_60
#print axioms coreCheck680_60
end Erdos883Verified
