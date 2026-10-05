import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_49 :
    (List.ofFn coreChunks680_49).flatten =
      (coreData680.take (coreResources680 49).q).drop 103 := by
  decide +kernel

theorem coreCheck680_49 :
    ∀ c : Fin 1, (coreChunks680_49 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 49)) = true := by
  decide +kernel
#print axioms coreFlatten680_49
#print axioms coreCheck680_49
end Erdos883Verified
