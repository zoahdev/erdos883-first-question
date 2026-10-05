import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_39 :
    (List.ofFn coreChunks680_39).flatten =
      (coreData680.take (coreResources680 39).q).drop 162 := by
  decide +kernel

theorem coreCheck680_39 :
    ∀ c : Fin 1, (coreChunks680_39 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 39)) = true := by
  decide +kernel
#print axioms coreFlatten680_39
#print axioms coreCheck680_39
end Erdos883Verified
