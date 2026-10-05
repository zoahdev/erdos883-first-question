import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_31 :
    (List.ofFn coreChunks680_31).flatten =
      (coreData680.take (coreResources680 31).q).drop 149 := by
  decide +kernel

theorem coreCheck680_31 :
    ∀ c : Fin 1, (coreChunks680_31 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 31)) = true := by
  decide +kernel
#print axioms coreFlatten680_31
#print axioms coreCheck680_31
end Erdos883Verified
