import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_34 :
    (List.ofFn coreChunks680_34).flatten =
      (coreData680.take (coreResources680 34).q).drop 152 := by
  decide +kernel

theorem coreCheck680_34 :
    ∀ c : Fin 1, (coreChunks680_34 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 34)) = true := by
  decide +kernel
#print axioms coreFlatten680_34
#print axioms coreCheck680_34
end Erdos883Verified
