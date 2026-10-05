import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_46 :
    (List.ofFn coreChunks680_46).flatten =
      (coreData680.take (coreResources680 46).q).drop 89 := by
  decide +kernel

theorem coreCheck680_46 :
    ∀ c : Fin 1, (coreChunks680_46 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 46)) = true := by
  decide +kernel
#print axioms coreFlatten680_46
#print axioms coreCheck680_46
end Erdos883Verified
