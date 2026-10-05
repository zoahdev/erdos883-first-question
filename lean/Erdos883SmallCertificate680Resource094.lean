import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_94 :
    (List.ofFn coreChunks680_94).flatten =
      (coreData680.take (coreResources680 94).q).drop 174 := by
  decide +kernel

theorem coreCheck680_94 :
    ∀ c : Fin 1, (coreChunks680_94 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 94)) = true := by
  decide +kernel
#print axioms coreFlatten680_94
#print axioms coreCheck680_94
end Erdos883Verified
