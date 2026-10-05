import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_30 :
    (List.ofFn coreChunks680_30).flatten =
      (coreData680.take (coreResources680 30).q).drop 148 := by
  decide +kernel

theorem coreCheck680_30 :
    ∀ c : Fin 1, (coreChunks680_30 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 30)) = true := by
  decide +kernel
#print axioms coreFlatten680_30
#print axioms coreCheck680_30
end Erdos883Verified
