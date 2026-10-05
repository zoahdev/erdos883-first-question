import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_6 :
    (List.ofFn coreChunks680_6).flatten =
      (coreData680.take (coreResources680 6).q).drop 89 := by
  decide +kernel

theorem coreCheck680_6 :
    ∀ c : Fin 1, (coreChunks680_6 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 6)) = true := by
  decide +kernel
#print axioms coreFlatten680_6
#print axioms coreCheck680_6
end Erdos883Verified
