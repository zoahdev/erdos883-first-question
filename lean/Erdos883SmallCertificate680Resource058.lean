import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_58 :
    (List.ofFn coreChunks680_58).flatten =
      (coreData680.take (coreResources680 58).q).drop 114 := by
  decide +kernel

theorem coreCheck680_58 :
    ∀ c : Fin 1, (coreChunks680_58 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 58)) = true := by
  decide +kernel
#print axioms coreFlatten680_58
#print axioms coreCheck680_58
end Erdos883Verified
