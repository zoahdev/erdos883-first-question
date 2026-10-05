import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_122 :
    (List.ofFn coreChunks680_122).flatten =
      (coreData680.take (coreResources680 122).q).drop 291 := by
  decide +kernel

theorem coreCheck680_122 :
    ∀ c : Fin 1, (coreChunks680_122 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 122)) = true := by
  decide +kernel
#print axioms coreFlatten680_122
#print axioms coreCheck680_122
end Erdos883Verified
