import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_115 :
    (List.ofFn coreChunks680_115).flatten =
      (coreData680.take (coreResources680 115).q).drop 273 := by
  decide +kernel

theorem coreCheck680_115 :
    ∀ c : Fin 1, (coreChunks680_115 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 115)) = true := by
  decide +kernel
#print axioms coreFlatten680_115
#print axioms coreCheck680_115
end Erdos883Verified
