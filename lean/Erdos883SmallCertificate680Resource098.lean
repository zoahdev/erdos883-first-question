import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_98 :
    (List.ofFn coreChunks680_98).flatten =
      (coreData680.take (coreResources680 98).q).drop 178 := by
  decide +kernel

theorem coreCheck680_98 :
    ∀ c : Fin 1, (coreChunks680_98 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 98)) = true := by
  decide +kernel
#print axioms coreFlatten680_98
#print axioms coreCheck680_98
end Erdos883Verified
